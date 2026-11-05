"""Exercise the real runner with fake executables; no commercial CAS required."""
import contextlib
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import run as runner


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="cas test ")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.fake = self.root / "fake CAS.py"
        self.fake.write_text('''import json, pathlib, sys, time
mode = sys.argv[1]
source = pathlib.Path(sys.argv[-1]).read_text() if mode == "file" else sys.stdin.read()
assert "(1/2)" in source and "@LHS@" not in source
if mode == "fail":
    print("license unavailable", file=sys.stderr)
    sys.exit(7)
if mode == "timeout":
    time.sleep(10)
if mode == "bad":
    print("no protocol record")
    sys.exit(0)
terms = [
 {"powers":[1,1],"num":"1","den":"1"},
 {"powers":[0,1],"num":"1","den":"2"},
 {"powers":[1,0],"num":"-4","den":"6"},
 {"powers":[0,0],"num":"-1","den":"3"}]
if mode == "wrong": terms = []
print("startup banner")
print("CSBENCH_VERSION:fake 1.0")
samples = []
from fractions import Fraction
for trial in range(3):
    outputs = []
    for i in range(16):
        k = trial*16+i+1
        coefficients = {(1,1):Fraction(1), (0,1):Fraction(1,2),
                        (1,0):Fraction(-2,3)+k, (0,0):Fraction(-1,3)+Fraction(k,2)}
        outputs.append([{"powers":list(m),"num":str(c.numerator),"den":str(c.denominator)}
                        for m,c in coefficients.items()])
    samples.append({"seconds":0.16,"outputs":outputs})
print("CSBENCH_RESULT:" + json.dumps({"terms":terms,"samples":samples}))
''')

    def invoke(self, backend="maple", mode="stdin", extra=()):
        config = self.root / "config.local.toml"
        config.write_text(f"[{backend}]\nexecutable = {json.dumps(sys.executable)}\n"
                          f"args = {json.dumps([str(self.fake), mode])}\n")
        output = self.root / "result directory"
        with patch.dict(os.environ, {}, clear=False):
            os.environ.pop("MAPLE_BIN", None)
            os.environ.pop("MATHEMATICA_BIN", None)
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                code = runner.main(["run", "--backend", backend, "--config", str(config),
                                    "--output-dir", str(output), *extra])
        return code, json.loads((output / "result.json").read_text()), output

    def test_maple_stdin_and_exact_unordered_rationals(self):
        code, report, output = self.invoke()
        self.assertEqual(code, 0)
        self.assertEqual(report["status"], "ok")
        self.assertEqual(report["version"], "fake 1.0")
        self.assertIn("startup banner", (output / "stdout.log").read_text())
        self.assertTrue((output / "job.mpl").exists())

    def test_mathematica_script_argument(self):
        code, report, _ = self.invoke("mathematica", "file")
        self.assertEqual(code, 0)
        self.assertTrue(report["command"][-1].endswith("job.wls"))

    def test_nonzero_exit_preserves_stderr(self):
        code, report, output = self.invoke(mode="fail")
        self.assertEqual(code, 1)
        self.assertEqual(report["exit_code"], 7)
        self.assertIn("license unavailable", (output / "stderr.log").read_text())

    def test_timeout_preserves_failure(self):
        code, report, _ = self.invoke(mode="timeout", extra=["--timeout", "0.1"])
        self.assertEqual(code, 1)
        self.assertEqual(report["exit_code"], 124)

    def test_missing_protocol_and_wrong_result(self):
        for mode, status in [("bad", "error"), ("wrong", "mismatch")]:
            with self.subTest(mode=mode):
                code, report, _ = self.invoke(mode=mode)
                self.assertEqual(code, 1)
                self.assertEqual(report["status"], status)

    def test_path_config_environment_precedence_and_relative_paths(self):
        config = self.root / "config.local.toml"
        config.write_text('[maple]\nexecutable = "missing"\nargs = ["a b"]\n')
        fake_name = self.root / "maple"
        fake_name.symlink_to(sys.executable)
        with patch.dict(os.environ, {"PATH": str(self.root)}, clear=True):
            self.assertEqual(runner.backend_command("maple", self.root / "absent.toml")[0],
                             str(fake_name))
            with self.assertRaises(ValueError):
                runner.backend_command("maple", config)
            with patch.dict(os.environ, {"MAPLE_BIN": sys.executable}):
                command = runner.backend_command("maple", config)
                self.assertEqual(command, [sys.executable, "a b"])
            config.write_text('[maple]\nexecutable = "./maple"\n')
            self.assertEqual(Path(runner.backend_command("maple", config)[0]).resolve(),
                             Path(sys.executable).resolve())

    def test_config_errors(self):
        for content in ['[maple', '[maple]\nargs = "-q"', '[maple]\nexecutable = ""']:
            config = self.root / "bad.toml"
            config.write_text(content)
            with self.subTest(content=content), self.assertRaises(ValueError):
                runner.backend_command("maple", config)
        code, report, _ = self.invoke(extra=["--config", str(self.root / "absent.toml")])
        self.assertEqual(code, 1)
        self.assertIn("configuration file does not exist", report["error"])

    def test_prompt_and_echoed_source_are_not_protocol_records(self):
        version, result = runner.parse_output(
            'printf("CSBENCH_RESULT:...")\n> CSBENCH_VERSION:fake 1\n'
            '> CSBENCH_RESULT:{"terms":[]}\n')
        self.assertEqual((version, result), ("fake 1", []))

    def test_timed_results_and_metadata_are_checked(self):
        fixture = json.loads((runner.BENCH / "cas/cases/multiply.json").read_text())
        fixture.update(batch_size=1, trials=1)
        shifted = runner.canonical(fixture["expected"] + fixture["lhs"])
        payload = {"samples": [{"seconds": 0.2, "outputs": [shifted]}]}
        def parse():
            return runner.timing_samples("CSBENCH_RESULT:" + json.dumps(payload), fixture)
        self.assertEqual(parse()["median_seconds_per_call"], 0.2)
        payload["samples"][0]["outputs"] = [fixture["expected"]]
        with self.assertRaisesRegex(ValueError, "timed result mismatch"):
            parse()
        payload["samples"][0]["seconds"] = -1
        with self.assertRaisesRegex(ValueError, "invalid computation time"):
            parse()

    def test_dense_fixture_expected_product(self):
        from workloads import dense
        fixture = dense(2)
        def evaluate(ts, x, y):
            from fractions import Fraction
            return sum(Fraction(t["num"])/int(t["den"]) * x**t["powers"][0]
                       * y**t["powers"][1] for t in ts)
        for x,y in ((0,0),(1,1),(-2,3)):
            self.assertEqual(evaluate(fixture["expected"],x,y),
                             evaluate(fixture["lhs"],x,y)*evaluate(fixture["rhs"],x,y))

    def test_invalid_case_rejected(self):
        fixture = self.root / "invalid.json"
        fixture.write_text('{"id":"bad","variables":["x","y"],"expected":[], '
                           '"lhs":[{"powers":[0,0],"num":"1","den":"0"}],"rhs":[]}')
        code, report, _ = self.invoke(extra=["--case", str(fixture)])
        self.assertEqual(code, 1)
        self.assertIn("denominator", report["error"])

    def test_shell_entry_from_other_directory_does_not_build_lean_for_cas(self):
        # No real CAS or Lake invocation: this checks shell dispatch and cwd handling.
        config = self.root / "custom.toml"
        config.write_text('[maple]\nexecutable = "definitely-missing-cas"\n')
        import subprocess
        env = dict(os.environ)
        env.pop("MAPLE_BIN", None)
        output = self.root / "shell output"
        result = subprocess.run([str(runner.BENCH / "run.sh"), "run", "--backend=maple",
                                 "--config", str(config), "--output-dir", str(output)],
                                cwd=self.root, env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("cannot find", result.stderr)
        self.assertFalse((output / "build.log").exists())


if __name__ == "__main__":
    unittest.main()
