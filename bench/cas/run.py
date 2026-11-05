#!/usr/bin/env python3
"""Optional CAS smoke runner; Python 3.11+, standard library only."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction
import json
import math
import os
import platform
from pathlib import Path
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
import tomllib
from workloads import dense

BENCH = Path(__file__).resolve().parents[1]
RESULT_MARKER = "CSBENCH_RESULT:"
VERSION_MARKER = "CSBENCH_VERSION:"
DEFAULTS = {
    "maple": ("maple", ["-q"], "MAPLE_BIN"),
    "mathematica": ("wolframscript", ["-file"], "MATHEMATICA_BIN"),
    "sympy": ("python3", [], "SYMPY_PYTHON"),
}


def canonical(terms: list) -> list:
    """Compare exact polynomials, independently of term order and formatting."""
    if not isinstance(terms, list):
        raise ValueError("terms must be an array")
    coefficients: dict[tuple[int, int], Fraction] = {}
    for term in terms:
        powers = term["powers"]
        if (not isinstance(powers, list) or len(powers) != 2
                or any(type(p) is not int or p < 0 for p in powers)):
            raise ValueError("expected two nonnegative integer exponents")
        for key in ("num", "den"):
            if not isinstance(term[key], str) or not re.fullmatch(r"-?[0-9]+", term[key]):
                raise ValueError(f"{key} must be a decimal integer string")
        if int(term["den"]) <= 0:
            raise ValueError("denominator must be positive")
        key = tuple(powers)
        coefficients[key] = coefficients.get(key, Fraction()) + Fraction(
            int(term["num"]), int(term["den"]))
    return [{"powers": list(powers), "num": str(c.numerator), "den": str(c.denominator)}
            for powers, c in sorted(coefficients.items()) if c]


def expression(terms: list) -> str:
    return " + ".join(
        f"({t['num']}/{t['den']})*x^{t['powers'][0]}*y^{t['powers'][1]}"
        for t in canonical(terms)) or "0"


def backend_command(backend: str, config_path: Path) -> list[str]:
    config = {}
    if config_path.exists():
        with config_path.open("rb") as stream:
            config = tomllib.load(stream)
    executable, args, env_key = DEFAULTS[backend]
    section = config.get(backend, {})
    if not isinstance(section, dict):
        raise ValueError(f"[{backend}] must be a table")
    executable = os.environ.get(env_key, section.get("executable", executable))
    args = section.get("args", args)
    if not isinstance(executable, str) or not executable:
        raise ValueError(f"[{backend}].executable must be a nonempty string")
    if not isinstance(args, list) or any(not isinstance(a, str) for a in args):
        raise ValueError(f"[{backend}].args must be an array of strings")
    if "/" in executable or "\\" in executable:
        path = Path(executable).expanduser()
        executable = str(path if path.is_absolute() else config_path.parent / path)
    resolved = shutil.which(executable)
    if resolved is None:
        raise ValueError(f"cannot find {executable!r}; set [{backend}].executable in "
                         f"{config_path} or {env_key}")
    return [resolved, *args]


def parse_output(output: str) -> tuple[str, list]:
    # Maple may prepend a prompt to printf output. Ignore banners, never eval text.
    records = [match.groups() for line in output.splitlines()
               if (match := re.fullmatch(r"\s*(?:>\s*)?(CSBENCH_RESULT:|CSBENCH_VERSION:)(.*)", line))]
    results = [value for marker, value in records if marker == RESULT_MARKER]
    versions = [value.strip() for marker, value in records if marker == VERSION_MARKER]
    if len(results) != 1 or len(versions) != 1 or not versions[0]:
        raise ValueError("backend must emit exactly one result and software version")
    return versions[0], canonical(json.loads(results[0])["terms"])


def timing_samples(output, fixture):
    records = [m.group(1) for line in output.splitlines()
               if (m := re.fullmatch(r"\s*(?:>\s*)?CSBENCH_RESULT:(.*)", line))]
    payload = json.loads(records[0])
    samples = payload.get("samples")
    if not isinstance(samples, list) or len(samples) != fixture["trials"]:
        raise ValueError("backend did not return the requested timed trials")
    timings = []
    batch = fixture["batch_size"]
    for trial, sample in enumerate(samples):
        elapsed = sample["seconds"]
        if type(elapsed) not in (int, float) or not math.isfinite(elapsed) or elapsed < 0:
            raise ValueError("invalid computation time")
        if len(sample["outputs"]) != batch:
            raise ValueError("backend returned wrong batch size")
        for i, actual in enumerate(sample["outputs"]):
            offset = trial*batch + i + 1
            correction = [dict(t, num=str(int(t["num"])*offset)) for t in fixture["lhs"]]
            expected = canonical(fixture["expected"] + correction)
            if canonical(actual) != expected:
                raise ValueError(f"timed result mismatch in trial {trial+1}, item {i+1}")
        timings.append(elapsed / batch)
    return {"samples_seconds_per_call": timings,
            "median_seconds_per_call": statistics.median(timings),
            "min_seconds_per_call": min(timings), "max_seconds_per_call": max(timings),
            "below_resolution": any(s["seconds"] < 0.01 for s in samples)}


def execute(command: list[str], stdin: str | None, timeout: float) -> tuple[int, str, str]:
    # A process group lets a timeout stop wrapper scripts and their children too.
    import signal
    with subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True, start_new_session=True) as child:
        try:
            stdout, stderr = child.communicate(stdin, timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL)
            stdout, stderr = child.communicate()
            return 124, stdout, stderr + "\nbackend timed out\n"
        return child.returncode, stdout, stderr


def compare_all(options):
    root = options.output_dir.resolve() if options.output_dir else Path(tempfile.mkdtemp(
        prefix="comparison-", dir=BENCH / ".lake/cas-results"))
    root.mkdir(parents=True, exist_ok=True)
    summary = {"case": options.case, "backends": {}}
    failed = False
    for backend in ("lean", *DEFAULTS):
        args = ["run", "--backend", backend, "--case", options.case,
                "--batch-size", str(options.batch_size), "--trials", str(options.trials),
                "--timeout", str(options.timeout), "--output-dir", str(root / backend)]
        if options.config:
            args.extend(["--config", str(options.config)])
        failed |= main(args) != 0
        report = json.loads((root / backend / "result.json").read_text())
        summary["backends"][backend] = {key: report.get(key) for key in (
            "status", "version", "computation", "process_seconds", "error")}
    (root / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Comparison: {root / 'summary.json'}", flush=True)
    return int(failed)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["run"])
    parser.add_argument("--backend", required=True, choices=["lean", *DEFAULTS, "all"])
    parser.add_argument("--case", default="smoke", help="smoke, dense-8/16/32, or JSON path")
    parser.add_argument("--batch-size", type=int, default=16)
    parser.add_argument("--trials", type=int, default=3)
    parser.add_argument("--config", type=Path)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--timeout", type=float, default=30.0)
    options = parser.parse_args(argv)
    if options.batch_size < 1 or options.trials < 1:
        parser.error("--batch-size and --trials must be positive")
    if not 0 < options.timeout < float("inf"):
        parser.error("--timeout must be finite and positive")
    if options.backend == "all":
        (BENCH / ".lake/cas-results").mkdir(parents=True, exist_ok=True)
        return compare_all(options)
    if options.output_dir:
        directory = options.output_dir.resolve()
        directory.mkdir(parents=True, exist_ok=True)
    else:
        root = BENCH / ".lake/cas-results"
        root.mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix=options.backend + "-", dir=root))
    report = {"schema_version": 1, "backend": options.backend, "case": None,
              "version": None, "status": "error", "result": None,
              "operation": "multiply", "coefficient_domain": "QQ",
              "runner_platform": platform.platform(),
              "timestamp": datetime.now(timezone.utc).isoformat()}
    stdout = stderr = ""
    try:
        if options.case in ("dense-8", "dense-16", "dense-32"):
            fixture = dense(int(options.case.split("-")[1]))
        else:
            path = BENCH / "cas/cases/multiply.json" if options.case == "smoke" else Path(options.case)
            fixture = json.loads(path.read_text())
        if fixture["variables"] != ["x", "y"] or not isinstance(fixture["id"], str):
            raise ValueError("case requires an id and variables [x, y]")
        report["case"] = fixture["id"]
        expected = canonical(fixture["expected"])
        # Persist the exact validated inputs so every artifact is reproducible.
        for key in ("lhs", "rhs"):
            fixture[key] = canonical(fixture[key])
        fixture["expected"] = expected
        fixture.update(batch_size=options.batch_size, trials=options.trials)
        report.update(batch_size=options.batch_size, trials=options.trials,
                      input_terms=[len(fixture[k]) for k in ("lhs", "rhs")],
                      output_terms=len(expected))
        input_path = directory / "input.json"
        input_path.write_text(json.dumps(fixture, indent=2) + "\n")
        stdin = None
        if options.backend == "lean":
            env = dict(os.environ)
            env.setdefault("LEAN_NUM_THREADS", "2")
            build = subprocess.run(["lake", "build", "characteristic_bench"], cwd=BENCH,
                                   env=env, capture_output=True, text=True)
            (directory / "build.log").write_text(build.stdout + build.stderr)
            if build.returncode:
                raise ValueError(f"Lean build failed; see {directory / 'build.log'}")
            command = [str(BENCH / ".lake/build/bin/characteristic_bench"),
                       "cas-smoke", str(input_path)]
        else:
            config = options.config.resolve() if options.config else BENCH / "config.local.toml"
            if options.config and not config.is_file():
                raise ValueError(f"configuration file does not exist: {config}")
            command = backend_command(options.backend, config)
            if options.backend == "sympy":
                command.extend([str(BENCH / "cas/sympy_backend.py"), str(input_path)])
            else:
                suffix = "mpl" if options.backend == "maple" else "wls"
                source = (BENCH / f"cas/{options.backend}.{suffix}").read_text()
                for key, value in {"LHS": expression(fixture["lhs"]),
                                   "RHS": expression(fixture["rhs"]),
                                   "BATCH": str(options.batch_size),
                                   "TRIALS": str(options.trials)}.items():
                    source = source.replace(f"@{key}@", value)
                script = directory / f"job.{suffix}"
                script.write_text(source)
                if options.backend == "maple":
                    stdin = source
                else:
                    command.append(str(script))
        report["command"] = command
        start = time.monotonic()
        code, stdout, stderr = execute(command, stdin, options.timeout)
        report["process_seconds"] = time.monotonic() - start
        report["exit_code"] = code
        if code:
            raise ValueError("backend timed out" if code == 124 else f"backend exited with {code}")
        version, result = parse_output(stdout)
        report.update(version=version, result=result)
        if result != expected:
            report["status"] = "mismatch"
            report["expected"] = expected
            raise ValueError("computed polynomial does not match expected result")
        report["computation"] = timing_samples(stdout, fixture)
        report["status"] = "ok"
    except (OSError, ValueError, KeyError, TypeError, ZeroDivisionError) as error:
        report["error"] = str(error)
    (directory / "stdout.log").write_text(stdout)
    (directory / "stderr.log").write_text(stderr)
    (directory / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{options.backend}: {report['status']}; {directory / 'result.json'}", flush=True)
    if report["status"] == "ok":
        timing = report["computation"]
        print(f"  multiplication median: {timing['median_seconds_per_call']*1e3:.4f} ms/call"
              + (" (batch below 10 ms; increase --batch-size)" if timing['below_resolution'] else ""), flush=True)
    if report["status"] != "ok":
        print(report["error"], file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
