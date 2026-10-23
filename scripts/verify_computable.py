#!/usr/bin/env python3
"""Build the current computable package outside the repository and test its boundary.

Requires Python 3 and the pinned Lean toolchain. All artifacts are retained in a
fresh temporary directory. --dependency-cache accepts a Lake packages directory;
only clean Git sources at manifest revisions are copied, never build artifacts.
"""

import argparse
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dependency-cache", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    work = Path(tempfile.mkdtemp(prefix="characteristic-computable-"))
    assert not work.is_relative_to(repo)
    package = work / "computable"
    logs = work / "logs"
    logs.mkdir()
    print(f"Artifacts and logs: {work}", flush=True)
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(key, None)

    def run(label, command, cwd, expected=0):
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (logs / f"{label}.log").write_text(
            f"cwd: {cwd}\n$ {shlex.join(command)}\n{result.stdout}"
            f"\nexit: {result.returncode}\n")
        if expected is None:
            assert result.returncode != 0, f"{label}: unexpectedly succeeded"
        else:
            assert result.returncode == expected, f"{label}: see {logs / (label + '.log')}"
        print(f"{label}: exit {result.returncode}", flush=True)
        return result.stdout

    # Copy the working tree, including uncommitted changes, without old artifacts.
    package.mkdir()
    for filename in ("lakefile.toml", "lake-manifest.json", "lean-toolchain",
                     "CharacteristicSet.lean"):
        shutil.copyfile(repo / filename, package / filename)
    shutil.copytree(repo / "CharacteristicSet", package / "CharacteristicSet")
    manifest = json.loads((package / "lake-manifest.json").read_text())
    allowed = {"HexMvPoly", "HexBasic", "HexPoly", "HexModArith", "HexArith"}
    assert {p["name"] for p in manifest["packages"]} == allowed
    assert all(p["type"] == "git" for p in manifest["packages"])
    (logs / "package-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

    if args.dependency_cache:
        cache = args.dependency_cache.resolve()
        for entry in manifest["packages"]:
            name = entry["name"]
            source = cache / name
            assert not run(f"cache-clean-{name}",
                           ["git", "status", "--porcelain"], source).strip()
            dest = package / ".lake/packages" / name
            run(f"cache-clone-{name}", ["git", "-c", "advice.detachedHead=false",
                "clone", "--quiet", "--no-hardlinks", str(source), str(dest)], work)
            run(f"cache-checkout-{name}", ["git", "-c", "advice.detachedHead=false",
                "checkout", "--quiet", "--detach", entry["rev"]], dest)
            run(f"cache-origin-{name}",
                ["git", "remote", "set-url", "origin", entry["url"]], dest)

    assert not list(package.rglob("*.olean")), "pre-existing Lean artifacts"
    run("package-build", ["lake", "build"], package)
    run("package-examples", ["lake", "env", "lean",
                            "CharacteristicSet/Computable/Examples.lean"], package)
    assert len(re.findall(r"^#guard\b", (package /
        "CharacteristicSet/Computable/Examples.lean").read_text(), re.M)) == 19
    for entry in manifest["packages"]:
        source = package / ".lake/packages" / entry["name"]
        assert run(f"revision-{entry['name']}",
                   ["git", "rev-parse", "HEAD"], source).strip() == entry["rev"]
        assert not run(f"clean-{entry['name']}",
                       ["git", "status", "--porcelain"], source).strip()

    # Audit the project/Hex source closure. Init, Std and Lean belong to Lean's
    # toolchain; every other import must resolve inside these copied sources.
    roots = [package] + [package / ".lake/packages" / p["name"]
                         for p in manifest["packages"]]
    import_line = re.compile(r"^\s*(?:(?:public|private)\s+)?import\s+(?:all\s+)?(.+)$", re.M)

    def closure(start):
        seen = set()
        pending = [start]
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            if name.split(".")[0] in {"Init", "Std", "Lean"}:
                continue
            assert name == "CharacteristicSet" or name.startswith("CharacteristicSet.Computable") or name.split(".")[0] in allowed, name
            candidates = [r / (name.replace(".", "/") + ".lean") for r in roots]
            sources = [p for p in candidates if p.is_file()]
            assert len(sources) == 1, (name, sources)
            for line in import_line.findall(sources[0].read_text()):
                pending.extend(line.split("--", 1)[0].split())
        return sorted(seen)

    (logs / "source-import-closure.json").write_text(json.dumps({
        name: closure(name) for name in
        ("CharacteristicSet", "CharacteristicSet.Computable.Examples")
    }, indent=2) + "\n")

    consumer = work / "consumer"
    consumer.mkdir()
    shutil.copyfile(package / "lean-toolchain", consumer / "lean-toolchain")
    (consumer / "lakefile.toml").write_text('''name = "ComputableConsumer"
defaultTargets = ["Main"]
[[require]]
name = "CharacteristicSet"
path = "../computable"
[[lean_lib]]
name = "Main"
''')
    (consumer / "Main.lean").write_text('''import CharacteristicSet
import HexMvPoly.Ring

open Hex Hex.MvPoly CharacteristicSet.Computable
abbrev P := MvPoly 2 Rat Mono.lex
def x : P := X 0
def y : P := X 1
#guard mainVar (x * y * y + C 1) == some 1
#guard mainDegree (x * y * y + C 1) == 2
#guard initial (x * y * y + C 1) == x
#guard compareRank x y == .lt
#eval (mainVar (x * y * y + C 1), mainDegree (x * y * y + C 1),
  (initial (x * y * y + C 1)).termsList.map fun (m, c) => (m.toList, c))
''')
    # Reuse only the fresh isolated dependency clones, still without copying any
    # build directories. Lake resolves the path package's pinned manifest.
    (consumer / ".lake/packages").parent.mkdir()
    (consumer / ".lake/packages").symlink_to(package / ".lake/packages", target_is_directory=True)
    run("consumer-update", ["lake", "update"], consumer)
    consumer_manifest = json.loads((consumer / "lake-manifest.json").read_text())
    assert {p["name"] for p in consumer_manifest["packages"]} == allowed | {"CharacteristicSet"}
    run("consumer-build", ["lake", "build"], consumer)
    run("consumer-run", ["lake", "env", "lean", "Main.lean"], consumer)
    paths = json.loads(run("consumer-paths", ["lake", "env", "python3", "-c",
        'import json,os; print(json.dumps({k:os.environ.get(k, "") for k in '
        '["LEAN_PATH", "LEAN_SRC_PATH"]}))'], consumer))
    toolchain = Path(run("toolchain", ["lean", "--print-prefix"], consumer).strip()).resolve()
    for value in paths.values():
        for raw in value.split(os.pathsep):
            if raw:
                path = (consumer / raw).resolve()
                assert path.is_relative_to(work) or path.is_relative_to(toolchain), path

    for module in ("Mathlib", "HexMvPolyTheory", "CharacteristicSetTheory",
                   "CharacteristicSetBridge"):
        path = consumer / "Unavailable.lean"
        path.write_text(f"import {module}\n")
        output = run(f"reject-{module}", ["lake", "env", "lean", path.name],
                     consumer, expected=None)
        assert ("unknown module prefix" in output or
                ("object file" in output and "does not exist" in output)), output
        assert module.split(".")[-1] in output, output
    print(f"PASS: isolated package, 19 guards, consumer, import closure and negative imports.\n{work}", flush=True)


if __name__ == "__main__":
    main()
