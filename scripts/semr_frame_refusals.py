#!/usr/bin/env python3
# Copyright 2026 Andrew Yates | Apache-2.0
"""Exercise the real frame audit against must-refuse inputs under pinned Lean.

Run standalone through build-slot; the Rust test inherits its caller's slot.
Generated probes stay outside source. They are counterfeit negative inputs,
never proof authority. This checks the audit, not independent Clean replay.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


def qualify(lake: Path, work: Path) -> None:
    repo = Path(__file__).resolve().parents[1]
    package = repo / "lean/semr-memory"
    fixture = json.loads((package / "frame-audit-refusals.json").read_text())
    if fixture["schema"] != 1 or len(fixture["cases"]) != 10:
        raise RuntimeError("exact ten-case refusal fixture required")
    source = (package / "FrameAudit.lean").read_text()
    environment = os.environ.copy()
    environment.pop("SDKROOT", None)
    environment["PATH"] = str(lake.parent) + os.pathsep + environment.get("PATH", "")
    base = [str(lake), "-R"]
    if linker := environment.get("TRUST_IR_NATIVE_LINKER"):
        base.append("-KnativeLinker=" + linker)
    base += ["-d", str(package)]
    commands = []

    def run(argv: list[str], label: str, env: dict[str, str] = environment):
        result = subprocess.run(argv, cwd=package, env=env, capture_output=True, text=True)
        log = result.stdout + result.stderr
        (work / (label + ".log")).write_text(log)
        commands.append({"argv": argv, "log": label + ".log", "exit_code": result.returncode})
        (work / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        return result.returncode, log

    def succeeds(argv: list[str], label: str):
        code, log = run(argv, label)
        if code:
            raise RuntimeError(f"{label} failed ({code}); see {work / (label + '.log')}")
        return log

    version = succeeds(base + ["env", "lean", "--version"], "compiler-version").strip()
    if not version.startswith("Lean (version 4.30.0-rc2,"):
        raise RuntimeError(f"exact pinned Lean4.30.0-rc2 required, got {version}")
    succeeds(base + ["build", "SemRFrameChecks"], "build")
    positive = succeeds(base + ["env", "lean", str(package / "FrameAudit.lean")], "positive-audit")
    components = re.findall(r"semr-frame component: module=(\w+) declarations=(\d+) theorems=(\d+) replayed=(\d+) native-evaluations=(\d+)", positive)
    if [row[0] for row in components] != fixture["components"]:
        raise RuntimeError("positive audit did not cover the exact eight components")
    if any(int(d) == 0 or int(t) == 0 or d != r or int(n) != 0 for _, d, t, r, n in components):
        raise RuntimeError("incomplete component replay accounting")
    summary = re.findall(r"semr-frame audit: declarations=(\d+) theorems=(\d+) replayed=(\d+) native-evaluations=(\d+)", positive)
    expected = (str(sum(int(row[1]) for row in components)),
                str(sum(int(row[2]) for row in components)),
                str(sum(int(row[3]) for row in components)), "0")
    if summary != [expected]:
        raise RuntimeError("incomplete aggregate replay accounting")

    # Capture only compiler/search-path variables, never the complete environment.
    keys = ["LEAN_PATH", "PATH", "LEAN_SYSROOT", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"]
    expression = "import json,os; print(json.dumps({k:os.environ.get(k) for k in " + repr(keys) + "}))"
    selected = json.loads(succeeds(base + ["env", sys.executable, "-c", expression], "compiler-environment"))
    lean_env = environment.copy()
    for key, value in selected.items():
        if value is None:
            lean_env.pop(key, None)
        else:
            lean_env[key] = value
    lean_env["LEAN_PATH"] = str(work) + os.pathsep + lean_env.get("LEAN_PATH", "")
    lean = shutil.which("lean", path=lean_env["PATH"])
    if lean is None:
        raise RuntimeError("Lake did not select a Lean executable")
    results = []

    for index, case in enumerate(fixture["cases"]):
        mutant = source
        for change in case["replacements"]:
            if mutant.count(change["needle"]) != change["count"]:
                raise RuntimeError(f"{case['name']}: refusal template no longer matches")
            mutant = mutant.replace(change["needle"], change["replacement"])
        if probe := case.get("probe"):
            for definition in probe.get("dependencies", []) + [probe]:
                module = definition["module"]
                if not re.fullmatch(r"FrameAudit[A-Za-z]+", module):
                    raise RuntimeError("invalid counterfeit probe module name")
                file = work / (module + ".lean")
                file.write_text(definition["source"])
                argv = [lean, "--root=" + str(work), "-o", str(file.with_suffix(".olean")), str(file)]
                code, _ = run(argv, "compile-" + module, lean_env)
                if code:
                    raise RuntimeError(f"counterfeit probe did not compile: {module}")
            mutant = "import " + probe["module"] + "\n" + mutant
        file = work / f"FrameAuditRefusal{index}.lean"
        file.write_text(mutant)
        code, log = run([lean, "--root=" + str(work), str(file)], case["name"], lean_env)
        if code != 1 or case["diagnostic"] not in log:
            raise RuntimeError(f"{case['name']}: expected audit refusal was not observed; see {work / (case['name'] + '.log')}")
        results.append({"case": case["name"], "exit_code": code, "diagnostic": case["diagnostic"],
                        "mutant_sha256": hashlib.sha256(file.read_bytes()).hexdigest()})
    (work / "result.json").write_text(json.dumps({"schema": 1, "compiler": version,
        "positive_summary": list(expected), "cases": results,
        "independent_Clean_replay": False, "native_authority": False}, indent=2) + "\n")
    print(f"semr-frame refusals: PASS cases={len(results)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", required=True, type=Path)
    parser.add_argument("--work-dir", type=Path, help="new owned directory outside the repository; retain inputs/logs")
    args = parser.parse_args()
    lake = args.lake.absolute()  # Preserve elan shim names; do not dereference symlinks.
    if args.work_dir is None:
        with tempfile.TemporaryDirectory(prefix="trust-ir-frame-audit-") as directory:
            qualify(lake, Path(directory))
    else:
        work = args.work_dir.resolve()
        repo = Path(__file__).resolve().parents[1]
        if work == repo or repo in work.parents:
            parser.error("generated refusal inputs must remain outside the source tree")
        work.mkdir(parents=True, exist_ok=False)
        qualify(lake, work)


if __name__ == "__main__":
    main()
