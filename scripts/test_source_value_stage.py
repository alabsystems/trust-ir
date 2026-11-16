#!/usr/bin/env python3
"""Run source-value interoperability in the existing, frozen Trust stage context."""

from __future__ import annotations

import argparse
from contextlib import ExitStack
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tomllib


HARNESS = Path("crates/trust-ir-build/tests/stage_source_value_equation")
SUBJECTS = ("source_value_equation", "source_value_equation_producer")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stable(stamp: os.stat_result) -> tuple[int, ...]:
    # Reading a source can update atime without changing its contents.
    return tuple(getattr(stamp, name) for name in (
        "st_dev", "st_ino", "st_mode", "st_nlink", "st_size", "st_mtime_ns", "st_ctime_ns"
    ))


def inline(table: dict) -> str:
    return "{ " + ", ".join(f"{json.dumps(k)} = {json.dumps(v)}" for k, v in table.items()) + " }"


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def snapshot(paths: list[Path]) -> dict[str, str]:
    return {str(path): digest(path.read_bytes()) for path in paths}


def copy_sources(source: Path, target: Path) -> tuple[list[dict], list[str]]:
    listed = subprocess.run(
        ["git", "ls-files", "-co", "--exclude-standard", "-z"], cwd=source,
        check=True, capture_output=True,
    ).stdout
    rows, absent = [], []
    for raw in sorted(set(listed.split(b"\0")) - {b""}):
        relative = Path(os.fsdecode(raw))
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"invalid source path: {relative}")
        path = source / relative
        try:
            before = path.lstat()
        except FileNotFoundError:
            absent.append(str(relative))
            continue
        if not stat.S_ISREG(before.st_mode):
            raise ValueError(f"source copy needs a regular file: {path}")
        data = path.read_bytes()
        if stable(before) != stable(path.lstat()):
            raise ValueError(f"source changed while copying: {path}")
        copied = target / relative
        copied.parent.mkdir(parents=True, exist_ok=True)
        with copied.open("xb") as stream:
            stream.write(data)
        os.chmod(copied, stat.S_IMODE(before.st_mode))
        if copied.read_bytes() != data:
            raise ValueError(f"source copy differs: {copied}")
        rows.append({"path": str(relative), "bytes": len(data), "sha256": digest(data)})
    return rows, absent


def patches(stage: Path, source: Path, copied: Path, manifest: dict) -> tuple[str, list]:
    text, redirects = [], []
    for url, entries in manifest["patch"].items():
        text.append(f"[patch.{json.dumps(url)}]")
        for name, entry in entries.items():
            entry = dict(entry)
            if "path" in entry:
                physical = (stage / entry["path"]).resolve(strict=True)
                selected = physical
                if physical.is_relative_to(source):
                    selected = copied / physical.relative_to(source)
                    redirects.append([url, name, str(physical), str(selected)])
                if not (selected / "Cargo.toml").is_file():
                    raise ValueError(f"missing existing stage patch manifest: {selected}")
                entry["path"] = str(selected)
            text.append(f"{json.dumps(name)} = {inline(entry)}")
        text.append("")
    return "\n".join(text) + "\n", redirects


def integration_manifest(harness: Path, stage: Path, stage_manifest: dict) -> tuple[str, Path]:
    template = tomllib.loads((harness / "Cargo.toml").read_text())
    if set(template) != {"package", "workspace", "features", "dependencies", "test"}:
        raise ValueError("unhandled integration manifest section")
    lines = ["[package]"]
    lines.extend(f"{json.dumps(k)} = {json.dumps(v)}" for k, v in template["package"].items())
    lines.extend(["", "[workspace]"])
    lines.extend(f"{json.dumps(k)} = {json.dumps(v)}" for k, v in template["workspace"].items())
    lines.extend(["", "[features]"])
    lines.extend(f"{json.dumps(k)} = {json.dumps(v)}" for k, v in template["features"].items())
    lines.extend(["", "[dependencies]"])
    dependencies = dict(template["dependencies"])
    kernel = dict(stage_manifest["workspace"]["dependencies"]["clean-kernel"])
    if "path" not in kernel or "math-overlays" not in kernel.get("features", []):
        raise ValueError("stage no longer selects the expected kernel/feature context")
    kernel_source = (stage / kernel["path"]).resolve(strict=True)
    kernel["path"] = str(kernel_source)
    dependencies["clean-kernel"] = kernel
    for name, entry in dependencies.items():
        entry = dict(entry)
        if name != "clean-kernel" and "path" in entry:
            entry["path"] = str((harness / entry["path"]).resolve(strict=True))
        lines.append(f"{json.dumps(name)} = {inline(entry)}")
    for test in template["test"]:
        lines.extend(["", "[[test]]"])
        lines.extend(f"{json.dumps(k)} = {json.dumps(v)}" for k, v in test.items())
    return "\n".join(lines) + "\n", kernel_source


def run(argv: list[str], cwd: Path, env: dict, log: Path, stdout: Path | None = None) -> None:
    print(f"Running {log.stem} (log: {log})", flush=True)
    with ExitStack() as stack:
        stream = stack.enter_context(log.open("xb"))
        output = stack.enter_context(stdout.open("xb")) if stdout else stream
        result = subprocess.run(argv, cwd=cwd, env=env, stdout=output, stderr=stream)
    if result.returncode:
        raise subprocess.CalledProcessError(result.returncode, argv)


def required_test_inventory(text: str) -> dict:
    expected = dict(zip(SUBJECTS, (7, 10)))
    inventories = {}
    current = None
    names = []
    for line in text.splitlines():
        running = re.match(r"\s*Running\s+(\S+)", line)
        if running:
            subject = Path(running[1]).stem
            if current is not None or subject not in expected or subject in inventories:
                raise ValueError("unexpected or duplicate test target")
            current, names = subject, []
        test = re.fullmatch(r"test (\S+) \.\.\. (ok|FAILED|ignored)", line)
        if test:
            if current is None or test[2] != "ok" or test[1] in names:
                raise ValueError("unexpected, failed, ignored or duplicate test")
            names.append(test[1])
        result = re.match(
            r"test result: ok\. (\d+) passed; (\d+) failed; (\d+) ignored; "
            r"(\d+) measured; (\d+) filtered out;", line
        )
        if result:
            counts = tuple(map(int, result.groups()))
            if current is None or counts != (expected[current], 0, 0, 0, 0) or len(names) != counts[0]:
                raise ValueError("required per-target test inventory did not pass in full")
            inventories[current] = {"passed": counts[0], "failed": 0, "ignored": 0, "names": names}
            current = None
    if current is not None or set(inventories) != set(expected):
        raise ValueError("missing required test target/result")
    return inventories


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trust-root", required=True, type=Path)
    parser.add_argument("--cargo-home", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parents[1]
    stage = args.trust_root.resolve(strict=True)
    cargo_home = args.cargo_home.resolve(strict=True)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    canonical = snapshot([source / "Cargo.toml", source / "Cargo.lock", stage / "Cargo.toml", stage / "Cargo.lock"])
    rows, absent, outcome = [], [], None
    generated = {}
    try:
        copied = output / "source"
        rows, absent = copy_sources(source, copied)
        stage_manifest = tomllib.loads((stage / "Cargo.toml").read_text())
        harness = copied / HARNESS
        profile, redirects = patches(stage, source, copied, stage_manifest)
        (harness / ".cargo").mkdir()
        (harness / ".cargo/config.toml").write_text(profile)
        manifest, kernel_source = integration_manifest(harness, stage, stage_manifest)
        (harness / "Cargo.toml").write_text(manifest)
        generated[str((harness / "Cargo.toml").relative_to(copied))] = digest(manifest.encode())
        (harness / "Cargo.lock").write_bytes((stage / "Cargo.lock").read_bytes())
        write_json(output / "inputs.json", {
            "canonical": canonical, "source": str(source), "copy": str(copied),
            "files": rows, "same_absent_paths": absent, "self_ir_redirects": redirects,
            "stage_patch_sha256": digest(profile.encode()),
            "generated_manifest_sha256": digest(manifest.encode()),
            "kernel_source": str(kernel_source),
        })
        env = dict(os.environ)
        env.pop("SDKROOT", None)
        env.update(CARGO_HOME=str(cargo_home), CARGO_BUILD_JOBS="6", TRUST_IR_TARGO_JOBS="6")
        wrapper = str(copied / "scripts/run-targo.sh")
        metadata = [wrapper, "metadata", "--manifest-path", str(harness / "Cargo.toml"), "--format-version", "1", "--offline"]
        run(metadata, harness, env, output / "metadata-resolve.log", output / "metadata-resolve.json")
        run(metadata + ["--locked"], harness, env, output / "metadata-locked.log", output / "metadata-locked.json")
        resolved = json.loads((output / "metadata-locked.json").read_bytes())
        if Path(resolved["workspace_root"]).resolve() != harness:
            raise ValueError("metadata selected a different workspace")
        for name in ("trust-ir", "trust-ir-build"):
            packages = [p for p in resolved["packages"] if p["name"] == name]
            expected = copied / "crates" / name / "Cargo.toml"
            if len(packages) != 1 or Path(packages[0]["manifest_path"]).resolve() != expected:
                raise ValueError(f"metadata selected a different candidate {name}")
        kernels = [p for p in resolved["packages"] if p["name"] == "clean-kernel"]
        if len(kernels) != 1 or Path(kernels[0]["manifest_path"]).resolve() != kernel_source / "Cargo.toml":
            raise ValueError("metadata selected a different kernel")
        kernel_node = next(n for n in resolved["resolve"]["nodes"] if n["id"] == kernels[0]["id"])
        if not {"math-overlays", "farkas-constructive"}.issubset(kernel_node["features"]):
            raise ValueError("stage kernel features did not unify")
        lock_digest = digest((harness / "Cargo.lock").read_bytes())
        command = [sys.executable, str(stage / "scripts/build-slot"), "--cpus", "6", "--", sys.executable,
                   str(copied / "scripts/host_scale.py"), "run", "--leg", "build", "--want", "6", "--",
                   wrapper, "test", "--manifest-path", str(harness / "Cargo.toml"), "--locked", "--offline", "-j6", "--message-format=json"]
        for subject in SUBJECTS:
            command.extend(["--test", subject])
        log = output / "tests.log"
        run(command, harness, env, log)
        text = log.read_text()
        inventories = required_test_inventory(text)
        artifacts = []
        for line in text.splitlines():
            if line.startswith("{"):
                try:
                    artifacts.append(json.loads(line))
                except ValueError:
                    pass  # The complete original log remains intact.
        actual = [a for a in artifacts if a.get("reason") == "compiler-artifact" and a["target"]["name"].replace("-", "_") == "clean_kernel"]
        if len(actual) != 1 or actual[0]["package_id"] != kernels[0]["id"] or actual[0]["features"] != kernel_node["features"]:
            raise ValueError("compiled kernel differs from the resolved stage context")
        if digest((harness / "Cargo.lock").read_bytes()) != lock_digest:
            raise ValueError("locked tests changed their development lock")
        outcome = {
            "tests": inventories, "exit": 0,
            "kernel": kernels[0]["id"], "kernel_features": kernel_node["features"],
            "development_lock_sha256": lock_digest, "raw_log_sha256": digest(log.read_bytes()),
            "operational_factory_restored": False,
        }
    finally:
        if snapshot([Path(p) for p in canonical]) != canonical:
            raise ValueError("canonical manifests/locks changed during the integration run")
        for row in rows:
            if digest((source / row["path"]).read_bytes()) != row["sha256"]:
                raise ValueError(f"source changed during integration run: {row['path']}")
            expected = generated.get(row["path"], row["sha256"])
            if digest((copied / row["path"]).read_bytes()) != expected:
                raise ValueError(f"copied source changed during integration run: {row['path']}")
    assert outcome is not None
    write_json(output / "result.json", outcome)
    print("Passed all 7 checker and 10 actual-stage producer tests.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except subprocess.CalledProcessError as error:
        print(f"Command failed with status {error.returncode}; retained its output.", file=sys.stderr)
        raise SystemExit(error.returncode)
