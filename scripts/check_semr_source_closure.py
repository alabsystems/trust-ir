#!/usr/bin/env python3
# Copyright 2026 Andrew Yates | Apache-2.0
"""Check SemR package/consumer inputs in a checkout or local source projection.

This checks source presence, local Lean imports/dependencies, literal Rust
includes into SemR, fixture bytes and upstream notices. It does not stage,
transform dependency pins, compile Rust or establish a publication verdict.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import posixpath
import re
import subprocess
import tomllib

if __package__:
    from .gate_select import lean_imports, lex_rust3
    from .lean_proofs import strip_lean_comments
else:
    from gate_select import lean_imports, lex_rust3
    from lean_proofs import strip_lean_comments

PACKAGES = ("lean/semr", "lean/semr-memory", "lean/trust_ir-semantics")
CORE = {"Init", "Lean", "Std", "Lake"}


def files(root):
    result = set()
    for directory, dirs, names in os.walk(root, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake", "target", "__pycache__"}]
        for name in names:
            result.add((Path(directory) / name).relative_to(root).as_posix())
    return result


def manifest_selection(root, manifest):
    specs = []
    for raw in manifest.read_text().splitlines():
        line = raw.split("#", 1)[0].strip().removeprefix("./")
        if not line:
            continue
        if line.startswith(":") or line == "!":
            raise ValueError("invalid publication pathspec")
        specs.append(":(exclude)" + line[1:] if line.startswith("!") else line)
    if not specs or all(s.startswith(":(exclude)") for s in specs):
        raise ValueError("publication manifest must contain positive includes")
    data = subprocess.check_output(["git", "-C", str(root), "ls-files", "--cached", "--others",
                                    "--exclude-standard", "-z", "--", *specs])
    return {p.decode() for p in data.split(b"\0") if p}


def check(root, selected):
    root = root.resolve()
    problems, edges = [], []

    def read(path):
        file = root / path
        if path not in selected or not file.is_file():
            problems.append("missing source input: " + path)
            return None
        if not file.resolve().is_relative_to(root):
            problems.append("escaping source input: " + path)
            return None
        return file.read_bytes()

    for package in PACKAGES:
        for metadata in ("lean-toolchain", "lake-manifest.json"):
            read(package + "/" + metadata)
        if not any(package + "/" + name in selected for name in ("lakefile.lean", "lakefile.toml")):
            problems.append("missing package configuration: " + package)
        config = package + "/lakefile.toml"
        if config in selected:
            data = read(config)
            if data:
                table = tomllib.loads(data.decode())
                for target in table.get("lean_lib", []) + table.get("lean_exe", []):
                    for module in target.get("roots", [target.get("root", target["name"])]):
                        path = package + "/" + target.get("srcDir", ".") + "/" + module.replace(".", "/") + ".lean"
                        path = posixpath.normpath(path)
                        edges.append((config, path)); read(path)
        config = package + "/lakefile.lean"
        if config in selected:
            data = read(config)
            if data:
                text = strip_lean_comments(data.decode())
                targets = list(re.finditer(r"(?m)^lean_(?:lib|exe)\s+([A-Za-z_]\w*)\s+where\b", text))
                for index, target in enumerate(targets):
                    block = text[target.end():targets[index + 1].start() if index + 1 < len(targets) else len(text)]
                    roots = re.search(r"\broots\s*:=\s*#\[([^]]*)\]", block)
                    single = re.search(r"\broot\s*:=\s*`([\w.]+)", block)
                    modules = re.findall(r"`([\w.]+)", roots[1]) if roots else [single[1] if single else target[1]]
                    directory = re.search(r'\bsrcDir\s*:=\s*"([^"]*)"', block)
                    for module in modules:
                        path = posixpath.normpath(package + "/" + (directory[1] if directory else ".") + "/" + module.replace(".", "/") + ".lean")
                        edges.append((config, path)); read(path)
    for required in ("lean/semr/SemR.lean", "lean/semr/Main.lean", "lean/semr/FRAGMENT.tsv",
                     "lean/semr/QUOTED_MODEL.tsv", "lean/semr-memory/SemRFrameChecks.lean",
                     "lean/semr-memory/FrameAudit.lean", "lean/semr-memory/frame-audit-refusals.json"):
        read(required)

    for package in PACKAGES:
        manifest = read(package + "/lake-manifest.json")
        if manifest:
            for dependency in json.loads(manifest).get("packages", []):
                if dependency.get("type") != "path":
                    problems.append("unexpected nonlocal Lean dependency: " + package)
                    continue
                destination = posixpath.normpath(package + "/" + dependency["dir"])
                if destination.startswith("../") or destination.startswith("/"):
                    problems.append("escaping Lean dependency: " + destination)
                else:
                    target = destination + "/" + dependency["configFile"]
                    edges.append((package + "/lake-manifest.json", target)); read(target)
        for path in sorted(p for p in selected if p.startswith(package + "/") and p.endswith(".lean")):
            data = read(path)
            if data is None:
                continue
            for module in lean_imports(data.decode()):
                if module.split(".")[0] in CORE:
                    continue
                candidates = [p + "/" + module.replace(".", "/") + ".lean" for p in (package,) + tuple(p for p in PACKAGES if p != package)]
                found = next((p for p in candidates if p in selected), None)
                if found is None:
                    problems.append(f"missing Lean import: {path} -> {module}")
                else:
                    edges.append((path, found)); read(found)

    # The lexer removes comments and replaces every normal/raw literal by "".
    # Match only actual literal include calls, never examples inside a string.
    include = re.compile(r'\binclude(?:_str|_bytes)?\s*!\s*\(\s*(?P<literal>"")\s*,?\s*\)')
    for path in sorted(p for p in selected if p.endswith(".rs")):
        data = read(path)
        if data is None:
            continue
        literals, code, _ = lex_rust3(data.decode())
        positions = list(re.finditer('""', code))
        if len(literals) != len(positions):
            problems.append("Rust literal inventory mismatch: " + path); continue
        values = {m.start(): value for m, value in zip(positions, literals)}
        for match in include.finditer(code):
            value = values[match.start("literal")]
            destination = posixpath.normpath(posixpath.dirname(path) + "/" + value)
            if destination.startswith(("lean/semr/", "lean/semr-memory/")):
                edges.append((path, destination)); read(destination)

    for manifest in sorted(p for p in selected if p.startswith("lean/semr/fixtures/") and p.endswith("/MANIFEST.json")):
        data = read(manifest)
        if data is None:
            continue
        table = json.loads(data)
        if table.get("schema") != "trust.generic-scalar-model-fixtures.v1" or not table.get("fixtures"):
            problems.append("unsupported or empty SemR fixture manifest: " + manifest)
            continue
        for row in table["fixtures"]:
            path = posixpath.normpath("lean/semr/fixtures/" + row["file"])
            if not path.startswith("lean/semr/fixtures/"):
                problems.append("escaping SemR fixture: " + path); continue
            edges.append((manifest, path))
            payload = read(path)
            if payload is not None and (len(payload) != row["bytes"] or hashlib.sha256(payload).hexdigest() != row["sha256"]):
                problems.append("SemR fixture bytes changed: " + path)

    provenance = read("LICENSES/MiniRust.json")
    read("THIRD_PARTY.md"); read("NOTICE")
    if provenance:
        record = json.loads(provenance)
        if record.get("schema") != 1:
            problems.append("invalid MiniRust provenance schema")
        if record["translation"] != "lean/semr/MiniRust.lean":
            problems.append("unexpected MiniRust translation path")
        translated = read(record["translation"])
        if translated and hashlib.sha256(translated).hexdigest() != record["translation_sha256"]:
            problems.append("MiniRust translation identity changed")
        revision = record.get("revision", "")
        if not re.fullmatch(r"[0-9a-f]{40}", revision) or (translated and
                ("from MiniRust " + revision).encode() not in translated):
            problems.append("MiniRust revision marker disagrees with provenance")
        if set(record["license_files"]) != {"LICENSES/MiniRust-MIT.txt", "LICENSES/MiniRust-APACHE.txt"}:
            problems.append("both upstream MiniRust license texts are required")
        for path, expected in record["license_files"].items():
            data = read(path)
            if data is not None:
                blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
                if hashlib.sha256(data).hexdigest() != expected["sha256"] or blob != expected["git_blob_sha1"]:
                    problems.append("upstream license bytes changed: " + path)
    return {"scope": "SemR source/import/literal-include and notice closure only",
            "edges": [list(edge) for edge in sorted(set(edges))], "problems": sorted(set(problems))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tree", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    selected = manifest_selection(args.tree, args.manifest) if args.manifest else files(args.tree)
    result = check(args.tree, selected)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    for problem in result["problems"]:
        print(problem)
    print(f"semr-source-closure: edges={len(result['edges'])} problems={len(result['problems'])}")
    raise SystemExit(bool(result["problems"]))


if __name__ == "__main__":
    main()
