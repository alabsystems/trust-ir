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
from pathlib import Path, PurePosixPath
import posixpath
import re
import subprocess
try:
    import tomllib
except ModuleNotFoundError:
    if __package__:
        from ._vendor import tomli as tomllib
    else:
        from _vendor import tomli as tomllib

if __package__:
    from .check_lean_runtime_boundary import code_only, comments_removed
    from .gate_select import lean_imports, lex_rust3
    from .rust_string_literals import decode_rust_string, literal_include_positions
else:
    from check_lean_runtime_boundary import code_only, comments_removed
    from gate_select import lean_imports, lex_rust3
    from rust_string_literals import decode_rust_string, literal_include_positions

PACKAGES = ("lean/semr", "lean/semr-memory", "lean/trust_ir-semantics")
CORE = {"Init", "Lean", "Std", "Lake"}


def files(root):
    result = set()
    for directory, dirs, names in os.walk(root, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake", "target", "__pycache__"}]
        for name in names + [d for d in dirs if (Path(directory) / d).is_symlink()]:
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
    directories = {"."}
    for path in selected:
        directories.update(parent.as_posix() for parent in PurePosixPath(path).parents)

    def projected_lookup(parts, current=(), active=frozenset(), *, directory=False):
        # Walk spellings rather than normalizing away prerequisites. A file-only
        # projection creates parents of selected entries and retains selected links.
        for index, part in enumerate(parts):
            if part in ("", "."):
                continue
            if part == "..":
                if not current:
                    problems.append("escaping source path in projection: " + "/".join(parts))
                    return None
                current = current[:-1]
                continue
            candidate = "/".join(current + (part,))
            node = root / candidate
            needs_directory = directory or index + 1 < len(parts)
            if node.is_symlink():
                if candidate not in selected:
                    problems.append("missing source symlink in projection: " + candidate)
                    return None
                target = os.readlink(node)
                if posixpath.isabs(target):
                    problems.append("nonportable source symlink in projection: " + candidate)
                    return None
                if candidate in active:
                    problems.append("cyclic source symlink in projection: " + candidate)
                    return None
                current = projected_lookup(target.split("/"), current, active | {candidate},
                                           directory=needs_directory)
                if current is None:
                    return None
            else:
                if needs_directory:
                    if candidate not in directories or not node.is_dir():
                        problems.append("missing source directory in projection: " + candidate)
                        return None
                elif candidate not in selected or not node.is_file():
                    problems.append("missing source input in projection: " + candidate)
                    return None
                current += (part,)
        final = "/".join(current) or "."
        if directory:
            if final not in directories or not (root / final).is_dir():
                problems.append("missing source directory in projection: " + final)
                return None
        elif final not in selected or not (root / final).is_file():
            problems.append("missing source input in projection: " + final)
            return None
        return current

    def read(path, *, spelling=None):
        file = root / path
        if path not in selected or not file.is_file():
            problems.append("missing source input: " + path)
            return None
        resolved = file.resolve()
        if not resolved.is_relative_to(root):
            problems.append("escaping source input: " + path)
            return None
        if spelling is not None:
            original = root / spelling
            if not original.is_file():
                problems.append("missing source input: " + spelling)
                return None
            original_resolved = original.resolve()
            if not original_resolved.is_relative_to(root):
                problems.append("escaping source input: " + spelling)
                return None
            if original_resolved != resolved:
                problems.append("source path normalization changes resolution: " + spelling)
                return None
        if projected_lookup((spelling if spelling is not None else path).split("/")) is None:
            return None
        return file.read_bytes()

    def read_json_object(path, label):
        data = read(path)
        if data is None:
            return None
        try:
            document = json.loads(data)
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            problems.append(f"invalid {label} JSON: {path}: {error}")
            return None
        if not isinstance(document, dict):
            problems.append(f"invalid {label} JSON: {path}: expected an object")
            return None
        return document

    for package in PACKAGES:
        read(package + "/lean-toolchain")
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
                text = comments_removed(data.decode())
                commands = code_only(text)
                # The shared lexer validates escaped identifiers but preserves
                # their contents; those contents cannot declare targets/fields.
                commands = re.sub(r"«[^»]*»", lambda m: re.sub(r"[^\n]", " ", m[0]), commands)
                targets = list(re.finditer(r"(?m)^[ \t]*lean_(?:lib|exe)\b", commands))
                for index, target in enumerate(targets):
                    end = targets[index + 1].start() if index + 1 < len(targets) else len(text)
                    name = re.match(r"\s+([A-Za-z_]\w*)\b", commands[target.end():end])
                    if name is None or name[1] == "where":
                        problems.append("unsupported Lean target declaration: " + config)
                        continue
                    start = target.end() + name.end()
                    where = re.match(r"\s+where\b", commands[start:end])
                    if where:
                        start += where.end()
                        block = commands[start:end]
                    elif re.match(r"[ \t\r]*(?:\n|$)", commands[start:end]):
                        # A bare target has defaults, never a later command's fields.
                        block = ""
                    else:
                        problems.append("unsupported Lean target configuration: " + config + " -> " + name[1])
                        continue
                    roots = re.search(r"\broots\s*:=\s*#\[([^]]*)\]", block)
                    single = re.search(r"\broot\s*:=\s*`([\w.]+)", block)
                    modules = re.findall(r"`([\w.]+)", roots[1]) if roots else [single[1] if single else name[1]]
                    directory_key = re.search(r"\bsrcDir\s*:=", block)
                    directory = (re.match(r'\s*"([^"\\]*)"', text[start + directory_key.end():end])
                                 if directory_key else None)
                    if directory_key and directory is None:
                        problems.append("unsupported Lean source directory: " + config + " -> " + name[1])
                        continue
                    for module in modules:
                        path = posixpath.normpath(package + "/" + (directory[1] if directory else ".") + "/" + module.replace(".", "/") + ".lean")
                        edges.append((config, path)); read(path)
    for required in ("lean/semr/SemR.lean", "lean/semr/Main.lean", "lean/semr/FRAGMENT.tsv",
                     "lean/semr/QUOTED_MODEL.tsv", "lean/semr-memory/SemRFrameChecks.lean",
                     "lean/semr-memory/FrameAudit.lean", "lean/semr-memory/frame-audit-refusals.json"):
        read(required)

    for package in PACKAGES:
        manifest_path = package + "/lake-manifest.json"
        manifest = read_json_object(manifest_path, "Lean dependency manifest")
        if manifest is not None:
            dependencies = manifest.get("packages", [])
            if not isinstance(dependencies, list):
                problems.append("invalid Lean dependency array: " + manifest_path)
            else:
                for dependency in dependencies:
                    if not isinstance(dependency, dict):
                        problems.append("invalid Lean dependency record: " + manifest_path)
                        continue
                    if dependency.get("type") != "path":
                        problems.append("unexpected nonlocal Lean dependency: " + package)
                        continue
                    if not all(isinstance(dependency.get(key), str) for key in ("dir", "configFile")):
                        problems.append("invalid local Lean dependency paths: " + manifest_path)
                        continue
                    original_directory = posixpath.join(package, dependency["dir"])
                    destination = posixpath.normpath(original_directory)
                    config_file = dependency["configFile"]
                    if destination == ".." or destination.startswith(("../", "/")):
                        problems.append("escaping Lean dependency: " + destination)
                    elif posixpath.isabs(config_file):
                        problems.append("escaping Lean dependency: " + config_file)
                    else:
                        original_target = posixpath.join(original_directory, config_file)
                        target = posixpath.normpath(posixpath.join(destination, config_file))
                        if target == ".." or target.startswith(("../", "/")):
                            problems.append("escaping Lean dependency: " + target)
                        else:
                            edges.append((manifest_path, target)); read(target, spelling=original_target)
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

    # The lexer removes comments and replaces each string literal with "".
    for path in sorted(p for p in selected if p.endswith(".rs")):
        data = read(path)
        if data is None:
            continue
        raw_literals = []
        literals, code, _ = lex_rust3(data.decode(), raw_literals=raw_literals)
        positions = list(re.finditer('""', code))
        if len(literals) != len(positions) or len(raw_literals) != len(literals):
            problems.append("Rust literal inventory mismatch: " + path); continue
        values = {m.start(): (value, raw) for m, value, raw in zip(positions, literals, raw_literals)}
        for position in literal_include_positions(code):
            value, raw = values[position]
            if not raw:
                try:
                    value = decode_rust_string(value)
                except ValueError as error:
                    problems.append(f"invalid Rust literal include: {path}: {error}")
                    continue
            destination = posixpath.normpath(posixpath.dirname(path) + "/" + value)
            if destination.startswith(("lean/semr/", "lean/semr-memory/")):
                edges.append((path, destination)); read(destination)

    for manifest in sorted(p for p in selected if p.startswith("lean/semr/fixtures/") and p.endswith("/MANIFEST.json")):
        table = read_json_object(manifest, "SemR fixture manifest")
        if table is None:
            continue
        fixtures = table.get("fixtures")
        if (table.get("schema") != "trust.generic-scalar-model-fixtures.v1" or
                not isinstance(fixtures, list) or not fixtures):
            problems.append("unsupported or empty SemR fixture manifest: " + manifest)
            continue
        for row in fixtures:
            if (not isinstance(row, dict) or not isinstance(row.get("file"), str) or
                    not row["file"] or type(row.get("bytes")) is not int or row["bytes"] < 0 or
                    not isinstance(row.get("sha256"), str) or
                    re.fullmatch(r"[0-9a-f]{64}", row["sha256"]) is None):
                problems.append("invalid SemR fixture record: " + manifest)
                continue
            original_path = posixpath.join("lean/semr/fixtures", row["file"])
            path = posixpath.normpath(original_path)
            if not path.startswith("lean/semr/fixtures/"):
                problems.append("escaping SemR fixture: " + path); continue
            edges.append((manifest, path))
            payload = read(path, spelling=original_path)
            if payload is not None and (len(payload) != row["bytes"] or hashlib.sha256(payload).hexdigest() != row["sha256"]):
                problems.append("SemR fixture bytes changed: " + path)

    record = read_json_object("LICENSES/MiniRust.json", "MiniRust provenance")
    read("THIRD_PARTY.md"); read("NOTICE")
    if record is not None:
        licenses = record.get("license_files")
        if (type(record.get("schema")) is not int or
                not all(isinstance(record.get(key), str) for key in ("translation", "translation_sha256")) or
                not isinstance(record.get("revision", ""), str) or not isinstance(licenses, dict) or
                not all(isinstance(expected, dict) and
                        all(isinstance(expected.get(key), str) for key in ("sha256", "git_blob_sha1"))
                        for expected in licenses.values())):
            problems.append("invalid MiniRust provenance fields: LICENSES/MiniRust.json")
        else:
            if record.get("schema") != 1:
                problems.append("invalid MiniRust provenance schema")
            if record["translation"] != "lean/semr/MiniRust.lean":
                problems.append("unexpected MiniRust translation path")
            translated = read(record["translation"])
            if translated is not None and hashlib.sha256(translated).hexdigest() != record["translation_sha256"]:
                problems.append("MiniRust translation identity changed")
            revision = record.get("revision", "")
            if not re.fullmatch(r"[0-9a-f]{40}", revision) or (translated is not None and
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
