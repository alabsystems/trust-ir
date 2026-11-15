#!/usr/bin/env python3
"""Inventory the explicit Lean logical/runtime boundary; never issue proof grades.

The runtime is intentionally unproved. This guard conserves its recorded obligations,
checks source attachment/import custody and binds exact source bytes for later readers.
A successful guard is neither a kernel replay nor a runtime correspondence certificate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

PRODUCER = Path("lean/trust_ir-semantics")
LEDGER = PRODUCER / "runtime-boundary.json"
EXPECTED = (7125, 7084, 41, 15)
# Immutable historical subjects; editable ledger bytes cannot authorize a new baseline.
BASELINE_IDENTITY = {
    "root_subject": "98e439cf1281e226c88448cbb24ebe9fbb07fab5",
    "ir_source": "5e950fbff8b1beb5f0a7388a30a124ab4be3d66a",
    "scope": "imported_restored_declarations",
    "roster_sha256": "89d0b2f955f0204a4adcab51a305cee0fd20a1e524a9c69c7c8f24feec7493dc",
    "complete_inventory_sha256": "3d329ae9e3287c0a77b17223b7f6df1dbeb6c0ec32ead43c6f34ff9887fb1e6e",
}
REPAIR_BASE = "7895a3dd1822c7f8034f7dc7bd7e826b2392bfe6"

CALLER_INPUTS = [
    "scripts/ci-self-verify.sh",
    "scripts/lean_proofs.py",
    "crates/trust-ir-conformance/tests/lean_exec_differential.rs",
    "crates/trust-ir-conformance/tests/common/aggregate_memory.rs",
    "crates/trust-ir-conformance/tests/common/compact_value_graph.rs",
    "crates/trust-ir-conformance/tests/common/generic_coro_prefix.rs",
    "crates/trust-ir-conformance/tests/common/generic_coro_prefix_seqmap.rs",
    "crates/trust-ir-conformance/tests/common/generic_coro_all_blocks.rs",
]


class BoundaryError(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise BoundaryError(message)


def comments_removed(text: str) -> str:
    """Remove nested Lean comments while retaining line positions and strings."""
    out, index, depth, string = [], 0, 0, False
    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif string:
            out.append(text[index])
            if text[index] == "\\" and index + 1 < len(text):
                index += 1
                out.append(text[index])
            elif text[index] == '"':
                string = False
            index += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            index += 2
        elif pair == "--":
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - index))
            index = end
        else:
            string = text[index] == '"'
            out.append(text[index])
            index += 1
    require(depth == 0 and not string, "unterminated Lean comment or string")
    return "".join(out)


def unique(rows: list[dict], keys: tuple[str, ...], label: str) -> set[tuple]:
    identities = [tuple(row[key] for key in keys) for row in rows]
    require(len(set(identities)) == len(rows), f"duplicate {label}")
    return set(identities)


def imports(text: str) -> list[str]:
    found = []
    for row in re.findall(r"(?m)^\s*import\s+([^\n]+)", comments_removed(text)):
        for module in row.split():
            require(re.fullmatch(r"[A-Za-z][A-Za-z0-9_'.]*", module) is not None,
                    f"unrecognized Lean import: {module}")
            found.append(module)
    return found


def runtime_declarations(module: str, text: str) -> set[tuple[str, str]]:
    stack: list[tuple[str, str]] = []
    found = set()
    cleaned = comments_removed(text)
    for line in cleaned.splitlines():
        namespace = re.fullmatch(r"namespace\s+([\w.]+)\s*", line)
        if namespace:
            stack.append(("namespace", namespace[1]))
            continue
        if line.strip() == "mutual":
            stack.append(("mutual", ""))
            continue
        if re.fullmatch(r"end(?:\s+[\w.]+)?\s*", line):
            require(bool(stack), f"unbalanced runtime namespace in {module}")
            stack.pop()
            continue
        declaration = re.match(r"\s*(private\s+)?unsafe def\s+([\w.]+)\b", line)
        if declaration:
            prefix = ".".join(name for kind, name in stack if kind == "namespace")
            name = prefix + "." + declaration[2]
            if declaration[1]:
                name = "_private." + module + ".0." + name
            identity = (module, name)
            require(identity not in found, f"duplicate runtime declaration {name}")
            found.add(identity)
    require(not stack, f"unclosed runtime namespace in {module}")
    require(len(found) == len(re.findall(r"\bunsafe\s+def\b", cleaned)),
            f"unclassified unsafe declaration in {module}")
    require(not re.search(r"\bunsafe\s+(?:opaque|axiom|abbrev)\b|\bpartial\s+def\b", cleaned),
            f"unregistered unsafe/partial declaration kind in {module}")
    return found


def logical_extern_declarations(module: str, text: str) -> list[tuple[str, int, str, str]]:
    """Resolve the reviewed extern syntax in its actual namespace/block scope.

    This is a fail-closed source inventory, not a Lean parser or typed identity
    certificate. Private module prefix zero is the measured Lean4.8 identity
    used by the existing interface; unsupported scope syntax is refused.
    """
    cleaned = comments_removed(text)
    cleaned = re.sub(r'trustIrExtern\s+(\d+)\s+("[^"\n]+")',
                     r'extern \1 c inline \2', cleaned)
    declarations = list(re.finditer(
        r'(?m)^[ \t]*@\[nospecialize,\s*extern\s+(\d+)\s+c\s+inline\s+"([^"\n]+)"\]\s*(private\s+)?def\s+([\w.]+)\b',
        cleaned))
    if not declarations:
        return []
    # Strings cannot introduce namespace/end commands into the scope walk.
    commands = re.sub(r'"(?:\\.|[^"\\])*"',
                      lambda match: re.sub(r"[^\n]", " ", match[0]), cleaned,
                      flags=re.DOTALL)
    stack: list[tuple[str, str]] = []
    result = []
    cursor, index = 0, 0
    for line in commands.splitlines(keepends=True):
        while index < len(declarations) and declarations[index].start() < cursor + len(line):
            declaration = declarations[index]
            require("_root_" not in declaration[4].split("."),
                    f"unsupported absolute logical declaration in {module}")
            prefix = ".".join(name for kind, name in stack if kind == "namespace")
            name = ".".join(part for part in (prefix, declaration[4]) if part)
            if declaration[3]:
                name = "_private." + module + ".0." + name
            result.append((module, int(declaration[1]), declaration[2], name))
            index += 1
        command = line.strip()
        if re.match(r"(?:namespace|section|noncomputable\s+section|mutual|end)\b", command):
            namespace = re.fullmatch(r"namespace\s+([\w.]+)", command)
            section = re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+([\w.]+))?", command)
            closing = re.fullmatch(r"end(?:\s+([\w.]+))?", command)
            if namespace:
                require("_root_" not in namespace[1].split("."),
                        f"unsupported absolute logical namespace in {module}")
                stack.append(("namespace", namespace[1]))
            elif section:
                stack.append(("section", section[1] or ""))
            elif command == "mutual":
                stack.append(("mutual", ""))
            elif closing:
                require(bool(stack), f"unbalanced logical scope in {module}")
                _, name = stack.pop()
                require(closing[1] is None or closing[1] == name,
                        f"mismatched logical scope end in {module}")
            else:
                raise BoundaryError(f"unclassified logical scope syntax in {module}")
        cursor += len(line)
    require(not stack and index == len(declarations), f"unclosed logical scope in {module}")
    return result


def inspect(root: Path) -> dict:
    root = root.resolve()
    producer = root / PRODUCER
    ledger = json.loads((root / LEDGER).read_text())
    require(ledger.get("schema") == 2, "unsupported runtime boundary schema")
    baseline = ledger["baseline"]
    require(all(baseline.get(key) == value for key, value in BASELINE_IDENTITY.items()),
            "historical baseline identity changed")
    require(ledger.get("repair_base") == REPAIR_BASE, "historical repair predecessor changed")
    total, logical, count, interfaces_count = EXPECTED
    require((baseline["total_obligations"], baseline["logical_safe_obligations"],
             baseline["runtime_unproved_obligations"]) == (total, logical, count),
            "baseline obligations were changed or dropped")
    require(total == logical + count, "baseline conservation is inconsistent")
    obligations = ledger["runtime_obligations"]
    interfaces = ledger["interfaces"]
    require(len(obligations) == count and len(interfaces) == interfaces_count,
            "runtime obligation/interface census changed")
    unique(obligations, ("original_module", "original_full_name"), "original obligation identity")
    expected = unique(obligations, ("runtime_module", "runtime_full_name"), "runtime obligation identity")
    baseline_bytes = (producer / "runtime-boundary-baseline.json").read_bytes()
    require(hashlib.sha256(baseline_bytes).hexdigest() == baseline["roster_sha256"],
            "baseline roster source digest changed")
    frozen = json.loads(baseline_bytes)
    require(frozen["trust_ir_declarations"] == total and frozen["unsafe_count"] == count,
            "baseline roster population differs")
    original = {(row["original_module"], row["original_full_name"]) for row in obligations}
    require(original == {(row["module"], row["name"]) for row in frozen["unsafe_declarations"]},
            "original full-name/module obligations differ from the baseline roster")
    unique(interfaces, ("logical_module", "logical_full_name"), "logical interface")
    unique(interfaces, ("symbol",), "runtime ABI symbol")
    for row in obligations:
        require(row["state"] == "UNPROVED" and row["certified"] is False,
                "runtime metadata cannot promote an unproved obligation")
        require(row["original_kind"] == "definition" and row["original_safety"] == "unsafe",
                "baseline runtime safety/kind was reclassified")
    for row in interfaces:
        require(row["correspondence"] == "UNPROVED" and row["certified"] is False,
                "ABI metadata cannot mint a correspondence certificate")
    support = ledger["support_obligations"]
    require(len(support) == 3, "support obligation census changed")
    unique(support, ("id",), "support obligation")
    require({row["id"] for row in support} == {
        "runtime-module-initialization", "native-only-lake-link", "logical-fixture-native-evaluation"},
        "support obligation identities changed")
    for row in support:
        require(row["state"] == "UNPROVED" and row["certified"] is False,
                "support metadata cannot promote an unproved obligation")
        require(bool(row["role"]) and bool(row["source_inputs"]), "support inputs/role are absent")
        for relative in row["source_inputs"]:
            relative_path = Path(relative)
            path = root / relative_path
            require(not relative_path.is_absolute() and ".." not in relative_path.parts
                    and path.is_file() and not path.is_symlink()
                    and path.resolve().is_relative_to(root), "support input escaped its source root")
    attachment = ledger["native_attachment"]
    require(attachment == {
        "logical_module": "TrustIrNativeLink", "provider_module": "TrustIrRuntime",
        "activation_module": "TrustIr.Semantics.Eval",
        "initializer_symbol": "initialize_TrustIrNativeLink",
        "provider_initializer_symbol": "initialize_TrustIrRuntime",
        "initializer_source": "lean/trust_ir-semantics/native/runtime_init.c",
        "lean430_initializer": {"arity": 1, "symbols": "initialize_ + Lake.Module.dynlibName"},
        "fixture_modules": ["TrustIr.Semantics.ExecutableFixtures", "TrustIr.Semantics.FloatFixtures"]},
        "native attachment identity changed")
    link = comments_removed((producer / "TrustIrNativeLink.lean").read_text()).strip()
    require(link == "import Init",
            "native attachment must have only its reviewed pure import and no declarations")
    activation = producer / (attachment["activation_module"].replace(".", "/") + ".lean")
    require(imports(activation.read_text()).count("TrustIrNativeLink") == 1,
            "semantic evaluation lacks its native attachment")
    modules = ledger["runtime_modules"]
    require(len(set(modules)) == len(modules), "duplicate runtime module")
    require(set(modules) == {row[0] for row in expected}, "runtime module inventory is incomplete")
    sources = {}
    for path in producer.rglob("*"):
        if ".lake" in path.relative_to(producer).parts:
            continue
        require(not path.is_symlink(), f"source symlink is not an immutable runtime input: {path}")
        if path.is_file():
            sources[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    guard = Path(__file__).resolve()
    require((root / "scripts/check_lean_runtime_boundary.py").read_bytes() == guard.read_bytes(),
            "executed guard differs from the requested source guard")
    sources["scripts/check_lean_runtime_boundary.py"] = hashlib.sha256(guard.read_bytes()).hexdigest()
    actual = set()
    exports = []
    for module in modules:
        require(module.startswith("TrustIrRuntime."), "runtime module escaped its library")
        path = producer / (module.replace(".", "/") + ".lean")
        text = path.read_text()
        actual |= runtime_declarations(module, text)
        for symbol, provider in re.findall(r"@\[export\s+([\w]+)\]\s*unsafe def\s+([\w]+)\b",
                                           comments_removed(text)):
            exports.append((module, symbol, provider))
    require(actual == expected, f"runtime declaration identity mismatch: missing={expected-actual}, extra={actual-expected}")
    require(len(exports) == interfaces_count, "runtime exports are not the complete interface census")
    for module in modules:
        text = (producer / (module.replace(".", "/") + ".lean")).read_text()
        require(len(re.findall(r"@\[[^\]]*\bexport\b", comments_removed(text))) ==
                sum(row[0] == module for row in exports), "unclassified runtime export attribute")
    expected_exports = {(row["runtime_module"], row["symbol"], row["runtime_provider"]) for row in interfaces}
    require(set(exports) == expected_exports, "runtime export/provider mismatch")
    # Reviewed two-version expansion: preserve the full boxed export ABI and inline call pattern.
    compat = (producer / "TrustIr/CompilerCompat.lean").read_text()
    marker = 'macro "trustIrExtern "'
    require(compat.count(marker) == 1, "extern compatibility macro missing or duplicated")
    expansion = marker + compat.split(marker, 1)[1].split("\n\n", 1)[0]
    require(hashlib.sha256(expansion.encode()).hexdigest() ==
            "7d1033b86729c82c18c6e24f68fc78ea6150e63478a289e6fd3076de2688a7d5", "extern compatibility macro expansion changed")
    all_externs = []
    extern_attributes = 0
    for path in (producer / "TrustIr").rglob("*.lean"):
        text = comments_removed(path.read_text())
        require(not re.search(r"\bunsafe\s+(?:def|opaque|axiom|abbrev)\b", text),
                f"unsafe runtime declaration leaked into logical source: {path}")
        require(not re.search(r"@\[[^\]]*\bimplemented_by\b", text),
                f"unregistered codegen replacement in logical source: {path}")
        extern_attributes += len(re.findall(r"@\[[^\]]*\b(?:extern|trustIrExtern)\b", text))
        module = path.relative_to(producer).with_suffix("").as_posix().replace("/", ".")
        all_externs.extend(logical_extern_declarations(module, text))
    require(len(all_externs) == extern_attributes == interfaces_count, "logical extern interface census changed")
    header = """/* Copyright 2026 Andrew Yates | Apache-2.0
 * Actual boxed Lean provider export ABI, including erased type placeholders.
 * Runtime correspondence remains UNPROVED. Checked against runtime-boundary.json.
 */
#ifndef TRUST_IR_RUNTIME_FFI_H
#define TRUST_IR_RUNTIME_FFI_H
#include <lean/lean.h>

"""
    for row in interfaces:
        abi = row["abi"]
        arity = abi["arity"]
        require(type(arity) is int and 0 < arity <= 16
                and len(abi["parameter_types"]) == arity
                and abi["return_type"] == "lean_object*"
                and all(kind == "lean_object*" for kind in abi["parameter_types"]),
                "unsupported or inconsistent observed Lean export ABI")
        header += f'LEAN_EXPORT {abi["return_type"]} {row["symbol"]}({", ".join(abi["parameter_types"])});\n'
        pattern = row["symbol"] + "(" + ", ".join("#" + str(i) for i in range(1, arity + 1)) + ")"
        wanted = [(module, count, actual, name) for module, count, actual, name in all_externs
                  if module == row["logical_module"] and count == arity and actual == pattern
                  and row["logical_full_name"] == name]
        require(len(wanted) == 1, f"logical interface attachment mismatch: {row['logical_full_name']}")
        candidates = [name for module, name in actual if module == row["runtime_module"]
                      and name.endswith("." + row["runtime_provider"]) and not name.startswith("_private.")]
        require(len(candidates) == 1, "ABI provider is not a named public runtime obligation")
        require(row["runtime_full_name"] == candidates[0]
                and (row["runtime_module"], row["runtime_full_name"]) in actual,
                "ABI full-name identity does not match the actual runtime obligation")
    header += "\n#endif\n"
    require((producer / "native/runtime_ffi.h").read_text() == header,
            "native provider header differs from the boxed ABI inventory")
    seen, pending = set(), ["TrustIr"]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        require(not module.startswith("TrustIrRuntime"), "runtime library leaked into the logical import closure")
        path = producer / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            require(module.split(".")[0] in {"Init", "Lean", "Std"},
                    f"unbound logical import {module}")
            continue
        seen.add(module)
        pending.extend(imports(path.read_text()))
    for module in modules:
        text = (producer / (module.replace(".", "/") + ".lean")).read_text()
        for dependency in imports(text):
            require(dependency in modules or dependency in seen
                    or dependency.split(".")[0] in {"Lean", "Init", "Std"},
                    f"unregistered runtime dependency: {dependency}")
    # Native-only linking must remain acyclic: provider foundations cannot import
    # the attachment whose own native facet builds that provider.
    visited, pending = set(), list(modules)
    while pending:
        module = pending.pop()
        require(module != "TrustIrNativeLink", "runtime provider depends on its native attachment")
        if module in visited:
            continue
        visited.add(module)
        path = producer / (module.replace(".", "/") + ".lean")
        if path.is_file():
            pending.extend(imports(path.read_text()))
    foundations = sorted(name for name in visited if name.startswith("TrustIr."))
    require(ledger.get("native_foundation_modules_lean430") == foundations,
            "native foundations differ from the provider import closure")
    actual_runtime_sources = {p.relative_to(producer).with_suffix("").as_posix().replace("/", ".")
                              for p in (producer / "TrustIrRuntime").rglob("*.lean")}
    require(actual_runtime_sources == set(modules), "runtime source module census changed")
    lake_source = (producer / "lakefile.lean").read_text()
    for name, digest in {'trustIrRuntimeInput': '8ecf5e5f4f0d62427f9bed3d716564f48df5daa51ea65df89a48b6a7f817db3f', 'trustIrNativeFacet': '043a9c2c26db8806d15982fb34c145293de1d8e1f85171f3aa516edf834c386a'}.items():
        marker = 'macro "' + name + ' "'
        require(lake_source.count(marker) == 1, "native Lake compatibility macro missing or duplicated")
        expansion = marker + lake_source.split(marker, 1)[1].split("\n\n", 1)[0]
        require(hashlib.sha256(expansion.encode()).hexdigest() == digest,
                "native Lake compatibility macro expansion changed")
    marker = 'macro "trustIrRuntimeInitFlags "'
    require(lake_source.count(marker) == 1, "native initializer ABI macro missing or duplicated")
    expansion = marker + lake_source.split(marker, 1)[1].split("\n\n", 1)[0]
    require(hashlib.sha256(expansion.encode()).hexdigest() ==
            "516cd78d61bd433ed0f0038d5ae48cf50f9127314c922434c6b244e9107487f3", "native initializer ABI expansion changed")
    marker = 'macro "trustIrRuntimeProviderJob"'
    require(lake_source.count(marker) == 1, "native provider job macro missing or duplicated")
    expansion = marker + lake_source.split(marker, 1)[1].split("\n\n", 1)[0]
    require(hashlib.sha256(expansion.encode()).hexdigest() ==
            "3db083a66aa600ad698054a154ca55c93cd25e56d11bd3e18d3b1a1f4b47671e", "native provider job expansion changed")
    require('module_facet trustirRuntimeProvider (_mod) : System.FilePath :=\n  trustIrRuntimeProviderJob' in lake_source,
            "native provider facet bypasses its reviewed dependency closure")
    require('moreLeancArgs := if Lean.versionString == "4.30.0-rc2" then\n    #["-include", (__dir__ / "native" / "runtime_ffi.h").toString] else #[]' in lake_source,
            "modern native provider ABI header is not configured")
    marker = 'macro "trustIrFfiOJob "'
    require(lake_source.count(marker) == 1, "native object job macro missing or duplicated")
    expansion = marker + lake_source.split(marker, 1)[1].split("\n\n", 1)[0]
    require(hashlib.sha256(expansion.encode()).hexdigest() ==
            "73ed949c58276014c76e8bfc6d00e244a4077405e988fa7be09c31f43e89d358", "native object job expansion changed")
    marker = 'macro "trustIrNativeObjects"'
    require(lake_source.count(marker) == 1, "native object selection macro missing or duplicated")
    expansion = marker + lake_source.split(marker, 1)[1].split("\n\n", 1)[0]
    require(hashlib.sha256(expansion.encode()).hexdigest() ==
            "d9d4d4ff4a2fe96d6138f1dc5c6f6ad442c9ea85b95bdeecaa7545af394dcae2", "native object selection expansion changed")
    marker = 'def trustIrProviderRoots : Array Lean.Name :='
    require(lake_source.count(marker) == 1, "native foundation ownership policy missing or duplicated")
    expansion = marker + lake_source.split(marker, 1)[1].split("\n\n", 1)[0]
    require(hashlib.sha256(expansion.encode()).hexdigest() ==
            "75a3080780714df6da7a0788e1df733a92e60d604bf0fc08c23cd4f95bf9e6d1", "native foundation ownership policy changed")
    marker = 'def trustIrProviderFoundations : Array Lean.Name :='
    require(lake_source.count(marker) == 1, "native foundation roster missing or duplicated")
    expansion = marker + lake_source.split(marker, 1)[1].split("\n\n", 1)[0]
    roster = re.fullmatch(r"\s*#\[(.*)\]", expansion[len(marker):], re.DOTALL)
    require(roster is not None, "native foundation roster is not a literal name array")
    entries = [entry.strip() for entry in roster[1].split(",")]
    require(all(re.fullmatch(r"`TrustIr\.[A-Za-z0-9_.]+", entry) for entry in entries),
            "native foundation roster contains a nonliteral module")
    require(sorted(entry[1:] for entry in entries) == foundations,
            "native foundation ownership differs from the provider import closure")
    require(hashlib.sha256(expansion.encode()).hexdigest() ==
            "681cf09ec38f074e3b4786cd9d9c694d65137d8d88c7c5937d751b73a7f6a3f1", "native foundation roster changed")
    libraries = dict(re.findall(r"lean_lib (\w+) where([\s\S]*?)(?=\n(?:@\[|module_facet|lean_(?:lib|exe))|\Z)", comments_removed(lake_source)))
    require(set(libraries) == {"TrustIrNativeLink", "TrustIr", "TrustIrRuntime", "TrustIrEval", "TrustIrLookupTools", "TrustIrDecodedCFGTools", "TrustIrCFGMappingTools"},
            "native library header policy census changed")
    require("roots := trustIrProviderRoots" in libraries["TrustIrRuntime"]
            and lake_source.index("lean_lib TrustIrRuntime where") > lake_source.index("lean_lib TrustIr where"),
            "native provider requires its reviewed foundation ownership")
    for name in ("TrustIr", "TrustIrRuntime", "TrustIrEval", "TrustIrLookupTools", "TrustIrDecodedCFGTools", "TrustIrCFGMappingTools"):
        require("nativeFacets := trustIrNativeObjects" in libraries[name],
                "native objects require their header dependency")
    lake = comments_removed(lake_source)
    lake = re.sub(r"trustIrNativeFacet\s+(\w+)", r"`\1", lake)
    link_config = re.search(r"lean_lib TrustIrNativeLink where([\s\S]*?)(?=\n(?:@\[|module_facet|lean_(?:lib|exe))|\Z)", lake)
    require(link_config is not None and "precompileModules := true" in link_config[1]
            and "nativeFacets := fun shouldExport =>" in link_config[1]
            and "if shouldExport then #[`trustirRuntimeInit, `trustirRuntimeProvider]" in link_config[1]
            and "else #[`trustirRuntimeInit]" in link_config[1]
            and '"-DLEAN_EXPORTING"' in lake,
            "native attachment requires its exported initializer and provider facets")
    roots = re.findall(r"lean_exe\s+\w+\s+where\s+root\s*:=\s*`([\w.]+)", lake)
    execution_roots = set()
    for path in producer.rglob("*.lean"):
        if ".lake" in path.relative_to(producer).parts:
            continue
        if re.search(r"(?m)^(?:(?:unsafe|partial) )?def main\b", comments_removed(path.read_text())):
            execution_roots.add(path.relative_to(producer).with_suffix("").as_posix().replace("/", "."))
    require(len(set(ledger["runtime_import_roots"])) == len(ledger["runtime_import_roots"])
            and set(roots) <= execution_roots
            and execution_roots == set(ledger["runtime_import_roots"]),
            "runtime executable/direct-run root census changed")
    runtime_config = re.search(r"lean_lib TrustIrRuntime where([\s\S]*?)(?=\nlean_(?:lib|exe)|\Z)", lake)
    require(runtime_config is not None and "precompileModules := false" in runtime_config[1],
            "runtime library must load through the complete native attachment")
    for module in ledger["runtime_import_roots"]:
        path = producer / (module.replace(".", "/") + ".lean")
        require(imports(path.read_text()).count("TrustIrRuntime") == 1,
                f"runtime executable root lacks one explicit complete attachment: {module}")
    require(set(imports((producer / "TrustIrRuntime.lean").read_text())) == set(modules),
            "runtime aggregate import set is incomplete")
    for relative in CALLER_INPUTS:
        path = root / relative
        require(not path.is_symlink(), "execution caller source must be an owned regular input")
        sources[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
    return {"schema": 2, "scope": "source boundary/identity inventory only; no kernel or runtime proof verdict",
            "baseline_count_scope": "imported_restored_declarations",
            "baseline_total": total, "baseline_logical_safe": logical, "runtime_open": count,
            "interfaces_open": interfaces_count, "support_open": len(support), "source_inputs": dict(sorted(sources.items())),
            "logical_import_modules": sorted(seen), "runtime_modules": sorted(modules)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path)
    parser.add_argument("--against", type=Path, help="refuse any source-input difference from this prior inventory")
    args = parser.parse_args()
    try:
        result = inspect(args.root)
        if args.against:
            prior = json.loads(args.against.read_text())
            require(prior.get("schema") == 2 and prior.get("source_inputs") == result["source_inputs"],
                    "source inputs differ from the bound runtime inventory")
        data = json.dumps(result, indent=2) + "\n"
        if args.output:
            require(not args.output.resolve().is_relative_to(args.root.resolve() / PRODUCER),
                    "inventory output must not become its own producer input")
            args.output.write_text(data)
        else:
            sys.stdout.write(data)
        return 0
    except (BoundaryError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"lean-runtime-boundary: REFUSED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
