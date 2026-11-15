#!/usr/bin/env python3
# Copyright 2026 Andrew Yates | Apache-2.0
"""Audit complete SemR replay coverage; this is not a proof checker.

Consume ExportSemR's lossless inventory and Clean's JSON plus actual process
exit. Never turn an admitted subset, partial skip, decline, or missing record
into complete acceptance. A successful audit still grants no reference-entry,
axiom-policy, native-code, or whole-toolchain authority.
"""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path

MODELS = {"SemR", "MiniRust", "SemRMiniRust", "SemRMemory"}
VERDICTS = {"admitted": "admitted", "refused": "refused",
            "budget-exhausted": "budget_exhausted", "not-replayable": "not_replayable"}


def read_json(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate JSON key: " + key)
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=unique)


def report_name(components):
    """Clean Name::to_unambiguous_string, over typed Lean name components."""
    if not isinstance(components, list) or not components:
        raise ValueError("declaration has no structured name")
    out = []
    for component in components:
        if not isinstance(component, dict) or len(component) != 1:
            raise ValueError("invalid name component")
        if "num" in component:
            n = component["num"]
            if type(n) is not int or not 0 <= n <= 0xffffffffffffffff:
                raise ValueError("invalid numeric name component")
            out.append(str(n))
        elif "str" in component and isinstance(component["str"], str):
            s = component["str"]
            plain = (bool(s) and not all('0' <= c <= '9' for c in s)
                     and not s.startswith('[')
                     and all(33 <= ord(c) <= 126 and c not in '.\\' for c in s))
            if plain:
                out.append(s)
            else:
                escaped = ''.join('\\\\' if c == '\\' else c if 32 <= ord(c) <= 126
                                  else '\\u{' + format(ord(c), 'x') + '}' for c in s)
                out.append('«' + escaped + '»')
        else:
            raise ValueError("invalid string name component")
    return '.'.join(out)


def audit(inventory, report, process_exit):
    if (not isinstance(inventory, dict) or type(inventory.get("schema")) is not int
            or inventory["schema"] != 2):
        raise ValueError("lossless inventory schema 2 required")
    constants = inventory.get("constants")
    if not isinstance(constants, list) or not constants:
        raise ValueError("empty or missing inventory")
    expected, unsafe, seen = {}, set(), set()
    for row in constants:
        name = report_name(row["components"])
        if name in seen:
            raise ValueError("duplicate inventory identity: " + name)
        seen.add(name)
        if not isinstance(row.get("module"), str) or not row["module"]:
            raise ValueError("missing module owner: " + name)
        if any(type(row.get(k)) is not bool for k in ("unsafe", "partial")):
            raise ValueError("invalid safety flags: " + name)
        if row["unsafe"]:
            unsafe.add(name)
        else:
            expected[name] = row
    if {row["module"] for row in expected.values()} & MODELS != MODELS:
        raise ValueError("inventory does not cover all four model modules")
    if not isinstance(report, dict) or not isinstance(report.get("records"), list):
        raise ValueError("missing checker records")
    records, counts, by_module = {}, Counter(), defaultdict(Counter)
    partial_mismatches = []
    for row in report["records"]:
        name, verdict = row["name"], row["verdict"]
        if name in records:
            raise ValueError("duplicate checker identity: " + name)
        if name not in expected:
            raise ValueError("unexpected checker identity: " + name)
        if verdict not in VERDICTS:
            raise ValueError("unknown checker verdict: " + str(verdict))
        records[name] = row
        counts[verdict] += 1
        by_module[expected[name]["module"]][verdict] += 1
        if expected[name]["partial"] != (verdict == "not-replayable"):
            partial_mismatches.append(name)
    missing = sorted(expected.keys() - records.keys())
    problems = []
    if missing:
        problems.append(f"{len(missing)} safe declarations missing checker records")
    if partial_mismatches:
        problems.append("partial disposition disagrees with inventory")
    for verdict, field in VERDICTS.items():
        if type(report.get(field)) is not int or report[field] != counts[verdict]:
            problems.append("checker count disagrees with records: " + field)
    if type(report.get("declarations")) is not int or report["declarations"] != len(records):
        problems.append("checker declaration count disagrees with records")
    exits = {0: "accept", 1: "reject", 2: "decline"}
    if type(process_exit) is not int or process_exit not in exits:
        problems.append("checker did not exit with a replay verdict")
    if (type(report.get("exit_code")) is not int or report["exit_code"] != process_exit
            or report.get("exit") != exits.get(process_exit)):
        problems.append("process and reported exit disagree")
    if process_exit != 0:
        problems.append("checker did not accept the export")
    if any(counts[v] for v in VERDICTS if v != "admitted"):
        problems.append("export has refused, exhausted or skipped declarations")
    if report.get("reader_error") is not None or report.get("decline_reason") is not None:
        problems.append("checker reports a reader error or decline")
    if not records:
        problems.append("empty replay")
    return {"schema": 1, "complete_replay_report": not problems,
            "proof_authority": "none: evidence audit only",
            "problems": problems, "missing": missing,
            "inventory_constants": len(constants), "unsafe_excluded": len(unsafe),
            "safe_expected": len(expected), "records": len(records),
            "verdicts": dict(counts), "by_module": {k: dict(v) for k, v in sorted(by_module.items())},
            "partial_mismatches": partial_mismatches}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--process-exit", required=True, type=int)
    args = parser.parse_args()
    try:
        result = audit(read_json(args.inventory), read_json(args.report), args.process_exit)
    except (ValueError, KeyError, TypeError, OSError) as error:
        result = {"complete_replay_report": False, "error": str(error)}
    print(json.dumps(result, indent=2))
    return 0 if result["complete_replay_report"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
