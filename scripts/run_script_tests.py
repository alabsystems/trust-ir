#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Run each script test file in its own process and report actual test results."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve()
TESTS = SCRIPT.parent / "tests"
COUNTS = ("discovered_tests", "tests_run", "executed", "passed", "skipped",
          "partially_skipped_cases", "skipped_subtests", "skipped_fixtures",
          "subtests_executed", "subtests_passed", "expected_failures",
          "unexpected_successes", "failures", "errors")


class RecordingResult(unittest.TextTestResult):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.passed = 0
        self.active_test = None
        self.skip_reasons = []
        self.skip_counts = {"case": 0, "subtest": 0, "fixture": 0}
        self.partially_skipped_cases = 0
        self.subtests_executed = 0
        self.subtests_passed = 0

    def case_outcomes(self):
        return (self.passed, len(self.failures), len(self.errors),
                len(self.expectedFailures), len(self.unexpectedSuccesses),
                self.skip_counts["case"])

    def startTest(self, test):
        super().startTest(test)
        self.active_test = test
        self.case_baseline = self.case_outcomes()
        self.subskip_baseline = self.skip_counts["subtest"]

    def stopTest(self, test):
        if (self.case_outcomes() == self.case_baseline
                and self.skip_counts["subtest"] > self.subskip_baseline):
            self.partially_skipped_cases += 1
        super().stopTest(test)
        self.active_test = None

    def addSuccess(self, test):
        super().addSuccess(test)
        self.passed += 1

    def addSkip(self, test, reason):
        super().addSkip(test, reason)
        kind = ("case" if test is self.active_test else
                "fixture" if self.active_test is None else "subtest")
        self.skip_counts[kind] += 1
        self.skip_reasons.append({"test": test.id(), "reason": str(reason), "kind": kind})

    def addSubTest(self, test, subtest, error):
        super().addSubTest(test, subtest, error)
        self.subtests_executed += 1
        self.subtests_passed += error is None


def completed_outcomes(data):
    return data["passed"] + data["expected_failures"] + data["subtests_passed"]


def run_child(test_file: Path, result_file: Path) -> int:
    if test_file.resolve().parent != TESTS or not test_file.is_file():
        raise ValueError("test file must be in scripts/tests")
    # Running this file by its absolute path puts scripts/, rather than the
    # repository, on sys.path. Preserve ordinary `from scripts import ...`
    # imports in each isolated test process without an ambient PYTHONPATH.
    sys.path.insert(0, str(SCRIPT.parent.parent))
    suite = unittest.defaultTestLoader.discover(str(TESTS), pattern=test_file.name)
    discovered = suite.countTestCases()
    result = unittest.TextTestRunner(verbosity=2, resultclass=RecordingResult).run(suite)
    skips = {kind: sum(row["kind"] == kind for row in result.skip_reasons)
             for kind in ("case", "subtest", "fixture")}
    payload = {
        "schema": 1, "file": test_file.name, "pid": os.getpid(),
        "discovered_tests": discovered,
        "tests_run": result.testsRun, "executed": result.testsRun - skips["case"],
        "passed": result.passed, "skipped": skips["case"],
        "skipped_subtests": skips["subtest"], "skipped_fixtures": skips["fixture"],
        "partially_skipped_cases": result.partially_skipped_cases,
        "subtests_executed": result.subtests_executed, "subtests_passed": result.subtests_passed,
        "expected_failures": len(result.expectedFailures),
        "unexpected_successes": len(result.unexpectedSuccesses),
        "failures": len(result.failures), "errors": len(result.errors),
        "successful": result.wasSuccessful(),
        "skip_reasons": result.skip_reasons,
    }
    with result_file.open("x", encoding="utf-8") as output:
        json.dump(payload, output)
        output.write("\n")
    return 0 if payload["successful"] and payload["executed"] > 0 and completed_outcomes(payload) > 0 else 1


def run_file(test_file: Path, logs: Path) -> tuple[dict, str]:
    result_file = logs / (test_file.name + ".json")
    log_file = logs / (test_file.name + ".log")
    with log_file.open("w", encoding="utf-8") as output:
        process = subprocess.run(
            [sys.executable, "-B", str(SCRIPT), "--test-file", str(test_file),
             "--result", str(result_file)],
            stdout=output, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
        )
    text = log_file.read_text(encoding="utf-8", errors="replace")
    try:
        data = json.loads(result_file.read_text(encoding="utf-8"))
        if not isinstance(data, dict) or data.get("schema") != 1 or data.get("file") != test_file.name:
            raise ValueError("wrong result identity")
        if any(type(data.get(key)) is not int or data[key] < 0 for key in COUNTS):
            raise ValueError("invalid result counters")
        reasons = data.get("skip_reasons")
        if not isinstance(reasons, list):
            raise ValueError("invalid skip results")
        if any(not isinstance(row, dict) or not isinstance(row.get("test"), str)
               or not isinstance(row.get("reason"), str)
               or row.get("kind") not in ("case", "subtest", "fixture") for row in reasons):
            raise ValueError("invalid skip details")
        for kind, counter in (("case", "skipped"), ("subtest", "skipped_subtests"),
                              ("fixture", "skipped_fixtures")):
            if sum(row["kind"] == kind for row in reasons) != data[counter]:
                raise ValueError("inconsistent skip count")
        if type(data.get("successful")) is not bool:
            raise ValueError("missing unittest outcome")
        if data["executed"] != data["tests_run"] - data["skipped"]:
            raise ValueError("inconsistent execution count")
        if data["tests_run"] > data["discovered_tests"]:
            raise ValueError("execution exceeds discovery")
        if data["subtests_passed"] > data["subtests_executed"]:
            raise ValueError("successful subtests exceed execution")
        if data["successful"] and (
            data["passed"] + data["skipped"] + data["partially_skipped_cases"]
            + data["expected_failures"] != data["tests_run"]
            or data["failures"] or data["errors"] or data["unexpected_successes"]
        ):
            raise ValueError("inconsistent successful result")
    except (OSError, ValueError, TypeError) as error:
        return {
            "file": test_file.name, "reported": False, "ok": False,
            "error": f"missing or invalid test result: {error}; child exit={process.returncode}",
        }, text
    data.update(reported=True, ok=process.returncode == 0 and data["successful"]
                and data["executed"] > 0 and completed_outcomes(data) > 0)
    if not data["ok"]:
        data["error"] = ("no tests executed" if data["executed"] == 0 else
                         "no tests completed" if completed_outcomes(data) == 0 else
                         f"child exit={process.returncode}")
    return data, text


def run_all() -> dict:
    files = sorted(TESTS.glob("test_*.py"))
    if not files:
        return {"schema": 1, "ok": False, "error": "no scripts/tests/test_*.py files found",
                "discovered_files": 0, "reported_files": 0, "files": [],
                "totals": {key: 0 for key in COUNTS}}
    outcomes = []
    with tempfile.TemporaryDirectory(prefix="script-test-results-") as directory:
        with ThreadPoolExecutor(max_workers=len(files)) as pool:
            pending = [pool.submit(run_file, path, Path(directory)) for path in files]
            for path, future in zip(files, pending):
                data, text = future.result()
                outcomes.append(data)
                if data["reported"]:
                    print(f'{path.name}: {data["discovered_tests"]} discovered, '
                          f'{data["tests_run"]} run, {data["executed"]} executed, '
                          f'{data["passed"]} passed, {data["skipped"]} skipped, '
                          f'{data["partially_skipped_cases"]} partially skipped cases, '
                          f'{data["skipped_subtests"]} skipped subtests, '
                          f'{data["skipped_fixtures"]} skipped fixtures, '
                          f'{data["subtests_passed"]}/{data["subtests_executed"]} subtests passed, '
                          f'{data["expected_failures"]} expected failures', flush=True)
                    for skip in data["skip_reasons"]:
                        print(f'{path.name}: SKIP {skip["test"]}: {skip["reason"]}', flush=True)
                if not data["ok"]:
                    print(f'{path.name} FAILED: {data.get("error", "test failure")}', file=sys.stderr)
                    print(text, end="" if text.endswith("\n") else "\n", file=sys.stderr)
    totals = {key: sum(row.get(key, 0) for row in outcomes if row["reported"]) for key in COUNTS}
    return {"schema": 1, "ok": all(row["ok"] for row in outcomes),
            "discovered_files": len(files), "reported_files": sum(row["reported"] for row in outcomes),
            "files": outcomes, "totals": totals}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write a new structured result file")
    parser.add_argument("--test-file", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--result", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.test_file is not None or args.result is not None:
        if args.test_file is None or args.result is None or args.json is not None:
            parser.error("child mode requires --test-file and --result only")
        return run_child(args.test_file, args.result)
    if args.json is not None and args.json.exists():
        parser.error("structured result already exists")
    report = run_all()
    if report.get("error"):
        print(report["error"], file=sys.stderr)
    totals = report["totals"]
    print(f'TOTAL: {totals["discovered_tests"]} discovered, '
          f'{totals["tests_run"]} run, {totals["executed"]} executed, '
          f'{totals["passed"]} passed, {totals["skipped"]} skipped, '
          f'{totals["partially_skipped_cases"]} partially skipped cases, '
          f'{totals["skipped_subtests"]} skipped subtests, '
          f'{totals["skipped_fixtures"]} skipped fixtures, '
          f'{totals["subtests_passed"]}/{totals["subtests_executed"]} subtests passed, '
          f'{totals["expected_failures"]} expected failures; '
          f'{report["reported_files"]}/{report["discovered_files"]} files reported')
    if args.json is not None:
        with args.json.open("x", encoding="utf-8") as output:
            json.dump(report, output, indent=2)
            output.write("\n")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
