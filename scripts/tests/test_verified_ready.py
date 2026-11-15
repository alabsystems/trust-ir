"""Guards for the verified READY lane (scripts/verified_ready.py, gate 16).

Toolchain-free: the table's grammar (a 0 floor is refused, a row names a real
crate), the committed table against the tree, and every condition of a row's
verdict over synthetic judgments — a NOT JUDGED run fails, unknown rows never
meet a floor, any refutation fails, the report's own gate is read, and gate
13's admitted law rows are never counted as proved.
"""

import sys
import unittest
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import verified_contracts as vc  # noqa: E402
import verified_ready as vr  # noqa: E402
import verified_survey as vs  # noqa: E402

HEADER = "\t".join(vr.HEADER)
ROW = vr.Row("trust-ir-fmt", "bins", 2, "measured", 3)
CLEAN_GATE = {"decision": "conditional-pass", "counts": {"proved": 3, "failed": 0, "unknown": 9}}


def result(proved=3, unknown=9, failed=0, reasons=(), refutations=(), laws=(), exit=0):
    r = vs.CrateResult("trust-ir-fmt")
    r.exit = exit
    r.statuses = Counter({"proved": proved, "unknown": unknown, "failed": failed})
    r.reasons = list(reasons)
    r.refutations = list(refutations)
    r.gate13_laws = list(laws)
    return r


class TableGrammar(unittest.TestCase):
    def test_a_good_table_parses(self):
        rows, errors = vr.parse_rows(f"# c\n{HEADER}\ntrust-ir-fmt\tbins\t2\tmeasured\ntrust-ir-laws\tlib\t8\tm\n")
        self.assertEqual(errors, [])
        self.assertEqual([r.key for r in rows], ["trust-ir-fmt.bins", "trust-ir-laws.lib"])
        self.assertEqual(rows[0].floor, 2)

    def test_a_zero_or_negative_floor_is_refused(self):
        for floor in ("0", "-1", "x", ""):
            _, errors = vr.parse_rows(f"{HEADER}\ntrust-ir-fmt\tbins\t{floor}\twhy\n")
            self.assertTrue(any("not a positive integer" in e for e in errors), (floor, errors))

    def test_bad_rows_are_refused(self):
        cases = {
            "trust-ir-fmt\ttests\t1\twhy": "target",
            "trust-ir-fmt\tbins\t1\t": "empty",
            "trust-ir-fmt\tbins\t1": "column",
            "Bad Crate\tbins\t1\twhy": "not a crate name",
        }
        for line, needle in cases.items():
            _, errors = vr.parse_rows(f"{HEADER}\n{line}\n")
            self.assertTrue(any(needle in e for e in errors), (line, errors))

    def test_a_duplicate_row_a_missing_header_and_an_empty_table_are_refused(self):
        _, errors = vr.parse_rows(f"{HEADER}\ntrust-ir-fmt\tbins\t1\tw\ntrust-ir-fmt\tbins\t2\tw\n")
        self.assertTrue(any("duplicate" in e for e in errors), errors)
        _, errors = vr.parse_rows("trust-ir-fmt\tbins\t1\tw\n")
        self.assertTrue(any("header" in e for e in errors), errors)
        _, errors = vr.parse_rows(f"# only\n{HEADER}\n")
        self.assertTrue(any("no rows" in e for e in errors), errors)

    def test_a_row_must_name_a_crate_of_the_tree(self):
        rows, errors = vr.parse_rows(f"{HEADER}\nno-such-crate\tlib\t1\tw\n")
        self.assertEqual(errors, [])
        self.assertTrue(vr.rows_against_tree(ROOT, rows))

    def test_the_committed_table_parses_and_matches_the_tree(self):
        rows, errors = vr.load_rows(ROOT)
        self.assertEqual(errors, [])
        self.assertTrue(rows)


class RowVerdict(unittest.TestCase):
    def test_a_clean_judged_run_over_its_floor_passes(self):
        v = vr.judge_row(ROW, result(proved=3), CLEAN_GATE)
        self.assertTrue(v.passed, v.failures)
        self.assertEqual((v.proved, v.unknown), (3, 9))

    def test_unknown_rows_never_meet_a_floor(self):
        v = vr.judge_row(ROW, result(proved=1, unknown=10_000), CLEAN_GATE)
        self.assertFalse(v.passed)
        self.assertTrue(any("below the floor" in f for f in v.failures), v.failures)

    def test_a_not_judged_run_fails_whatever_it_proved(self):
        v = vr.judge_row(ROW, result(proved=50, reasons=[f"{vc.NOT_JUDGED} 3 budget-attributable row(s)"]),
                         CLEAN_GATE)
        self.assertFalse(v.passed)
        self.assertTrue(any("NOT JUDGED" in f for f in v.failures), v.failures)

    def test_any_refutation_fails_failed_or_demoted(self):
        for route in (vs.REFUTED, vs.DEMOTED):
            ref = vs.Refutation(None, "f", "vc:f:0", "x", "a.rs:1:1-1:2", route)
            v = vr.judge_row(ROW, result(refutations=[ref]), CLEAN_GATE)
            self.assertFalse(v.passed, route)
            self.assertTrue(any(f"refutation ({route})" in f for f in v.failures), v.failures)

    def test_the_reports_own_gate_is_read(self):
        self.assertFalse(vr.judge_row(ROW, result(), None).passed)
        bad = {"decision": "fail", "counts": {"failed": 1}}
        v = vr.judge_row(ROW, result(), bad)
        self.assertTrue(any("decision is `fail`" in f for f in v.failures), v.failures)
        self.assertTrue(any("counts.failed = 1" in f for f in v.failures), v.failures)
        v = vr.judge_row(ROW, result(failed=1), CLEAN_GATE)
        self.assertTrue(any("failed row(s) in the primary unit" in f for f in v.failures), v.failures)

    def test_a_nonzero_or_missing_exit_fails_even_with_a_clean_report(self):
        for code in (1, 101, None):
            v = vr.judge_row(ROW, result(exit=code), CLEAN_GATE)
            self.assertFalse(v.passed, code)
            self.assertTrue(any(f"targo exited {code}" in f for f in v.failures), v.failures)

    def test_an_empty_rows_selection_is_refused_not_a_vacuous_pass(self):
        for sel in ("", ",", ",,"):
            self.assertEqual(vr.main(["--root", str(ROOT), "--rows", sel]), 2, sel)

    def test_admitted_law_rows_are_not_counted_as_proved(self):
        v = vr.judge_row(ROW, result(proved=0, laws=["law"] * 300), CLEAN_GATE)
        self.assertFalse(v.passed)
        self.assertEqual(v.laws_admitted, 300)
        self.assertEqual(v.proved, 0)


if __name__ == "__main__":
    unittest.main()
