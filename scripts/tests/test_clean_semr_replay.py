"""Coverage and verdict controls; these do not simulate a proof checker."""
import copy
import json
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest

from scripts import audit_clean_semr_replay as replay


class ReplayAuditTests(unittest.TestCase):
    def fixture(self):
        constants = [{"components": [{"str": m}, {"str": "test"}],
                      "module": m, "unsafe": False, "partial": False}
                     for m in sorted(replay.MODELS)]
        records = [{"name": replay.report_name(x["components"]), "verdict": "admitted"}
                   for x in constants]
        return ({"schema": 2, "constants": constants},
                {"exit": "accept", "exit_code": 0, "records": records,
                 "admitted": 4, "refused": 0, "budget_exhausted": 0,
                 "not_replayable": 0, "declarations": 4})

    def test_complete_report_is_only_evidence_audit(self):
        i, r = self.fixture()
        a = replay.audit(i, r, 0)
        self.assertTrue(a["complete_replay_report"])
        self.assertIn("none", a["proof_authority"])

    def test_omission_is_rejected_even_with_consistent_smaller_counts(self):
        i, r = self.fixture()
        r["records"].pop(); r["admitted"] = r["declarations"] = 3
        self.assertFalse(replay.audit(i, r, 0)["complete_replay_report"])

    def test_admitted_model_subset_does_not_hide_refused_import(self):
        i, r = self.fixture()
        i["constants"].append({"components": [{"str": "Init"}, {"str": "bad"}],
                               "module": "Init", "unsafe": False, "partial": False})
        r["records"].append({"name": "Init.bad", "verdict": "refused"})
        r.update(exit="reject", exit_code=1, declarations=5, refused=1)
        self.assertFalse(replay.audit(i, r, 1)["complete_replay_report"])

    def test_skip_exhaustion_and_decline_never_pass(self):
        for verdict in ("not-replayable", "budget-exhausted"):
            with self.subTest(verdict=verdict):
                i, r = self.fixture()
                r["records"][0]["verdict"] = verdict
                i["constants"][0]["partial"] = verdict == "not-replayable"
                r.update(exit="decline", exit_code=2, admitted=3)
                r[replay.VERDICTS[verdict]] = 1
                self.assertFalse(replay.audit(i, r, 2)["complete_replay_report"])

    def test_duplicate_and_foreign_records_refuse(self):
        i, r = self.fixture()
        r["records"].append(copy.deepcopy(r["records"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate checker"):
            replay.audit(i, r, 0)
        r["records"][-1]["name"] = "Foreign.declaration"
        with self.assertRaisesRegex(ValueError, "unexpected checker"):
            replay.audit(i, r, 0)

    def test_duplicate_inventory_and_missing_model_refuse(self):
        i, r = self.fixture()
        i["constants"].append(copy.deepcopy(i["constants"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate inventory"):
            replay.audit(i, r, 0)
        i["constants"] = i["constants"][:3]
        with self.assertRaisesRegex(ValueError, "all four"):
            replay.audit(i, r, 0)

    def test_process_exit_cannot_be_overridden_by_report(self):
        i, r = self.fixture()
        for exit_code in (1, 2, 137, True):
            self.assertFalse(replay.audit(i, r, exit_code)["complete_replay_report"])

    def test_counts_reader_errors_and_false_partial_admission_refuse(self):
        i, r = self.fixture()
        for field, value in (("admitted", 3), ("declarations", 5),
                             ("reader_error", {"rule": "broken"}),
                             ("decline_reason", "unsupported world")):
            bad = copy.deepcopy(r); bad[field] = value
            self.assertFalse(replay.audit(i, bad, 0)["complete_replay_report"])
        i["constants"][0]["partial"] = True
        self.assertFalse(replay.audit(i, r, 0)["complete_replay_report"])

    def test_unsafe_exclusion_is_explicit_and_never_replayed(self):
        i, r = self.fixture()
        i["constants"].append({"components": [{"str": "Unsafe"}], "module": "Init",
                               "unsafe": True, "partial": False})
        self.assertEqual(replay.audit(i, r, 0)["unsafe_excluded"], 1)
        r["records"].append({"name": "Unsafe", "verdict": "admitted"})
        with self.assertRaisesRegex(ValueError, "unexpected checker"):
            replay.audit(i, r, 0)

    def test_names_preserve_components_unicode_and_numeric_identity(self):
        cases = [([{"str": "a.b"}], "«a.b»"),
                 ([{"str": "a"}, {"str": "b"}], "a.b"),
                 ([{"str": "12"}], "«12»"), ([{"num": 12}], "12"),
                 ([{"str": "α"}], "«\\u{3b1}»"),
                 ([{"str": r"\u{3b1}"}], "«\\\\u{3b1}»"),
                 ([{"str": "».«"}], "«\\u{bb}.\\u{ab}»"),
                 ([{"str": ""}, {"str": ""}], "«».«»")]
        self.assertEqual(len({replay.report_name(parts) for parts, _ in cases}), len(cases))
        for parts, expected in cases:
            self.assertEqual(replay.report_name(parts), expected)
        for parts in ([], [{"num": True}], [{"num": -1}], [{"str": "x", "num": 1}]):
            with self.assertRaises(ValueError):
                replay.report_name(parts)

    def test_lossy_old_inventory_and_duplicate_json_keys_refuse(self):
        i, r = self.fixture(); i.pop("schema")
        with self.assertRaisesRegex(ValueError, "schema 2"):
            replay.audit(i, r, 0)
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / "input.json"; p.write_text('{"schema":2,"schema":1}')
            with self.assertRaisesRegex(ValueError, "duplicate JSON"):
                replay.read_json(p)

    def test_cli_missing_record_exits_nonzero_with_consistent_report_counts(self):
        i, r = self.fixture()
        r["records"].pop(); r["admitted"] = r["declarations"] = 3
        with tempfile.TemporaryDirectory() as directory:
            inventory, report = Path(directory) / "inventory.json", Path(directory) / "report.json"
            inventory.write_text(json.dumps(i)); report.write_text(json.dumps(r))
            result = subprocess.run([sys.executable, str(Path(replay.__file__)),
                                     "--inventory", str(inventory), "--report", str(report),
                                     "--process-exit", "0"], capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)
            self.assertEqual(len(json.loads(result.stdout)["missing"]), 1)


if __name__ == "__main__":
    unittest.main()
