# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The script gate must distinguish execution from discovery and skipped work."""

import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


SCRIPTS = Path(__file__).resolve().parents[1]
PASS = "import unittest\nclass Fixture(unittest.TestCase):\n    def test_ok(self): self.assertTrue(True)\n"


class ScriptTestRunner(unittest.TestCase):
    def invoke(self, files, prior_report=None):
        temporary = tempfile.TemporaryDirectory(prefix="script gate fixture ")
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        scripts = root / "scripts"
        tests = scripts / "tests"
        tests.mkdir(parents=True)
        for name in ("run_script_tests.sh", "run_script_tests.py"):
            shutil.copyfile(SCRIPTS / name, scripts / name)
        for name, content in files.items():
            (tests / name).write_text(content, encoding="utf-8")
        report = root / "results.json"
        if prior_report is not None:
            report.write_text(json.dumps(prior_report), encoding="utf-8")
        process = subprocess.run(
            ["bash", str(scripts / "run_script_tests.sh"), "--json", str(report)],
            capture_output=True, text=True, timeout=45,
        )
        data = json.loads(report.read_text()) if report.exists() else None
        return process, data

    def test_a_real_pass_reports_execution(self):
        process, data = self.invoke({"test_one.py": PASS})
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertTrue(data["ok"])
        self.assertEqual(data["totals"]["tests_run"], 1)
        self.assertEqual(data["totals"]["executed"], 1)
        self.assertEqual(data["totals"]["passed"], 1)
        self.assertEqual(data["totals"]["skipped"], 0)

    def test_partial_skips_are_named_and_not_counted_as_passes(self):
        content = PASS + "    @unittest.skip('fixture unavailable')\n    def test_skip(self): pass\n"
        process, data = self.invoke({"test_one.py": content})
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(data["totals"]["tests_run"], 2)
        self.assertEqual(data["totals"]["executed"], 1)
        self.assertEqual(data["totals"]["passed"], 1)
        self.assertEqual(data["totals"]["skipped"], 1)
        self.assertIn("SKIP test_one.Fixture.test_skip: fixture unavailable", process.stdout)

    def test_an_entirely_skipped_file_is_not_an_executed_gate(self):
        content = "import unittest\n@unittest.skip('no input')\nclass Fixture(unittest.TestCase):\n    def test_skip(self): pass\n"
        process, data = self.invoke({"test_one.py": content})
        self.assertNotEqual(process.returncode, 0)
        self.assertFalse(data["ok"])
        self.assertEqual(data["totals"]["executed"], 0)
        self.assertIn("no tests executed", process.stderr)

    def test_a_failure_does_not_hide_other_files(self):
        failure = PASS.replace("self.assertTrue(True)", "self.fail('intentional failure')")
        process, data = self.invoke({"test_failure.py": failure, "test_success.py": PASS})
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(data["reported_files"], 2)
        self.assertEqual(data["totals"]["passed"], 1)
        self.assertEqual(data["totals"]["failures"], 1)
        self.assertIn("intentional failure", process.stderr)

    def test_no_matching_files_refuses(self):
        process, data = self.invoke({})
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(data["discovered_files"], 0)
        self.assertIn("no scripts/tests/test_*.py files found", process.stderr)

    def test_a_file_with_no_tests_refuses(self):
        process, data = self.invoke({"test_empty.py": "import unittest\n"})
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(data["totals"]["tests_run"], 0)
        self.assertIn("no tests executed", process.stderr)

    def test_successful_process_exit_without_a_result_refuses(self):
        process, data = self.invoke({"test_exit.py": "import os\nos._exit(0)\n"})
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(data["reported_files"], 0)
        self.assertIn("missing or invalid test result", process.stderr)

    def test_successful_process_exit_with_a_corrupt_result_refuses(self):
        content = (
            "import os, sys\nfrom pathlib import Path\n"
            "Path(sys.argv[sys.argv.index('--result') + 1]).write_text('not JSON')\n"
            "os._exit(0)\n"
        )
        process, data = self.invoke({"test_corrupt.py": content})
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(data["reported_files"], 0)
        self.assertIn("missing or invalid test result", process.stderr)

    def test_printed_summaries_do_not_inflate_counts(self):
        content = PASS.replace("self.assertTrue(True)", "print('Ran 999999 tests in 0s\\n\\nOK')")
        process, data = self.invoke({"test_one.py": content})
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(data["totals"]["tests_run"], 1)
        self.assertEqual(data["totals"]["passed"], 1)

    def test_files_retain_process_isolation(self):
        first = PASS.replace("self.assertTrue(True)", "__import__('os').environ['SCRIPT_GATE_LEAK'] = 'yes'")
        second = PASS.replace("self.assertTrue(True)", "self.assertNotIn('SCRIPT_GATE_LEAK', __import__('os').environ)")
        process, data = self.invoke({"test_first.py": first, "test_second.py": second})
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(len({row["pid"] for row in data["files"]}), 2)

    def test_expected_failures_remain_distinct_from_passes(self):
        content = PASS + "    @unittest.expectedFailure\n    def test_expected(self): self.fail('known fixture')\n"
        process, data = self.invoke({"test_one.py": content})
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(data["totals"]["executed"], 2)
        self.assertEqual(data["totals"]["passed"], 1)
        self.assertEqual(data["totals"]["expected_failures"], 1)

    def test_an_unexpected_success_is_not_a_pass(self):
        content = PASS.replace("    def test_ok", "    @unittest.expectedFailure\n    def test_ok")
        process, data = self.invoke({"test_one.py": content})
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(data["totals"]["passed"], 0)
        self.assertEqual(data["totals"]["unexpected_successes"], 1)

    def test_a_previous_report_is_not_overwritten(self):
        previous = {"immutable": "previous result"}
        process, data = self.invoke({"test_one.py": PASS}, prior_report=previous)
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(data, previous)
        self.assertIn("already exists", process.stderr)

    def test_subtest_skips_do_not_erase_an_executed_case(self):
        content = (
            "import unittest\nclass Fixture(unittest.TestCase):\n"
            "    def test_case(self):\n"
            "        with self.subTest(name='absent'):\n"
            "            self.skipTest('missing subcase')\n"
            "        with self.subTest(name='present'):\n"
            "            self.assertTrue(True)\n"
        )
        process, data = self.invoke({"test_one.py": content})
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(data["totals"]["tests_run"], 1)
        self.assertEqual(data["totals"]["executed"], 1)
        self.assertEqual(data["totals"]["passed"], 0)
        self.assertEqual(data["totals"]["partially_skipped_cases"], 1)
        self.assertEqual(data["totals"]["subtests_passed"], 1)
        self.assertEqual(data["totals"]["skipped"], 0)
        self.assertEqual(data["totals"]["skipped_subtests"], 1)
        self.assertIn("missing subcase", process.stdout)

    def test_all_skipped_subtests_are_not_completed_results(self):
        content = (
            "import unittest\nclass Fixture(unittest.TestCase):\n"
            "    def test_case(self):\n"
            "        for value in range(2):\n"
            "            with self.subTest(value=value):\n"
            "                self.skipTest('missing subcase')\n"
        )
        process, data = self.invoke({"test_one.py": content})
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(data["totals"]["executed"], 1)
        self.assertEqual(data["totals"]["passed"], 0)
        self.assertEqual(data["totals"]["partially_skipped_cases"], 1)
        self.assertEqual(data["totals"]["skipped_subtests"], 2)
        self.assertEqual(data["totals"]["subtests_passed"], 0)
        self.assertIn("no tests completed", process.stderr)

    def test_a_skipped_class_fixture_does_not_claim_discovered_tests_ran(self):
        content = (
            "import unittest\nclass Fixture(unittest.TestCase):\n"
            "    @classmethod\n"
            "    def setUpClass(cls): raise unittest.SkipTest('no class fixture')\n"
            "    def test_one(self): pass\n"
            "    def test_two(self): pass\n"
        )
        process, data = self.invoke({"test_one.py": content})
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(data["totals"]["discovered_tests"], 2)
        self.assertEqual(data["totals"]["tests_run"], 0)
        self.assertEqual(data["totals"]["executed"], 0)
        self.assertEqual(data["totals"]["skipped_fixtures"], 1)
        self.assertIn("no class fixture", process.stdout)

    def test_a_partial_class_fixture_skip_is_reported_separately(self):
        content = PASS + (
            "class Unavailable(unittest.TestCase):\n"
            "    @classmethod\n"
            "    def setUpClass(cls): raise unittest.SkipTest('no class fixture')\n"
            "    def test_one(self): pass\n"
            "    def test_two(self): pass\n"
        )
        process, data = self.invoke({"test_one.py": content})
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(data["totals"]["discovered_tests"], 3)
        self.assertEqual(data["totals"]["tests_run"], 1)
        self.assertEqual(data["totals"]["passed"], 1)
        self.assertEqual(data["totals"]["skipped_fixtures"], 1)


if __name__ == "__main__":
    unittest.main()
