"""Required-corpus and feature-forwarding regressions for the stage test runner."""

import importlib.util
from pathlib import Path
import tempfile
import tomllib
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "test_source_value_stage.py"
SPEC = importlib.util.spec_from_file_location("source_value_stage", SCRIPT)
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)


def transcript(subject, count, *, ignored=0, filtered=0):
    lines = [f"     Running {subject}.rs (/owned/{subject})"]
    lines += [f"test {subject}::case_{i} ... ok" for i in range(count)]
    lines += [
        f"test result: ok. {count} passed; 0 failed; {ignored} ignored; "
        f"0 measured; {filtered} filtered out; finished in 0.01s"
    ]
    return "\n".join(lines) + "\n"


class SourceValueStageTest(unittest.TestCase):
    def test_complete_named_targets_are_required(self):
        text = transcript(RUNNER.SUBJECTS[0], 7) + transcript(RUNNER.SUBJECTS[1], 10)
        observed = RUNNER.required_test_inventory(text)
        self.assertEqual({name: row["passed"] for name, row in observed.items()},
                         dict(zip(RUNNER.SUBJECTS, (7, 10))))
        self.assertEqual(len(observed[RUNNER.SUBJECTS[1]]["names"]), 10)

    def test_zero_tests_or_swapped_counts_do_not_pass(self):
        for counts in [(0, 0), (10, 7), (7, 9)]:
            with self.subTest(counts=counts), self.assertRaises(ValueError):
                RUNNER.required_test_inventory("".join(
                    transcript(name, count) for name, count in zip(RUNNER.SUBJECTS, counts)
                ))

    def test_wrong_targets_ignored_and_filtered_cases_refuse(self):
        for first in [transcript("another_target", 7),
                      transcript(RUNNER.SUBJECTS[0], 7, ignored=1),
                      transcript(RUNNER.SUBJECTS[0], 7, filtered=1)]:
            with self.subTest(first=first), self.assertRaises(ValueError):
                RUNNER.required_test_inventory(first + transcript(RUNNER.SUBJECTS[1], 10))

    def test_feature_forwarding_preserves_the_real_checker_guard(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            harness = root / "ir/crates/trust-ir-build/tests/stage_source_value_equation"
            harness.mkdir(parents=True)
            (root / "ir/crates/trust-ir").mkdir()
            source = SCRIPT.parents[1] / RUNNER.HARNESS / "Cargo.toml"
            (harness / "Cargo.toml").write_bytes(source.read_bytes())
            kernel = root / "trust/first-party/clean/crates/clean-kernel"
            kernel.mkdir(parents=True)
            stage = {"workspace": {"dependencies": {"clean-kernel": {
                "path": "first-party/clean/crates/clean-kernel", "features": ["math-overlays"]
            }}}}
            text, selected = RUNNER.integration_manifest(harness, root / "trust", stage)
            generated = tomllib.loads(text)
            self.assertEqual(selected, kernel.resolve())
            self.assertEqual(generated["features"]["default"], ["clean-tv-anchor"])
            self.assertEqual(generated["features"]["clean-tv-anchor"],
                             ["trust-ir-build/clean-tv-anchor"])
            self.assertFalse(generated["dependencies"]["trust-ir-build"]["default-features"])
            self.assertEqual(generated["dependencies"]["clean-kernel"]["features"],
                             ["math-overlays"])


if __name__ == "__main__":
    unittest.main()
