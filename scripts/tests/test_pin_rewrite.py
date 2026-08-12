"""Unit coverage for the dependency-pin leg table and rewriter.

The failure mode this guards is a rewriter that matches ZERO occurrences and
reports success — that is how a "pure pin bump" silently moves only some legs.
Every leg therefore declares an exact match count, and the tests below prove
the count is enforced rather than advisory.
"""

from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PIN_REWRITE_PATH = ROOT / "scripts" / "pin_rewrite.py"
BUMP_SCRIPT = ROOT / "scripts" / "bump-dep-pin.sh"

SPEC = importlib.util.spec_from_file_location("pin_rewrite", PIN_REWRITE_PATH)
assert SPEC is not None and SPEC.loader is not None
PIN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PIN
SPEC.loader.exec_module(PIN)


OLD = "a" * 40
NEW = "b" * 40
OTHER = "c" * 40

CLEAN_DEP_LINE = (
    'clean-kernel = {{ version = "1.2.0", '
    'git = "https://github.com/alabsystems/clean.git", rev = "{rev}" }}\n'
)


def leg(dep: str, relpath: str) -> "PIN.Leg":
    for candidate in PIN.LEGS[dep]:
        if candidate.relpath == relpath:
            return candidate
    raise AssertionError(f"no {dep} leg for {relpath}")


class LegTableTests(unittest.TestCase):
    def test_every_leg_declares_a_named_sha_group(self) -> None:
        for dep, legs in PIN.LEGS.items():
            for candidate in legs:
                with self.subTest(dep=dep, leg=candidate.relpath):
                    self.assertIn("(?P<sha>", candidate.pattern)

    def test_rewritable_legs_declare_an_exact_count(self) -> None:
        # A rewritable leg with no expected count could silently match zero.
        for dep, legs in PIN.LEGS.items():
            for candidate in legs:
                if candidate.rewritable:
                    with self.subTest(dep=dep, leg=candidate.relpath):
                        self.assertIsNotNone(candidate.expected)

    def test_the_guard_test_is_a_leg_of_both_dependencies(self) -> None:
        for dep in ("clean", "ay"):
            paths = [candidate.relpath for candidate in PIN.LEGS[dep]]
            self.assertIn(PIN.GUARD_TEST, paths)

    def test_the_ay_provenance_constants_are_legs(self) -> None:
        # Both constants stamp AY identity into evidence; no lockfile catches
        # a stale string literal after the dependency itself moves.
        paths = [candidate.relpath for candidate in PIN.LEGS["ay"]]
        self.assertIn("crates/trust-ir-ay/src/vc.rs", paths)
        self.assertIn("crates/trust-ir-ay/src/bvblast.rs", paths)

    def test_the_workspace_excluded_frontend_lock_is_a_leg(self) -> None:
        paths = [candidate.relpath for candidate in PIN.LEGS["clean"]]
        self.assertIn("frontend/Cargo.lock", paths)


class SubstituteTests(unittest.TestCase):
    def test_manifest_rewrite_reports_the_expected_count(self) -> None:
        target = leg("clean", "crates/trust-ir-build/Cargo.toml")
        manifest = "".join(CLEAN_DEP_LINE.format(rev=OLD) for _ in range(3))
        rewritten, count = PIN.substitute(manifest, target, NEW)
        self.assertEqual(count, 3)
        self.assertIsNone(PIN.check_count(target, count))
        self.assertNotIn(OLD, rewritten)
        self.assertEqual(rewritten.count(NEW), 3)

    def test_spacing_drift_matches_nothing_and_is_rejected(self) -> None:
        # The bug this prevents: a reformatted manifest where the anchored
        # regex quietly matches zero, so the "bump" writes the file back
        # unchanged and reports success.
        target = leg("clean", "crates/trust-ir/Cargo.toml")
        drifted = (
            'clean-kernel = { version = "1.2.0", '
            'git="https://github.com/alabsystems/clean.git", rev="%s" }\n' % OLD
        )
        rewritten, count = PIN.substitute(drifted, target, NEW)
        self.assertEqual(count, 0)
        self.assertEqual(rewritten, drifted)
        self.assertIsNotNone(PIN.check_count(target, count))

        with self.assertRaises(PIN.PinError):
            PIN.plan_edits(lambda relpath: drifted, "clean", NEW)

    def test_the_two_constants_in_one_file_move_independently(self) -> None:
        # CLEAN_REVISION and AY_REVISION share a file. A global string replace
        # is only accidentally correct while the two SHAs differ.
        guard = (
            f'const CLEAN_REVISION: &str = "{OLD}";\n'
            f'const AY_REVISION: &str = "{OLD}";\n'
        )
        clean_leg = leg("clean", PIN.GUARD_TEST)
        rewritten, count = PIN.substitute(guard, clean_leg, NEW)
        self.assertEqual(count, 1)
        self.assertIn(f'const CLEAN_REVISION: &str = "{NEW}";', rewritten)
        self.assertIn(f'const AY_REVISION: &str = "{OLD}";', rewritten)

        ay_leg = leg("ay", PIN.GUARD_TEST)
        rewritten, count = PIN.substitute(guard, ay_leg, NEW)
        self.assertEqual(count, 1)
        self.assertIn(f'const CLEAN_REVISION: &str = "{OLD}";', rewritten)
        self.assertIn(f'const AY_REVISION: &str = "{NEW}";', rewritten)

    def test_lockfile_legs_are_never_rewritten(self) -> None:
        lock_leg = leg("clean", "frontend/Cargo.lock")
        with self.assertRaises(PIN.PinError):
            PIN.substitute("whatever", lock_leg, NEW)

    def test_lockfile_scan_sees_both_halves_of_a_source_row(self) -> None:
        lock_leg = leg("clean", "frontend/Cargo.lock")
        row = (
            'source = "git+https://github.com/alabsystems/clean.git'
            f'?rev={OLD}#{OTHER}"\n'
            'name = "unrelated"\n'
        )
        self.assertEqual(PIN.find_shas(row, lock_leg), [OLD, OTHER])

    def test_apply_rejects_an_abbreviated_revision(self) -> None:
        with self.assertRaises(PIN.PinError):
            PIN.plan_edits(lambda relpath: "", "clean", OLD[:7])


class SyntheticTreeTests(unittest.TestCase):
    """Drive the CLI over a synthetic repository, coherent and half-bumped."""

    def build_tree(self, root: Path, *, guard_rev: str) -> None:
        files = {
            "crates/trust-ir/Cargo.toml": CLEAN_DEP_LINE.format(rev=OLD),
            "crates/trust-ir-build/Cargo.toml": "".join(
                CLEAN_DEP_LINE.format(rev=OLD) for _ in range(3)
            ),
            PIN.GUARD_TEST: (
                f'const CLEAN_REVISION: &str = "{guard_rev}";\n'
                f'const AY_REVISION: &str = "{OTHER}";\n'
            ),
            "frontend/Cargo.lock": (
                'source = "git+https://github.com/alabsystems/clean.git'
                f'?rev={OLD}#{OLD}"\n'
            ),
            "Cargo.lock": "# no clean rows: the root [patch] absorbs them\n",
            "crates/trust-ir-ay/Cargo.toml": (
                'ay = { version = "0.4.0", '
                'git = "https://github.com/alabsystems/ay.git", '
                f'rev = "{OTHER}" }}\n'
            ),
            "crates/trust-ir-ay/src/vc.rs": (
                f'pub const AY_REV: &str = "{OTHER}";\n'
            ),
        }
        for relpath, text in files.items():
            path = root / relpath
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")

    def run_cli(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["python3", "-B", os.fspath(PIN_REWRITE_PATH), *args],
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )

    def test_coherent_tree_passes_census(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.build_tree(root, guard_rev=OLD)
            result = self.run_cli("census", "--root", os.fspath(root), "--dep", "clean")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("COHERENT", result.stdout)

            current = self.run_cli(
                "current", "--root", os.fspath(root), "--dep", "clean"
            )
            self.assertEqual(current.returncode, 0, current.stderr)
            self.assertEqual(current.stdout.strip(), OLD)

    def test_half_bumped_tree_fails_census_and_names_the_file(self) -> None:
        # The exact recurring failure: manifests moved, guard constant left
        # behind. The census must exit 1 AND name the disagreeing leg.
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.build_tree(root, guard_rev=NEW)
            result = self.run_cli("census", "--root", os.fspath(root), "--dep", "clean")
            self.assertEqual(result.returncode, 1)
            self.assertIn("INCOHERENT", result.stderr)
            self.assertIn("bump-dep-pin.sh", result.stderr)
            guard_row = [
                line
                for line in result.stdout.splitlines()
                if PIN.GUARD_TEST in line
            ]
            self.assertEqual(len(guard_row), 1, result.stdout)
            self.assertIn(NEW, guard_row[0])

            current = self.run_cli(
                "current", "--root", os.fspath(root), "--dep", "clean"
            )
            self.assertEqual(current.returncode, 1)

    def test_apply_stages_without_touching_the_source_tree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "repo"
            stage = Path(temporary) / "stage"
            root.mkdir()
            self.build_tree(root, guard_rev=OLD)
            before = {
                path: path.read_bytes()
                for path in sorted(root.rglob("*"))
                if path.is_file()
            }

            result = self.run_cli(
                "apply",
                "--root",
                os.fspath(root),
                "--dep",
                "clean",
                "--from",
                OLD,
                "--to",
                NEW,
                "--stage-dir",
                os.fspath(stage),
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(
                sorted(result.stdout.split()),
                sorted(
                    [
                        "crates/trust-ir/Cargo.toml",
                        "crates/trust-ir-build/Cargo.toml",
                        PIN.GUARD_TEST,
                    ]
                ),
            )

            after = {
                path: path.read_bytes()
                for path in sorted(root.rglob("*"))
                if path.is_file()
            }
            self.assertEqual(before, after, "apply must not mutate --root")

            staged = (stage / PIN.GUARD_TEST).read_text(encoding="utf-8")
            self.assertIn(f'const CLEAN_REVISION: &str = "{NEW}";', staged)
            self.assertIn(f'const AY_REVISION: &str = "{OTHER}";', staged)
            # Lockfiles are cargo's job, never the rewriter's.
            self.assertFalse((stage / "frontend/Cargo.lock").exists())

    def test_apply_refuses_when_from_disagrees(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "repo"
            stage = Path(temporary) / "stage"
            root.mkdir()
            self.build_tree(root, guard_rev=OLD)
            result = self.run_cli(
                "apply",
                "--root",
                os.fspath(root),
                "--dep",
                "clean",
                "--from",
                NEW,
                "--to",
                OTHER,
                "--stage-dir",
                os.fspath(stage),
            )
            self.assertEqual(result.returncode, 1)
            self.assertIn("does not match the tree", result.stderr)
            self.assertFalse(stage.exists())

    def test_abbreviated_and_uppercase_revisions_are_usage_errors(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "repo"
            root.mkdir()
            self.build_tree(root, guard_rev=OLD)
            for bad in (OLD[:7], NEW.upper()):
                result = self.run_cli(
                    "apply",
                    "--root",
                    os.fspath(root),
                    "--dep",
                    "clean",
                    "--to",
                    bad,
                    "--stage-dir",
                    os.fspath(Path(temporary) / "stage"),
                )
                self.assertEqual(result.returncode, 2, bad)
                self.assertIn("40-hex", result.stderr)

    def test_unknown_dependency_is_a_usage_error(self) -> None:
        result = self.run_cli("census", "--dep", "llvm")
        self.assertEqual(result.returncode, 2)


class BumpScriptTests(unittest.TestCase):
    """The driver's argument validation, which needs no repository state."""

    def run_bump(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["/bin/bash", os.fspath(BUMP_SCRIPT), *args],
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )

    def test_missing_arguments_print_usage(self) -> None:
        result = self.run_bump()
        self.assertEqual(result.returncode, 2)
        self.assertIn("usage: scripts/bump-dep-pin.sh", result.stderr)

    def test_unknown_dependency_is_rejected(self) -> None:
        result = self.run_bump("llvm", "b" * 40)
        self.assertEqual(result.returncode, 2)
        self.assertIn("dependency must be clean or ay", result.stderr)

    def test_abbreviated_revision_is_rejected(self) -> None:
        result = self.run_bump("clean", "76a7508e")
        self.assertEqual(result.returncode, 1)
        self.assertIn("not a full 40-hex", result.stderr)

    def test_uppercase_revision_is_rejected(self) -> None:
        result = self.run_bump("ay", "B" * 40)
        self.assertEqual(result.returncode, 1)
        self.assertIn("not a full 40-hex", result.stderr)

    def test_unknown_option_prints_usage(self) -> None:
        result = self.run_bump("clean", "b" * 40, "--force")
        self.assertEqual(result.returncode, 2)
        self.assertIn("unknown option", result.stderr)

    def test_clean_sibling_check_accepts_linked_worktrees(self) -> None:
        script = BUMP_SCRIPT.read_text(encoding="utf-8")
        self.assertIn(
            'git -C "$CLEAN_SIBLING" rev-parse --is-inside-work-tree', script
        )
        self.assertNotIn('[[ -d "$CLEAN_SIBLING/.git" ]]', script)


class RepositoryCoherenceTests(unittest.TestCase):
    """The live repository must satisfy its own leg table."""

    def test_this_repository_is_pin_coherent(self) -> None:
        read = PIN.repo_reader(ROOT)
        for dep in sorted(PIN.LEGS):
            with self.subTest(dep=dep):
                report = PIN.census(read, dep)
                self.assertTrue(report.coherent, report.render())

    def test_the_leg_table_matches_the_rust_guard_inventory(self) -> None:
        # scripts/pin_rewrite.py and dependency_pin_coherence.rs duplicate the
        # same inventory. Drift between them is what makes a bump fail with a
        # confusing count mismatch, so assert they agree.
        guard = (ROOT / PIN.GUARD_TEST).read_text(encoding="utf-8")
        expected = {
            candidate.relpath: candidate.expected
            for candidate in PIN.LEGS["clean"]
            if candidate.rewritable and candidate.relpath.endswith("Cargo.toml")
        }
        self.assertEqual(
            expected,
            {
                "crates/trust-ir/Cargo.toml": 1,
                "crates/trust-ir-build/Cargo.toml": 3,
            },
        )
        self.assertIn(
            'assert_exact_manifest_pins("crates/trust-ir/Cargo.toml", TRUST_IR_MANIFEST, 1)',
            guard,
        )
        self.assertIn("TRUST_IR_BUILD_MANIFEST,\n        3,", guard)

    def test_the_guard_failure_message_names_the_bump_script(self) -> None:
        guard = (ROOT / PIN.GUARD_TEST).read_text(encoding="utf-8")
        self.assertIn("scripts/bump-dep-pin.sh", guard)
        self.assertIn("PIN_MOVE_PROTOCOL", guard)
        # Every assertion must carry the protocol, or the one that fires is the
        # one that teaches nothing.
        assertions = guard.count("assert!(") + guard.count("assert_eq!(")
        self.assertEqual(guard.count("{PIN_MOVE_PROTOCOL}"), assertions)

    def test_ci_gates_runs_both_halves_of_the_pin_guard(self) -> None:
        gates = (ROOT / "scripts" / "ci_gates.sh").read_text(encoding="utf-8")
        self.assertIn("gate dependency-pin-census pin_census", gates)
        self.assertIn("gate dependency-pin-coherence", gates)
        self.assertIn("--test dependency_pin_coherence", gates)


if __name__ == "__main__":
    unittest.main()
