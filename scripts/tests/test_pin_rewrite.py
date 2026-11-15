"""Unit coverage for the dependency-pin leg table and rewriter.

The failure mode this guards is a rewriter that matches ZERO occurrences and
reports success — that is how a "pure pin bump" silently moves only some legs.
Every leg therefore declares an exact match count, and the tests below prove
the count is enforced rather than advisory.
"""

from __future__ import annotations

import importlib.util
import contextlib
import json
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import tarfile
import hashlib
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PIN_REWRITE_PATH = ROOT / "scripts" / "pin_rewrite.py"
BUMP_SCRIPT = ROOT / "scripts" / "bump-dep-pin.sh"
TARGO_RUNNER = ROOT / "scripts" / "run-targo.sh"

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


def copy_archived_pin_boundary(root: Path) -> None:
    fixture = ROOT / "scripts/tests/fixtures/captured-pin-boundary"
    manifest = fixture / "artifact-manifest.json"
    assert hashlib.sha256(manifest.read_bytes()).hexdigest() == PIN.ARCHIVED_SOURCE_MANIFEST_SHA256
    rows = json.loads(manifest.read_text())["files"]
    with contextlib.ExitStack() as opened:
        archive = None
        for row in rows:
            if not row["path"].startswith("source/"):
                continue
            source = fixture / row["path"]
            target = root / PIN.ARCHIVED_SOURCE_ROOT / row["path"][7:]
            target.parent.mkdir(parents=True, exist_ok=True)
            if source.is_file():
                shutil.copy2(source, target)
            else:
                # Exact inert source fixture; no private history/network lookup.
                # Its original digest and all inner member checks remain binding.
                if archive is None:
                    container = fixture / "source.tar.gz"
                    assert hashlib.sha256(container.read_bytes()).hexdigest() == "311358d0bee8eaa5c692bd2aa1aee268e48d17311bb629848187d59413fecfba"
                    archive = opened.enter_context(tarfile.open(container, mode="r:gz"))
                member = archive.getmember(row["path"])
                assert member.isfile() and member.mode in (0o644, 0o755)
                payload = archive.extractfile(member).read()
                assert hashlib.sha256(payload).hexdigest() == row["sha256"]
                target.write_bytes(payload)
                target.chmod(member.mode)
    target_manifest = root / PIN.ARCHIVED_SOURCE_MANIFEST
    target_manifest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(manifest, target_manifest)


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

    def test_every_package_version_leg_declares_an_exact_count(self) -> None:
        for dep, legs in PIN.VERSION_LEGS.items():
            for candidate in legs:
                with self.subTest(dep=dep, leg=candidate.relpath):
                    self.assertGreater(candidate.expected, 0)
                    self.assertIn("(?P<version>", candidate.pattern)

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

    def test_clean_external_note_describes_the_predecessor_epoch_cut(self) -> None:
        note = PIN.EXTERNAL_LEGS["clean"]
        self.assertIn("predecessor-epoch cut", note)
        self.assertIn("final epoch receipt", note)
        self.assertNotIn("same transaction", note)
        self.assertNotIn("ty-mcc-drift-guard", note)


class SubstituteTests(unittest.TestCase):
    def test_manifest_rewrite_reports_the_expected_count(self) -> None:
        target = leg("clean", "crates/trust-ir-build/Cargo.toml")
        manifest = "".join(CLEAN_DEP_LINE.format(rev=OLD) for _ in range(6))
        rewritten, count = PIN.substitute(manifest, target, NEW)
        self.assertEqual(count, 6)
        self.assertIsNone(PIN.check_count(target, count))
        self.assertNotIn(OLD, rewritten)
        self.assertEqual(rewritten.count(NEW), 6)

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

    def test_version_rewrite_rejects_a_missing_guard_leg(self) -> None:
        manifest = CLEAN_DEP_LINE.format(rev=OLD)

        def read(relpath: str) -> str:
            if relpath == "crates/trust-ir/Cargo.toml":
                return manifest
            if relpath == "crates/trust-ir-build/Cargo.toml":
                return manifest * 6
            if relpath == PIN.GUARD_TEST:
                return f'const CLEAN_REVISION: &str = "{OLD}";\n'
            raise AssertionError(relpath)

        with self.assertRaisesRegex(PIN.PinError, "expected exactly 1"):
            PIN.plan_version_edits(read, "clean", "2.0.0")

    def test_version_rewrite_rejects_noncanonical_requirement(self) -> None:
        with self.assertRaisesRegex(PIN.PinError, "canonical semantic version"):
            PIN.plan_version_edits(lambda _: "", "clean", "^2.0")


class StaticGuardMirrorTests(unittest.TestCase):
    """The Python fallback must reject every authority class the Rust guard does."""

    @staticmethod
    def _reader(overrides: dict[str, str] | None = None) -> "PIN.Reader":
        base = PIN.repo_reader(ROOT)
        replacements = overrides or {}

        def read(relpath: str) -> str:
            return replacements.get(relpath, base(relpath))

        return read

    def assert_rejected(
        self, relpath: str, tampered: str, expected_diagnostic: str
    ) -> None:
        report = PIN.static_guard(self._reader({relpath: tampered}))
        self.assertFalse(report.coherent, report.render())
        self.assertIn(expected_diagnostic, report.render())

    def test_live_repository_passes_the_exact_static_mirror(self) -> None:
        report = PIN.static_guard(self._reader())
        self.assertTrue(report.coherent, report.render())

    def test_lock_source_control_prefix_is_not_rust_whitespace(self) -> None:
        revision = PIN.census(self._reader(), "clean").current()
        exact_source = f'source = "git+{PIN.CLEAN_REMOTE}?rev={revision}#{revision}"'
        lock = (ROOT / "Cargo.lock").read_text(encoding="utf-8")
        self.assertIn(exact_source, lock)
        for prefix in ("\x1c", "\x1d", "\x1e", "\x1f"):
            changed = lock.replace(exact_source, prefix + exact_source, 1)
            with self.subTest(prefix=prefix):
                self.assert_rejected("Cargo.lock", changed, "Clean source")

    def test_lock_only_lf_and_crlf_separate_rust_source_lines(self) -> None:
        revision = PIN.census(self._reader(), "clean").current()
        exact_source = f'source = "git+{PIN.CLEAN_REMOTE}?rev={revision}#{revision}"'
        lock = (ROOT / "Cargo.lock").read_text(encoding="utf-8")
        self.assertIn("\n" + exact_source, lock)
        for separator in ("\r", "\v", "\f", "\x85", "\x1c", "\x1d", "\x1e", "\u2028", "\u2029"):
            changed = lock.replace("\n" + exact_source, separator + exact_source, 1)
            with self.subTest(separator=separator):
                self.assert_rejected("Cargo.lock", changed, "Clean source")

    def test_frontend_lock_control_prefix_does_not_authenticate_exact_version(self) -> None:
        version = PIN.version_census(self._reader(), "clean").current()
        exact_version = f'version = "{version}"'
        lock = (ROOT / "frontend/Cargo.lock").read_text(encoding="utf-8")
        blocks = lock.split("[[package]]")
        selected = [i for i, block in enumerate(blocks) if 'name = "clean-kernel"' in block]
        self.assertEqual(len(selected), 1)
        position = selected[0]
        self.assertIn(exact_version, blocks[position])
        for prefix in ("\x1c", "\x1d", "\x1e", "\x1f"):
            changed = blocks.copy()
            changed[position] = changed[position].replace(exact_version, prefix + exact_version, 1)
            with self.subTest(prefix=prefix):
                self.assert_rejected("frontend/Cargo.lock", "[[package]]".join(changed), "exact version")

    def test_lock_rust_lf_crlf_and_unterminated_final_line_remain_supported(self) -> None:
        for relpath in ("Cargo.lock", "frontend/Cargo.lock"):
            lock = (ROOT / relpath).read_text(encoding="utf-8")
            for changed in (lock.rstrip("\n"), lock.replace("\n", "\r\n")):
                report = PIN.static_guard(self._reader({relpath: changed}))
                with self.subTest(relpath=relpath, crlf="\r\n" in changed):
                    self.assertTrue(report.coherent, report.render())

    def test_repo_reader_preserves_lock_bytes_for_rust_line_checks(self) -> None:
        revision = PIN.census(self._reader(), "clean").current()
        exact_source = f'source = "git+{PIN.CLEAN_REMOTE}?rev={revision}#{revision}"'
        lock = (ROOT / "Cargo.lock").read_text(encoding="utf-8")
        changed = lock.replace("\n" + exact_source, "\r" + exact_source, 1)
        self.assertNotEqual(changed, lock)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "Cargo.lock"
            path.write_bytes(changed.encode("utf-8"))
            read = PIN.repo_reader(Path(temporary))
            report = PIN.static_guard(self._reader({"Cargo.lock": read("Cargo.lock")}))
            self.assertFalse(report.coherent, report.render())
            self.assertIn("Clean source", report.render())
            self.assertEqual(read("Cargo.lock").encode("utf-8"), path.read_bytes())

    def test_root_clean_patch_is_rejected(self) -> None:
        manifest = (ROOT / "Cargo.toml").read_text(encoding="utf-8")
        manifest += (
            '\n[patch."https://github.com/alabsystems/clean.git"]\n'
            'clean-kernel = { path = "../clean/crates/clean-kernel" }\n'
        )
        self.assert_rejected("Cargo.toml", manifest, "re-introduces a Clean path patch")

    def test_clean_manifest_inventory_and_version_are_exact(self) -> None:
        relpath = "crates/trust-ir/Cargo.toml"
        manifest = (ROOT / relpath).read_text(encoding="utf-8")
        clean_revision = PIN.census(self._reader(), "clean").current()
        clean_version = PIN.version_census(self._reader(), "clean").current()
        manifest += (
            f'\nclean-extra = {{ version = "{clean_version}", '
            f'git = "{PIN.CLEAN_REMOTE}", rev = "{clean_revision}" }}\n'
        )
        self.assert_rejected(relpath, manifest, "Clean dependency inventory")

    def test_operational_factory_optional_dependency_is_an_exact_default_off_leg(self) -> None:
        relpath = "crates/trust-ir-build/Cargo.toml"
        manifest = (ROOT / relpath).read_text(encoding="utf-8")
        regular = manifest.split("[dev-dependencies]", 1)[0]
        lines = [line for line in regular.splitlines() if line.startswith("clean-verify = ")]
        self.assertEqual(len(lines), 1)
        declaration = lines[0]
        self.assertIn("optional = true", declaration)
        self.assertIn('source-value-operational = ["clean-tv-anchor", "dep:clean-verify"]', manifest)
        self.assertIn('default = ["clean-tv-anchor"]', manifest)
        self.assertIn('clean-tv-anchor = ["trust-ir/clean-expr"]', manifest)
        revision = PIN.census(self._reader(), "clean").current()
        version = PIN.version_census(self._reader(), "clean").current()
        for wrong, diagnostic in [
            (declaration.replace(revision, OTHER), "wrong revision"),
            (declaration.replace(f'version = "{version}"', 'version = "999.0.0"'), "wrong version"),
        ]:
            with self.subTest(diagnostic=diagnostic):
                self.assert_rejected(relpath, manifest.replace(declaration, wrong), diagnostic)

    def test_byte_replay_dev_dependency_is_an_atomic_pin_and_version_leg(self) -> None:
        relpath = "crates/trust-ir-build/Cargo.toml"
        manifest = (ROOT / relpath).read_text(encoding="utf-8")
        dev_section = manifest.split("[dev-dependencies]", 1)[1]
        lines = [line for line in dev_section.splitlines()
                 if line.startswith("clean-verify = ")]
        self.assertEqual(len(lines), 1)
        declaration = lines[0]
        current = PIN.census(self._reader(), "clean").current()
        version = PIN.version_census(self._reader(), "clean").current()
        rewritten, count = PIN.substitute(manifest, leg("clean", relpath), NEW)
        self.assertEqual(count, 6)
        self.assertIn(declaration.replace(current, NEW), rewritten)
        for wrong, diagnostic in [
            (declaration.replace(current, OTHER), "wrong revision"),
            (declaration.replace(f'version = "{version}"', 'version = "999.0.0"'), "wrong version"),
        ]:
            with self.subTest(diagnostic=diagnostic):
                self.assertNotEqual(wrong, declaration)
                self.assert_rejected(relpath, manifest.replace(declaration, wrong), diagnostic)
        self.assert_rejected(relpath, manifest.replace(declaration, ""), "Clean dependency inventory")

    def test_frontend_clean_package_cardinality_is_exact(self) -> None:
        relpath = "frontend/Cargo.lock"
        lock = (ROOT / relpath).read_text(encoding="utf-8")
        clean_revision = PIN.census(self._reader(), "clean").current()
        clean_version = PIN.version_census(self._reader(), "clean").current()
        lock += (
            "\n[[package]]\n"
            'name = "clean-extra"\n'
            f'version = "{clean_version}"\n'
            f'source = "git+{PIN.CLEAN_REMOTE}?rev={clean_revision}'
            f'#{clean_revision}"\n'
        )
        self.assert_rejected(relpath, lock, "Clean package inventory")

    def test_frontend_clean_package_version_is_exact(self) -> None:
        relpath = "frontend/Cargo.lock"
        lock = (ROOT / relpath).read_text(encoding="utf-8")
        clean_version = PIN.version_census(self._reader(), "clean").current()
        lock = lock.replace(
            f'version = "{clean_version}"', 'version = "999.0.0"', 1
        )
        self.assert_rejected(relpath, lock, "does not use the exact version")

    def test_root_clean_source_must_be_exact(self) -> None:
        relpath = "Cargo.lock"
        lock = (ROOT / relpath).read_text(encoding="utf-8")
        clean_revision = PIN.census(self._reader(), "clean").current()
        lock = lock.replace(f"#{clean_revision}", f"#{OTHER}", 1)
        self.assert_rejected(relpath, lock, "stale or split Clean source")

    def test_ay_manifest_floating_selector_is_rejected(self) -> None:
        relpath = "crates/trust-ir-ay/Cargo.toml"
        manifest = (ROOT / relpath).read_text(encoding="utf-8")
        ay_revision = PIN.census(self._reader(), "ay").current()
        manifest = manifest.replace(
            f'rev = "{ay_revision}"',
            f'rev = "{ay_revision}", branch = "main"',
            1,
        )
        self.assert_rejected(relpath, manifest, "non-exact AY authority")

    def test_ay_provenance_constant_is_exact(self) -> None:
        relpath = "crates/trust-ir-ay/src/vc.rs"
        source = (ROOT / relpath).read_text(encoding="utf-8")
        ay_revision = PIN.census(self._reader(), "ay").current()
        source = source.replace(ay_revision, OTHER, 1)
        self.assert_rejected(relpath, source, "AY_REV is stale or missing")

    def test_ay_lock_package_source_cardinality_is_exact(self) -> None:
        relpath = "Cargo.lock"
        lock = (ROOT / relpath).read_text(encoding="utf-8")
        ay_revision = PIN.census(self._reader(), "ay").current()
        exact_source = (
            f'source = "git+{PIN.AY_REMOTE}?rev={ay_revision}'
            f'#{ay_revision}"'
        )
        lock = lock.replace(
            exact_source,
            f"{exact_source}\n{exact_source}",
            1,
        )
        self.assert_rejected(relpath, lock, "package/source cardinality mismatch")

    def test_every_ay_lock_package_has_the_exact_version(self) -> None:
        relpath = "Cargo.lock"
        lock = (ROOT / relpath).read_text(encoding="utf-8")
        ay_version = PIN.version_census(self._reader(), "ay").current()
        lock = lock.replace(
            f'name = "ay"\nversion = "{ay_version}"',
            'name = "ay"\nversion = "999.0.0"',
            1,
        )
        self.assert_rejected(relpath, lock, "outside the exact version")

    # x86_icmp_certificate_rule_names_the_pinned_ay, mirrored. Until 2026-09-30
    # the mirror lacked it and passed a tree whose rule named another AY while
    # the compiled gate 7 failed.
    @staticmethod
    def _rule_ay_literal(rev: str, version: str) -> str:
        return (
            "    ay: ChcX86IcmpCertifyingBuild {\n"
            '        package: "ay",\n'
            f'        rev: "{rev}",\n'
            f'        version: "{version}",\n'
        )

    def _rule_with_ay(self, rev: str, version: str) -> str:
        text = (ROOT / PIN.CERTIFICATE_RULE_PATH).read_text(encoding="utf-8")
        live = self._rule_ay_literal(*PIN.certificate_rule_ay(text))
        self.assertEqual(text.count(live), 1)
        return text.replace(live, self._rule_ay_literal(rev, version))

    def test_the_live_rule_names_the_ay_pin(self) -> None:
        text = (ROOT / PIN.CERTIFICATE_RULE_PATH).read_text(encoding="utf-8")
        self.assertEqual(
            PIN.certificate_rule_ay(text),
            (
                PIN.census(self._reader(), "ay").current(),
                PIN.version_census(self._reader(), "ay").current(),
            ),
        )

    def test_certificate_rule_ay_revision_split_is_rejected(self) -> None:
        version = PIN.version_census(self._reader(), "ay").current()
        self.assert_rejected(
            PIN.CERTIFICATE_RULE_PATH,
            self._rule_with_ay(NEW, version),
            f"CHC_X86_ICMP_CERTIFICATE_RULE.ay names {NEW} {version}, not the AY pin",
        )

    def test_certificate_rule_ay_version_split_is_rejected(self) -> None:
        revision = PIN.census(self._reader(), "ay").current()
        self.assert_rejected(
            PIN.CERTIFICATE_RULE_PATH,
            self._rule_with_ay(revision, "999.0.0"),
            f"CHC_X86_ICMP_CERTIFICATE_RULE.ay names {revision} 999.0.0, not the AY pin",
        )

    def test_an_unanchorable_certificate_rule_is_rejected(self) -> None:
        text = (ROOT / PIN.CERTIFICATE_RULE_PATH).read_text(encoding="utf-8")
        self.assert_rejected(
            PIN.CERTIFICATE_RULE_PATH,
            text.replace(PIN.CERTIFICATE_RULE_DECLARATION, "", 1),
            "must declare CHC_X86_ICMP_CERTIFICATE_RULE exactly once",
        )
        self.assert_rejected(
            PIN.CERTIFICATE_RULE_PATH,
            text.replace('        package: "ay",\n', '        package:  "ay",\n', 1),
            "found 0",
        )

    # The mirror table, held against the guard's #[test] set.
    def test_the_mirror_table_names_exactly_the_guard_tests(self) -> None:
        guard = (ROOT / PIN.GUARD_TEST).read_text(encoding="utf-8")
        self.assertEqual(PIN.guard_test_parity(guard), [])
        names = {match["name"] for match in PIN.GUARD_TEST_FUNCTION.finditer(guard)}
        self.assertEqual(names, set(PIN.GUARD_TEST_MIRRORS))
        # The one exemption is the one the docstrings and CLAUDE.md name.
        self.assertEqual(
            {name for name, mirror in PIN.GUARD_TEST_MIRRORS.items() if mirror is None},
            {"frontend_lock_resolves_under_locked"},
        )

    def test_a_guard_test_without_a_mirror_row_is_rejected(self) -> None:
        guard = (ROOT / PIN.GUARD_TEST).read_text(encoding="utf-8")
        guard += "\n#[test]\nfn an_unmirrored_pin_assertion() {}\n"
        self.assert_rejected(
            PIN.GUARD_TEST,
            guard,
            "test an_unmirrored_pin_assertion has no row in scripts/pin_rewrite.py GUARD_TEST_MIRRORS",
        )

    def test_a_mirror_row_whose_guard_test_is_gone_is_rejected(self) -> None:
        guard = (ROOT / PIN.GUARD_TEST).read_text(encoding="utf-8")
        renamed = guard.replace(
            "fn x86_icmp_certificate_rule_names_the_pinned_ay()",
            "fn x86_icmp_certificate_rule_renamed()",
            1,
        )
        self.assertNotEqual(renamed, guard)
        report = PIN.static_guard(self._reader({PIN.GUARD_TEST: renamed}))
        self.assertIn(
            "GUARD_TEST_MIRRORS names x86_icmp_certificate_rule_names_the_pinned_ay, "
            "which crates/trust-ir/tests/dependency_pin_coherence.rs no longer defines",
            report.render(),
        )
        self.assertIn("test x86_icmp_certificate_rule_renamed has no row", report.render())

    def test_a_guard_test_the_reader_cannot_parse_is_rejected(self) -> None:
        guard = (ROOT / PIN.GUARD_TEST).read_text(encoding="utf-8")
        guard += "\n#[test]\nfn generic_pin_assertion<T>() {}\n"
        self.assert_rejected(
            PIN.GUARD_TEST, guard, "the mirror table cannot be checked"
        )


class SyntheticTreeTests(unittest.TestCase):
    """Drive the CLI over a synthetic repository, coherent and half-bumped."""

    def build_tree(self, root: Path, *, guard_rev: str) -> None:
        files = {
            "crates/trust-ir/Cargo.toml": CLEAN_DEP_LINE.format(rev=OLD),
            "crates/trust-ir-build/Cargo.toml": "".join(
                CLEAN_DEP_LINE.format(rev=OLD) for _ in range(6)
            ),
            PIN.GUARD_TEST: (
                f'const CLEAN_REVISION: &str = "{guard_rev}";\n'
                'const CLEAN_VERSION: &str = "1.2.0";\n'
                f'const AY_REVISION: &str = "{OTHER}";\n'
                'const AY_VERSION: &str = "0.4.0";\n'
            ),
            "frontend/Cargo.lock": (
                'source = "git+https://github.com/alabsystems/clean.git'
                f'?rev={OLD}#{OLD}"\n'
            ),
            "Cargo.lock": (
                'source = "git+https://github.com/alabsystems/clean.git'
                f'?rev={OLD}#{OLD}"\n'
                'source = "git+https://github.com/alabsystems/ay.git'
                f'?rev={OTHER}#{OTHER}"\n'
            ),
            "crates/trust-ir-ay/Cargo.toml": (
                'ay = { version = "0.4.0", '
                'git = "https://github.com/alabsystems/ay.git", '
                f'rev = "{OTHER}" }}\n'
                'ay-proof = { version = "0.4.0", '
                'git = "https://github.com/alabsystems/ay.git", '
                f'rev = "{OTHER}" }}\n'
            ),
            "crates/trust-ir-ay/src/vc.rs": (
                f'pub const AY_REV: &str = "{OTHER}";\n'
            ),
            "crates/trust-ir-ay/src/bvblast.rs": (
                'pub const BVBLAST_PROVER: &str = '
                f'"trust-ir-ay/bvblast@{OTHER}";\n'
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

    def test_apply_clean_ay_stages_both_shared_guard_constants_atomically(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "repo"
            stage = Path(temporary) / "stage"
            root.mkdir()
            self.build_tree(root, guard_rev=OLD)
            before = {
                path.relative_to(root): path.read_bytes()
                for path in sorted(root.rglob("*"))
                if path.is_file()
            }

            result = self.run_cli(
                "apply-clean-ay",
                "--root",
                os.fspath(root),
                "--clean-to",
                NEW,
                "--ay-to",
                NEW,
                "--stage-dir",
                os.fspath(stage),
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            guard = (stage / PIN.GUARD_TEST).read_text(encoding="utf-8")
            self.assertIn(f'const CLEAN_REVISION: &str = "{NEW}";', guard)
            self.assertIn(f'const AY_REVISION: &str = "{NEW}";', guard)
            self.assertNotIn(OLD, guard)
            self.assertNotIn(OTHER, guard)
            after = {
                path.relative_to(root): path.read_bytes()
                for path in sorted(root.rglob("*"))
                if path.is_file()
            }
            self.assertEqual(before, after, "coordinated apply must not mutate --root")

    def test_both_apply_modes_refuse_staging_inside_the_source_tree(self) -> None:
        for mode in ("apply", "apply-clean-ay"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / "repo"
                root.mkdir()
                self.build_tree(root, guard_rev=OLD)
                before = {p.relative_to(root): p.read_bytes() for p in root.rglob("*") if p.is_file()}
                args = (["--dep", "clean", "--to", NEW] if mode == "apply"
                        else ["--clean-to", NEW, "--ay-to", NEW])
                result = self.run_cli(mode, "--root", str(root), *args,
                                      "--stage-dir", str(root / PIN.ARCHIVED_SOURCE_ROOT))
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn("outside the source tree", result.stderr)
                self.assertEqual(before, {p.relative_to(root): p.read_bytes() for p in root.rglob("*") if p.is_file()})

    def test_both_apply_modes_refuse_redirected_stage_roots_and_children(self) -> None:
        for mode in ("apply", "apply-clean-ay"):
            for redirect in ("root", "child", "late-child"):
                with self.subTest(mode=mode, redirect=redirect), tempfile.TemporaryDirectory() as temporary:
                    root = Path(temporary) / "repo"
                    root.mkdir()
                    self.build_tree(root, guard_rev=OLD)
                    before = {p.relative_to(root): p.read_bytes() for p in root.rglob("*") if p.is_file()}
                    stage = Path(temporary) / "stage"
                    if redirect == "root":
                        stage.symlink_to(root, target_is_directory=True)
                    elif redirect == "child":
                        stage.mkdir()
                        (stage / "crates").symlink_to(root / "crates", target_is_directory=True)
                    else:
                        (stage / "crates/trust-ir").mkdir(parents=True)
                        (stage / "crates/trust-ir/tests").symlink_to(root / "crates/trust-ir/tests", target_is_directory=True)
                    args = (["--dep", "clean", "--to", NEW] if mode == "apply"
                            else ["--clean-to", NEW, "--ay-to", NEW])
                    result = self.run_cli(mode, "--root", str(root), *args, "--stage-dir", str(stage))
                    self.assertEqual(result.returncode, 1, result.stderr)
                    self.assertEqual(before, {p.relative_to(root): p.read_bytes() for p in root.rglob("*") if p.is_file()})
                    if redirect != "root":
                        self.assertEqual(list(stage.iterdir()), [stage / "crates"])
                    if redirect == "late-child":
                        self.assertFalse((stage / "crates/trust-ir-build/Cargo.toml").exists())

    def test_both_apply_modes_refuse_physical_case_alias_of_archived_source(self) -> None:
        for mode in ("apply", "apply-clean-ay"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / "repo"
                root.mkdir()
                self.build_tree(root, guard_rev=OLD)
                copy_archived_pin_boundary(root)
                alias = root.with_name("REPO")
                if not alias.exists():
                    # Case-sensitive hosts still exercise a physical alias;
                    # this machine's case-insensitive APFS takes the real alias.
                    alias.symlink_to(root, target_is_directory=True)
                self.assertTrue(alias.samefile(root))
                before = {p.relative_to(root): p.read_bytes() for p in root.rglob("*") if p.is_file()}
                args = (["--dep", "clean", "--to", NEW] if mode == "apply"
                        else ["--clean-to", NEW, "--ay-to", NEW])
                result = self.run_cli(mode, "--root", str(root), *args,
                                      "--stage-dir", str(alias / PIN.ARCHIVED_SOURCE_ROOT))
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn("outside the source tree", result.stderr)
                self.assertEqual(before, {p.relative_to(root): p.read_bytes() for p in root.rglob("*") if p.is_file()})

    def test_both_apply_modes_refuse_existing_hardlinked_stage_outputs(self) -> None:
        for mode in ("apply", "apply-clean-ay"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / "repo"
                root.mkdir()
                self.build_tree(root, guard_rev=OLD)
                copy_archived_pin_boundary(root)
                captured = root / PIN.ARCHIVED_SOURCE_ROOT / "crates/trust-ir-build/Cargo.toml"
                stage = Path(temporary) / "stage"
                output = stage / "crates/trust-ir-build/Cargo.toml"
                output.parent.mkdir(parents=True)
                os.link(captured, output)
                before = captured.read_bytes()
                args = (["--dep", "clean", "--to", NEW] if mode == "apply"
                        else ["--clean-to", NEW, "--ay-to", NEW])
                result = self.run_cli(mode, "--root", str(root), *args, "--stage-dir", str(stage))
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn("must be fresh", result.stderr)
                self.assertEqual(captured.read_bytes(), before)
                with self.assertRaisesRegex(PIN.PinError, "exclusively create"):
                    PIN.write_staged_output(output, "must not overwrite shared inode")
                self.assertEqual(captured.read_bytes(), before)

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
        self.assertIn("dependency must be clean, ay, or clean-ay", result.stderr)

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

    def test_clean_authority_reads_the_immutable_target_commit(self) -> None:
        script = BUMP_SCRIPT.read_text(encoding="utf-8")
        self.assertIn('"$AUTHORITY" manifest clean "$clean_rev"', script)
        self.assertIn('"$AUTHORITY" offline-manifest "$CLEAN_OBJECT_REPO" "$clean_rev"', script)
        self.assertIn("immutable Clean commit content is authoritative", script)

    def test_cross_repo_guidance_does_not_require_impossible_sha_equality(self) -> None:
        bump = BUMP_SCRIPT.read_text(encoding="utf-8")
        guard = (ROOT / PIN.GUARD_TEST).read_text(encoding="utf-8")
        for source in (bump, guard):
            self.assertIn("predecessor-epoch cut", source)
            self.assertIn("epoch receipt", source)
        self.assertNotIn("all four must move together", bump)
        normalized_guard = " ".join(guard.split())
        self.assertNotIn(
            "must move in ty, ay and trust-cg in the same transaction",
            normalized_guard,
        )

    def test_bumper_mandates_static_guard_before_compiled_fallback(self) -> None:
        script = BUMP_SCRIPT.read_text(encoding="utf-8")
        self.assertGreaterEqual(script.count('pin static-guard --root "$ROOT"'), 2)
        self.assertIn("compiled guard SKIPPED (targo unavailable)", script)
        self.assertIn("static mirror passed. Run the compiled gate", script)

    def test_clean_object_cache_never_controls_compiled_source(self) -> None:
        script = BUMP_SCRIPT.read_text(encoding="utf-8")
        self.assertIn("TRUST_IR_CLEAN_REPO", script)
        self.assertNotIn("VALIDATED_CLEAN_SIBLING", script)
        self.assertNotIn("PATCHED_CLEAN_SIBLING", script)

    def test_every_bump_ignores_ambient_clean_worktree_state(self) -> None:
        script = BUMP_SCRIPT.read_text(encoding="utf-8")
        self.assertNotIn("SIBLING_DIRTY", script)
        self.assertNotIn("SIBLING_HEAD", script)
        self.assertNotIn('status --porcelain --untracked-files=all', script)

    def test_ay_bump_requires_frozen_clean_commit_and_seven_coowned_pins(self) -> None:
        script = BUMP_SCRIPT.read_text(encoding="utf-8")
        self.assertIn(
            'FROZEN_CLEAN_REV="$(pin current --root "$ROOT" --dep clean)"',
            script,
        )
        self.assertIn(
            'validate_clean_commit_ay_pin "$FROZEN_CLEAN_REV" "$REV"',
            script,
        )
        self.assertIn('[[ "$count" -ne 7 ]]', script)
        self.assertIn("expected exactly 7", script)

    def test_coordinated_mode_requires_a_second_full_revision(self) -> None:
        missing = self.run_bump("clean-ay", NEW)
        self.assertEqual(missing.returncode, 2)
        self.assertIn("clean-ay <clean-sha> <ay-sha>", missing.stderr)

        abbreviated = self.run_bump("clean-ay", NEW, OLD[:7])
        self.assertEqual(abbreviated.returncode, 1)
        self.assertIn("AY commit sha", abbreviated.stderr)


class BumpScriptIntegrationTests(unittest.TestCase):
    """Exercise external Clean authority checks and transactional rollback."""

    @staticmethod
    def _write(path: Path, text: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def _init_clean(
        self,
        workspace: Path,
        *,
        ay_rev: str,
        clean_version: str = "1.2.0",
        ay_version: str = "0.9.0",
        declaration_count: int = 7,
        advance_head: bool = False,
    ) -> tuple[Path, str, str]:
        clean = workspace / "clean"
        clean.mkdir()
        declarations = "".join(
            f'ay-fixture-{index} = {{ version = "{ay_version}", '
            'git = "https://github.com/alabsystems/ay.git", '
            f'rev = "{ay_rev}" }}\n'
            for index in range(declaration_count)
        )
        self._write(
            clean / "Cargo.toml",
            "[workspace]\n"
            "members = []\n"
            "[workspace.package]\n"
            f'version = "{clean_version}"\n'
            "[workspace.dependencies]\n"
            + declarations,
        )
        subprocess.run(["git", "init", "-q", os.fspath(clean)], check=True)
        subprocess.run(
            ["git", "-C", os.fspath(clean), "config", "user.name", "pin-test"],
            check=True,
        )
        subprocess.run(
            ["git", "-C", os.fspath(clean), "config", "user.email", "pin@test.invalid"],
            check=True,
        )
        subprocess.run(
            ["git", "-C", os.fspath(clean), "add", "Cargo.toml"], check=True
        )
        subprocess.run(
            ["git", "-C", os.fspath(clean), "commit", "-q", "-m", "base"],
            check=True,
        )
        frozen = subprocess.check_output(
            ["git", "-C", os.fspath(clean), "rev-parse", "HEAD"], text=True
        ).strip()
        if advance_head:
            self._write(clean / "later.txt", "later clean bytes\n")
            subprocess.run(
                ["git", "-C", os.fspath(clean), "add", "later.txt"], check=True
            )
            subprocess.run(
                ["git", "-C", os.fspath(clean), "commit", "-q", "-m", "later"],
                check=True,
            )
        head = subprocess.check_output(
            ["git", "-C", os.fspath(clean), "rev-parse", "HEAD"], text=True
        ).strip()
        return clean, frozen, head

    def _build_trust_ir(
        self,
        workspace: Path,
        *,
        clean_rev: str,
        ay_rev: str,
        clean_version: str = "1.2.0",
        ay_version: str = "0.9.0",
        rule_ay: tuple[str, str] | None = None,
    ) -> Path:
        """A minimal trust-ir tree. ``rule_ay`` is the certificate rule's AY
        ``(rev, version)``, the pin's by default. An AY move needs it moved
        BEFORE the bump (re-certification is evidence, which the bumper cannot
        move), so a test that moves AY passes the target here."""
        root = workspace / "trust-ir"
        (root / "scripts").mkdir(parents=True)
        shutil.copy2(BUMP_SCRIPT, root / "scripts" / BUMP_SCRIPT.name)
        shutil.copy2(PIN_REWRITE_PATH, root / "scripts" / PIN_REWRITE_PATH.name)
        shutil.copy2(TARGO_RUNNER, root / "scripts" / TARGO_RUNNER.name)
        shutil.copy2(ROOT / "scripts/dependency_authority.py", root / "scripts/dependency_authority.py")
        self._write(root / "Cargo.toml", "[workspace]\nmembers = []\n")
        self._write(
            root / "crates/trust-ir/Cargo.toml",
            CLEAN_DEP_LINE.replace("1.2.0", clean_version).format(rev=clean_rev),
        )
        self._write(
            root / "crates/trust-ir-build/Cargo.toml",
            "".join(
                CLEAN_DEP_LINE.replace("1.2.0", clean_version).format(
                    rev=clean_rev
                )
                for _ in range(6)
            ),
        )
        self._write(
            root / PIN.GUARD_TEST,
            f'const CLEAN_REPOSITORY: &str = "{PIN.CLEAN_REMOTE}";\n'
            f'const CLEAN_REVISION: &str = "{clean_rev}";\n'
            f'const CLEAN_VERSION: &str = "{clean_version}";\n'
            f'const AY_REPOSITORY: &str = "{PIN.AY_REMOTE}";\n'
            f'const AY_REVISION: &str = "{ay_rev}";\n'
            f'const AY_VERSION: &str = "{ay_version}";\n'
            # One stub per guard test the mirror table names, so the parity
            # check reads the same test set the real guard has.
            + "".join(
                f"\n#[test]\nfn {name}() {{}}\n"
                for name in sorted(PIN.GUARD_TEST_MIRRORS)
            ),
        )
        rule_rev, rule_version = rule_ay or (ay_rev, ay_version)
        self._write(
            root / PIN.CERTIFICATE_RULE_PATH,
            PIN.CERTIFICATE_RULE_DECLARATION
            + "    ay: ChcX86IcmpCertifyingBuild {\n"
            + '        package: "ay",\n'
            + f'        rev: "{rule_rev}",\n'
            + f'        version: "{rule_version}",\n'
            + "    },\n"
            + "};\n",
        )
        self._write(
            root / "frontend/Cargo.lock",
            "version = 4\n\n"
            "[[package]]\n"
            'name = "clean-kernel"\n'
            f'version = "{clean_version}"\n'
            'source = "git+https://github.com/alabsystems/clean.git'
            f'?rev={clean_rev}#{clean_rev}"\n',
        )
        self._write(
            root / "Cargo.lock",
            "version = 4\n\n"
            "[[package]]\n"
            'name = "clean-kernel"\n'
            f'version = "{clean_version}"\n'
            'source = "git+https://github.com/alabsystems/clean.git'
            f'?rev={clean_rev}#{clean_rev}"\n\n'
            "[[package]]\n"
            'name = "ay"\n'
            f'version = "{ay_version}"\n'
            'source = "git+https://github.com/alabsystems/ay.git'
            f'?rev={ay_rev}#{ay_rev}"\n\n'
            "[[package]]\n"
            'name = "ay-proof"\n'
            f'version = "{ay_version}"\n'
            'source = "git+https://github.com/alabsystems/ay.git'
            f'?rev={ay_rev}#{ay_rev}"\n',
        )
        ay_line = (
            f'ay = {{ version = "{ay_version}", '
            'git = "https://github.com/alabsystems/ay.git", '
            f'rev = "{ay_rev}" }}\n'
        )
        self._write(root / "crates/trust-ir-ay/Cargo.toml", ay_line * 2)
        self._write(
            root / "crates/trust-ir-ay/src/vc.rs",
            f'pub const AY_REV: &str = "{ay_rev}";\n',
        )
        self._write(
            root / "crates/trust-ir-ay/src/bvblast.rs",
            f'pub const BVBLAST_PROVER: &str = "trust-ir-ay/bvblast@{ay_rev}";\n',
        )
        return root

    @staticmethod
    def _snapshot(root: Path) -> dict[str, bytes]:
        return {
            path.relative_to(root).as_posix(): path.read_bytes()
            for path in sorted(root.rglob("*"))
            if path.is_file()
        }

    def _fake_targo(self, directory: Path, body: str, *, guard_exit: int = 0) -> None:
        """A recorded fake frontend, never an actual compiler or resolver.

        The real repository wrapper must select this exact binary and preserve
        its argv. A poison stock-Cargo sibling catches accidental bypasses.
        Logs live outside the transaction tree so rollback cannot erase them.
        It answers the wrapper's `targo --unverified --version` discriminator
        (which upstream Cargo named targo fails) without logging it, so the
        log records exactly the dispatched commands.
        """
        binary = directory / "targo"
        self._write(
            binary,
            "#!/bin/sh\n"
            f"exec {shlex.quote(sys.executable)} - \"$@\" <<'PYTHON_FIXTURE'\n"
            "import json, os, subprocess, sys\n"
            "if sys.argv[1:] == ['--unverified', '--version']:\n"
            "    raise SystemExit(0)\n"
            "with open(os.environ['FAKE_TARGO_LOG'], 'a', encoding='utf-8') as log:\n"
            "    log.write(json.dumps(sys.argv[1:]) + '\\n')\n"
            "if sys.argv[1:3] == ['--unverified', 'test']:\n"
            f"    raise SystemExit({guard_exit})\n"
            "if sys.argv[1] not in ('metadata', 'update'):\n"
            "    raise SystemExit(97)\n"
            f"body = {body!r}\n"
            "raise SystemExit(subprocess.run(['/bin/sh', '-c', body, 'fake-targo', *sys.argv[1:]]).returncode)\n"
            "PYTHON_FIXTURE\n",
        )
        binary.chmod(0o755)
        cargo = directory / "cargo"
        self._write(cargo, "#!/bin/sh\necho 'stock Cargo bypass is forbidden' >&2\nexit 98\n")
        cargo.chmod(0o755)

    @staticmethod
    def _targo_calls(directory: Path) -> list[list[str]]:
        log = directory / "targo-calls.jsonl"
        if not log.exists():
            return []
        return [json.loads(line) for line in log.read_text(encoding="utf-8").splitlines()]

    @staticmethod
    def _expected_targo_calls(
        root: Path, *, frontend: bool, guard: bool = False
    ) -> list[list[str]]:
        calls = [["metadata", "--format-version", "1", "--all-features",
                  "--manifest-path", os.fspath(root / "Cargo.toml")]]
        if frontend:
            calls.append(["update", "--manifest-path", os.fspath(root / "frontend/Cargo.toml"),
                          "-p", "clean-kernel"])
        if guard:
            calls.append(["--unverified", "test", "--locked", "-p", "trust-ir",
                          "--test", "dependency_pin_coherence"])
        return calls

    @staticmethod
    def _environment(root: Path, path_prefix: Path | None = None) -> dict[str, str]:
        env = os.environ.copy()
        env.pop("TRUST_IR_CLEAN_SIBLING", None)
        # A parent test runner may select authenticated real binaries/object
        # caches. Fixtures must never inherit those authorities or compile.
        env["TRUST_IR_CLEAN_REPO"] = os.fspath(root.parent / "clean")
        env["TRUST_TARGO_BIN"] = os.fspath(root.parent / "absent-targo" / "targo")
        if path_prefix is not None:
            env["PATH"] = f"{path_prefix}{os.pathsep}{env['PATH']}"
            env["TRUST_TARGO_BIN"] = os.fspath(path_prefix / "targo")
            env["FAKE_TARGO_LOG"] = os.fspath(path_prefix / "targo-calls.jsonl")
        return env

    def _run_bump(
        self,
        root: Path,
        target: str,
        *,
        clean_override: Path | None = None,
        path_prefix: Path | None = None,
    ) -> subprocess.CompletedProcess[str]:
        env = self._environment(root, path_prefix)
        if clean_override is not None:
            env["TRUST_IR_CLEAN_REPO"] = os.fspath(clean_override)
        return subprocess.run(
            [
                "/bin/bash",
                os.fspath(root / "scripts/bump-dep-pin.sh"),
                "ay",
                target,
                "--offline",
                "--no-guard-test",
            ],
            cwd=root,
            env=env,
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )

    def _run_clean_ay_bump(
        self,
        root: Path,
        clean_target: str,
        ay_target: str,
        *,
        path_prefix: Path | None = None,
        clean_version: str | None = None,
        ay_version: str | None = None,
        dry_run: bool = False,
        run_guard: bool = False,
    ) -> subprocess.CompletedProcess[str]:
        env = self._environment(root, path_prefix)
        command = [
            "/bin/bash",
            os.fspath(root / "scripts/bump-dep-pin.sh"),
            "clean-ay",
            clean_target,
            ay_target,
            "--offline",
        ]
        if not run_guard:
            command.append("--no-guard-test")
        if clean_version is not None:
            command.extend(["--clean-version", clean_version])
        if ay_version is not None:
            command.extend(["--ay-version", ay_version])
        if dry_run:
            command.append("--dry-run")
        return subprocess.run(
            command,
            cwd=root,
            env=env,
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )

    def _run_clean_bump(
        self, root: Path, clean_target: str
    ) -> subprocess.CompletedProcess[str]:
        env = self._environment(root)
        return subprocess.run(
            [
                "/bin/bash",
                os.fspath(root / "scripts/bump-dep-pin.sh"),
                "clean",
                clean_target,
                "--offline",
                "--no-guard-test",
            ],
            cwd=root,
            env=env,
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )

    def test_ay_bump_uses_frozen_commit_even_when_clean_head_is_ahead(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, frozen, head = self._init_clean(
                workspace, ay_rev=OLD, advance_head=True
            )
            self.assertNotEqual(frozen, head)
            root = self._build_trust_ir(workspace, clean_rev=frozen, ay_rev=OLD)
            before = self._snapshot(root)

            result = self._run_bump(root, OLD)

            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn("all legs coherent", result.stdout)
            self.assertEqual(self._snapshot(root), before)

    def test_clean_only_bump_refuses_target_clean_with_new_ay_without_mutation(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, head = self._init_clean(workspace, ay_rev=NEW)
            self.assertEqual(clean_target, head)
            root = self._build_trust_ir(workspace, clean_rev=OLD, ay_rev=OLD)
            before = self._snapshot(root)

            result = self._run_clean_bump(root, clean_target)

            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("expected the exact coordinated AY revision", result.stdout)
            self.assertEqual(self._snapshot(root), before)
            self.assertNotIn(NEW, (root / PIN.GUARD_TEST).read_text(encoding="utf-8"))

    def test_offline_ay_bump_refuses_object_cache_missing_frozen_commit(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            clean, frozen, _ = self._init_clean(workspace, ay_rev=OLD)
            alternate_workspace = workspace / "alternate"
            alternate_workspace.mkdir()
            alternate, _, _ = self._init_clean(alternate_workspace, ay_rev=NEW)
            self.assertNotEqual(clean.resolve(), alternate.resolve())
            root = self._build_trust_ir(workspace, clean_rev=frozen, ay_rev=OLD)
            before = self._snapshot(root)

            result = self._run_bump(root, OLD, clean_override=alternate)

            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("offline Clean authority check cannot find commit", result.stdout)
            self.assertEqual(self._snapshot(root), before)

    def test_ay_bump_accepts_symlink_to_the_cargo_patched_checkout(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            clean, frozen, _ = self._init_clean(workspace, ay_rev=OLD)
            alias = workspace / "clean-alias"
            alias.symlink_to(clean, target_is_directory=True)
            root = self._build_trust_ir(workspace, clean_rev=frozen, ay_rev=OLD)
            before = self._snapshot(root)

            result = self._run_bump(root, OLD, clean_override=alias)

            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn("all legs coherent", result.stdout)
            self.assertEqual(self._snapshot(root), before)

    def test_ay_bump_ignores_dirty_clean_worktree_and_reads_commit(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            clean, frozen, _ = self._init_clean(workspace, ay_rev=OLD)
            self._write(clean / "untracked-proof-input.txt", "not committed\n")
            root = self._build_trust_ir(workspace, clean_rev=frozen, ay_rev=OLD)
            before = self._snapshot(root)

            result = self._run_bump(root, OLD)

            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn("all legs coherent", result.stdout)
            self.assertEqual(self._snapshot(root), before)

    def test_ay_bump_refuses_wrong_clean_declaration_count(self) -> None:
        for declaration_count in (0, 6, 8):
            with self.subTest(declaration_count=declaration_count):
                with tempfile.TemporaryDirectory() as temporary:
                    workspace = Path(temporary)
                    _, frozen, head = self._init_clean(
                        workspace,
                        ay_rev=OLD,
                        declaration_count=declaration_count,
                    )
                    self.assertEqual(frozen, head)
                    root = self._build_trust_ir(
                        workspace, clean_rev=frozen, ay_rev=OLD
                    )
                    before = self._snapshot(root)

                    result = self._run_bump(root, OLD)

                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn(
                        f"found {declaration_count} ay.git declarations",
                        result.stdout,
                    )
                    self.assertIn("expected exactly 7", result.stdout)
                    self.assertEqual(self._snapshot(root), before)

    def test_coordinated_semver_move_requires_both_explicit_reviews(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, _ = self._init_clean(
                workspace,
                ay_rev=NEW,
                clean_version="0.2.0",
                ay_version="0.13.0",
            )
            root = self._build_trust_ir(
                workspace,
                clean_rev=OLD,
                ay_rev=OLD,
                clean_version="0.1.0",
                ay_version="0.12.0",
            )
            before = self._snapshot(root)

            missing_clean = self._run_clean_ay_bump(
                root, clean_target, NEW, dry_run=True
            )
            self.assertNotEqual(missing_clean.returncode, 0, missing_clean.stdout)
            self.assertIn("--clean-version 0.2.0", missing_clean.stdout)
            self.assertEqual(self._snapshot(root), before)

            missing_ay = self._run_clean_ay_bump(
                root,
                clean_target,
                NEW,
                clean_version="0.2.0",
                dry_run=True,
            )
            self.assertNotEqual(missing_ay.returncode, 0, missing_ay.stdout)
            self.assertIn("--ay-version 0.13.0", missing_ay.stdout)
            self.assertEqual(self._snapshot(root), before)

    def test_coordinated_semver_move_refuses_wrong_or_malformed_version(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, _ = self._init_clean(
                workspace,
                ay_rev=NEW,
                clean_version="0.2.0",
                ay_version="0.13.0",
            )
            root = self._build_trust_ir(
                workspace,
                clean_rev=OLD,
                ay_rev=OLD,
                clean_version="0.1.0",
                ay_version="0.12.0",
            )
            before = self._snapshot(root)

            wrong = self._run_clean_ay_bump(
                root,
                clean_target,
                NEW,
                clean_version="0.2.0",
                ay_version="0.14.0",
                dry_run=True,
            )
            self.assertNotEqual(wrong.returncode, 0, wrong.stdout)
            self.assertIn("disagrees with immutable target authority 0.13.0", wrong.stdout)
            self.assertEqual(self._snapshot(root), before)

            malformed = self._run_clean_ay_bump(
                root,
                clean_target,
                NEW,
                clean_version="^0.2.0",
                ay_version="0.13.0",
                dry_run=True,
            )
            self.assertNotEqual(malformed.returncode, 0, malformed.stdout)
            self.assertIn("not an exact canonical Clean semantic version", malformed.stdout)
            self.assertEqual(self._snapshot(root), before)

    def test_coordinated_0_1_to_0_2_and_0_12_to_0_13_dry_run_is_atomic(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, _ = self._init_clean(
                workspace,
                ay_rev=NEW,
                clean_version="0.2.0",
                ay_version="0.13.0",
            )
            root = self._build_trust_ir(
                workspace,
                clean_rev=OLD,
                ay_rev=OLD,
                clean_version="0.1.0",
                ay_version="0.12.0",
            )
            before = self._snapshot(root)

            result = self._run_clean_ay_bump(
                root,
                clean_target,
                NEW,
                clean_version="0.2.0",
                ay_version="0.13.0",
                dry_run=True,
            )

            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn("DRY RUN — nothing installed", result.stdout)
            self.assertIn('const CLEAN_VERSION: &str = "0.2.0";', result.stdout)
            self.assertIn('const AY_VERSION: &str = "0.13.0";', result.stdout)
            self.assertIn('version = "0.2.0"', result.stdout)
            self.assertIn('version = "0.13.0"', result.stdout)
            self.assertEqual(self._snapshot(root), before)

    def test_post_install_failure_rolls_back_every_controlled_byte(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, frozen, head = self._init_clean(workspace, ay_rev=NEW)
            self.assertEqual(frozen, head)
            root = self._build_trust_ir(workspace, clean_rev=frozen, ay_rev=OLD)
            fake_bin = workspace / "fake-bin"
            fake_bin.mkdir()
            self._fake_targo(fake_bin,
                "printf '\\nforced lock mutation\\n' >> Cargo.lock\n"
                "exit 23\n",
            )
            before = self._snapshot(root)

            result = self._run_bump(root, NEW, path_prefix=fake_bin)

            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("root lock refresh failed", result.stdout)
            self.assertIn("ROLLED BACK — working tree unchanged", result.stdout)
            self.assertEqual(self._targo_calls(fake_bin),
                             self._expected_targo_calls(root, frontend=False))
            self.assertEqual(self._snapshot(root), before)
            self.assertNotIn(NEW, (root / "Cargo.lock").read_text(encoding="utf-8"))

    def test_coordinated_post_install_failure_restores_both_pin_sets_byte_exactly(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, head = self._init_clean(
                workspace,
                ay_rev=NEW,
                clean_version="0.2.0",
                ay_version="0.13.0",
            )
            self.assertEqual(clean_target, head)
            root = self._build_trust_ir(
                workspace,
                clean_rev=OLD,
                ay_rev=OLD,
                clean_version="0.1.0",
                ay_version="0.12.0",
            )
            fake_bin = workspace / "fake-bin"
            fake_bin.mkdir()
            self._fake_targo(fake_bin,
                "if [ \"$1\" = metadata ]; then\n"
                f"  sed 's/{OLD}/{NEW}/g' Cargo.lock > Cargo.lock.next || exit 21\n"
                "  mv Cargo.lock.next Cargo.lock || exit 22\n"
                "  exit 0\n"
                "fi\n"
                "printf '\\nforced coordinated frontend mutation\\n' >> frontend/Cargo.lock\n"
                "exit 23\n",
            )
            before = self._snapshot(root)

            result = self._run_clean_ay_bump(
                root,
                clean_target,
                NEW,
                path_prefix=fake_bin,
                clean_version="0.2.0",
                ay_version="0.13.0",
            )

            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("frontend/Cargo.lock refresh failed", result.stdout)
            self.assertIn("ROLLED BACK — working tree unchanged", result.stdout)
            self.assertEqual(self._targo_calls(fake_bin),
                             self._expected_targo_calls(root, frontend=True))
            self.assertEqual(self._snapshot(root), before)
            guard = (root / PIN.GUARD_TEST).read_text(encoding="utf-8")
            self.assertIn(f'const CLEAN_REVISION: &str = "{OLD}";', guard)
            self.assertIn(f'const AY_REVISION: &str = "{OLD}";', guard)
            self.assertIn('const CLEAN_VERSION: &str = "0.1.0";', guard)
            self.assertIn('const AY_VERSION: &str = "0.12.0";', guard)

    def test_coordinated_success_moves_both_pin_sets_and_both_locks(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, head = self._init_clean(workspace, ay_rev=NEW)
            self.assertEqual(clean_target, head)
            root = self._build_trust_ir(
                workspace, clean_rev=OLD, ay_rev=OLD, rule_ay=(NEW, "0.9.0")
            )
            fake_bin = workspace / "fake-bin"
            fake_bin.mkdir()
            self._fake_targo(fake_bin,
                "if [ \"$1\" = metadata ]; then\n"
                f"  sed -e 's|clean.git?rev={OLD}#{OLD}|clean.git?rev={clean_target}#{clean_target}|g' "
                f"-e 's|ay.git?rev={OLD}#{OLD}|ay.git?rev={NEW}#{NEW}|g' "
                "Cargo.lock > Cargo.lock.next || exit 31\n"
                "  mv Cargo.lock.next Cargo.lock || exit 32\n"
                "else\n"
                f"  sed 's/{OLD}/{clean_target}/g' frontend/Cargo.lock > frontend/Cargo.lock.next || exit 33\n"
                "  mv frontend/Cargo.lock.next frontend/Cargo.lock || exit 34\n"
                "fi\n",
            )

            result = self._run_clean_ay_bump(
                root, clean_target, NEW, path_prefix=fake_bin, run_guard=True
            )

            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn("DONE — Clean pinned", result.stdout)
            self.assertIn("STATIC GUARD: PASS", result.stdout)
            self.assertIn("VERIFY: guard test PASSED", result.stdout)
            self.assertEqual(self._targo_calls(fake_bin),
                             self._expected_targo_calls(root, frontend=True, guard=True))
            clean_report = PIN.census(PIN.repo_reader(root), "clean")
            ay_report = PIN.census(PIN.repo_reader(root), "ay")
            self.assertTrue(clean_report.coherent, clean_report.render())
            self.assertTrue(ay_report.coherent, ay_report.render())
            self.assertEqual(clean_report.current(), clean_target)
            self.assertEqual(ay_report.current(), NEW)
            guard = (root / PIN.GUARD_TEST).read_text(encoding="utf-8")
            self.assertIn(f'const CLEAN_REVISION: &str = "{clean_target}";', guard)
            self.assertIn(f'const AY_REVISION: &str = "{NEW}";', guard)

    def test_static_guard_failure_rolls_back_before_compiled_guard(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, _ = self._init_clean(workspace, ay_rev=NEW)
            root = self._build_trust_ir(workspace, clean_rev=OLD, ay_rev=OLD)
            self._write(
                root / "Cargo.toml",
                "[workspace]\nmembers = []\n"
                f'\n[patch."{PIN.CLEAN_REMOTE}"]\n'
                'clean-kernel = { path = "../clean/crates/clean-kernel" }\n',
            )
            fake_bin = workspace / "fake-bin"
            fake_bin.mkdir()
            self._fake_targo(fake_bin,
                "if [ \"$1\" = metadata ]; then\n"
                f"  sed -e 's|clean.git?rev={OLD}#{OLD}|clean.git?rev={clean_target}#{clean_target}|g' "
                f"-e 's|ay.git?rev={OLD}#{OLD}|ay.git?rev={NEW}#{NEW}|g' "
                "Cargo.lock > Cargo.lock.next || exit 31\n"
                "  mv Cargo.lock.next Cargo.lock || exit 32\n"
                "else\n"
                f"  sed 's/{OLD}/{clean_target}/g' frontend/Cargo.lock > frontend/Cargo.lock.next || exit 33\n"
                "  mv frontend/Cargo.lock.next frontend/Cargo.lock || exit 34\n"
                "fi\n",
            )
            before = self._snapshot(root)

            result = self._run_clean_ay_bump(
                root, clean_target, NEW, path_prefix=fake_bin, run_guard=True
            )

            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("re-introduces a Clean path patch", result.stdout)
            self.assertIn("exact static dependency-pin guard FAILED", result.stdout)
            self.assertIn("ROLLED BACK — working tree unchanged", result.stdout)
            self.assertEqual(self._targo_calls(fake_bin),
                             self._expected_targo_calls(root, frontend=True))
            self.assertEqual(self._snapshot(root), before)

    def test_ay_move_that_does_not_move_the_certificate_rule_rolls_back(self) -> None:
        # Tier 1 alone (no compiled guard): before the mirror held the rule this
        # printed DONE while gate 7 was red.
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, _ = self._init_clean(workspace, ay_rev=NEW)
            root = self._build_trust_ir(workspace, clean_rev=OLD, ay_rev=OLD)
            fake_bin = workspace / "fake-bin"
            fake_bin.mkdir()
            self._fake_targo(fake_bin,
                "if [ \"$1\" = metadata ]; then\n"
                f"  sed -e 's|clean.git?rev={OLD}#{OLD}|clean.git?rev={clean_target}#{clean_target}|g' "
                f"-e 's|ay.git?rev={OLD}#{OLD}|ay.git?rev={NEW}#{NEW}|g' "
                "Cargo.lock > Cargo.lock.next || exit 31\n"
                "  mv Cargo.lock.next Cargo.lock || exit 32\n"
                "else\n"
                f"  sed 's/{OLD}/{clean_target}/g' frontend/Cargo.lock > frontend/Cargo.lock.next || exit 33\n"
                "  mv frontend/Cargo.lock.next frontend/Cargo.lock || exit 34\n"
                "fi\n",
            )
            before = self._snapshot(root)

            result = self._run_clean_ay_bump(root, clean_target, NEW, path_prefix=fake_bin)

            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn(
                f"CHC_X86_ICMP_CERTIFICATE_RULE.ay names {OLD} 0.9.0, not the AY pin {NEW} 0.9.0",
                result.stdout,
            )
            self.assertIn("exact static dependency-pin guard FAILED", result.stdout)
            self.assertIn("ROLLED BACK — working tree unchanged", result.stdout)
            self.assertNotIn("DONE", result.stdout)
            self.assertEqual(self._snapshot(root), before)

    def test_compiled_guard_failure_still_rolls_back_after_successful_static_guard(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, _ = self._init_clean(workspace, ay_rev=NEW)
            root = self._build_trust_ir(
                workspace, clean_rev=OLD, ay_rev=OLD, rule_ay=(NEW, "0.9.0")
            )
            fake_bin = workspace / "fake-bin"
            fake_bin.mkdir()
            self._fake_targo(fake_bin,
                "if [ \"$1\" = metadata ]; then\n"
                f"  sed -e 's|clean.git?rev={OLD}#{OLD}|clean.git?rev={clean_target}#{clean_target}|g' "
                f"-e 's|ay.git?rev={OLD}#{OLD}|ay.git?rev={NEW}#{NEW}|g' "
                "Cargo.lock > Cargo.lock.next || exit 31\n"
                "  mv Cargo.lock.next Cargo.lock || exit 32\n"
                "else\n"
                f"  sed 's/{OLD}/{clean_target}/g' frontend/Cargo.lock > frontend/Cargo.lock.next || exit 33\n"
                "  mv frontend/Cargo.lock.next frontend/Cargo.lock || exit 34\n"
                "fi\n",
                guard_exit=41,
            )
            before = self._snapshot(root)
            result = self._run_clean_ay_bump(
                root, clean_target, NEW, path_prefix=fake_bin, run_guard=True
            )
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn("STATIC GUARD: PASS", result.stdout)
            self.assertIn("coherence guard test FAILED", result.stdout)
            self.assertNotIn("compiled guard SKIPPED", result.stdout)
            self.assertIn("ROLLED BACK — working tree unchanged", result.stdout)
            self.assertEqual(self._targo_calls(fake_bin),
                             self._expected_targo_calls(root, frontend=True, guard=True))
            self.assertEqual(self._snapshot(root), before)

    def test_unavailable_selected_targo_refuses_lock_refresh_and_restores_both_pin_sets(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, _ = self._init_clean(workspace, ay_rev=NEW)
            root = self._build_trust_ir(workspace, clean_rev=OLD, ay_rev=OLD)
            before = self._snapshot(root)
            result = self._run_clean_ay_bump(root, clean_target, NEW)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn("TRUST_TARGO_BIN is not executable", result.stdout)
            self.assertIn("root lock refresh failed (Targo metadata)", result.stdout)
            self.assertNotIn("compiled guard SKIPPED", result.stdout)
            self.assertIn("ROLLED BACK — working tree unchanged", result.stdout)
            self.assertEqual(self._snapshot(root), before)

    def test_coordinated_stale_warning_skips_only_unchanged_authority(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, _ = self._init_clean(workspace, ay_rev=OLD)
            root = self._build_trust_ir(
                workspace, clean_rev=OTHER, ay_rev=OLD
            )
            subprocess.run(["git", "init", "-q", os.fspath(root)], check=True)
            subprocess.run(["git", "-C", os.fspath(root), "add", "."], check=True)
            fake_bin = workspace / "fake-bin"
            fake_bin.mkdir()
            self._fake_targo(fake_bin,
                "if [ \"$1\" = metadata ]; then\n"
                f"  sed 's/{OTHER}/{clean_target}/g' Cargo.lock > Cargo.lock.next || exit 31\n"
                "  mv Cargo.lock.next Cargo.lock || exit 32\n"
                "else\n"
                f"  sed 's/{OTHER}/{clean_target}/g' frontend/Cargo.lock > frontend/Cargo.lock.next || exit 33\n"
                "  mv frontend/Cargo.lock.next frontend/Cargo.lock || exit 34\n"
                "fi\n",
            )

            unchanged = self._run_clean_ay_bump(
                root, clean_target, OLD, path_prefix=fake_bin
            )

            self.assertEqual(unchanged.returncode, 0, unchanged.stdout)
            self.assertNotIn(f"the previous revision {OLD}", unchanged.stdout)
            self.assertEqual(self._targo_calls(fake_bin),
                             self._expected_targo_calls(root, frontend=True))

        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary)
            _, clean_target, _ = self._init_clean(workspace, ay_rev=NEW)
            root = self._build_trust_ir(
                workspace, clean_rev=OTHER, ay_rev=OLD, rule_ay=(NEW, "0.9.0")
            )
            self._write(root / "notes/stale-ay.txt", f"retired AY {OLD}\n")
            subprocess.run(["git", "init", "-q", os.fspath(root)], check=True)
            subprocess.run(["git", "-C", os.fspath(root), "add", "."], check=True)
            fake_bin = workspace / "fake-bin"
            fake_bin.mkdir()
            self._fake_targo(fake_bin,
                "if [ \"$1\" = metadata ]; then\n"
                f"  sed -e 's/{OTHER}/{clean_target}/g' -e 's/{OLD}/{NEW}/g' Cargo.lock > Cargo.lock.next || exit 31\n"
                "  mv Cargo.lock.next Cargo.lock || exit 32\n"
                "else\n"
                f"  sed 's/{OTHER}/{clean_target}/g' frontend/Cargo.lock > frontend/Cargo.lock.next || exit 33\n"
                "  mv frontend/Cargo.lock.next frontend/Cargo.lock || exit 34\n"
                "fi\n",
            )

            stale = self._run_clean_ay_bump(
                root, clean_target, NEW, path_prefix=fake_bin
            )

            self.assertEqual(stale.returncode, 0, stale.stdout)
            self.assertIn(f"the previous revision {OLD}", stale.stdout)
            self.assertIn("notes/stale-ay.txt", stale.stdout)
            self.assertEqual(self._targo_calls(fake_bin),
                             self._expected_targo_calls(root, frontend=True))


    def test_dry_run_and_noop_refuse_capture_integrity_before_staging(self) -> None:
        for mode in ("clean", "clean-ay"):
            for damage in ("content", "redirect"):
                with self.subTest(mode=mode, damage=damage), tempfile.TemporaryDirectory() as temporary:
                    workspace = Path(temporary)
                    _, target, _ = self._init_clean(workspace, ay_rev=NEW)
                    root = self._build_trust_ir(workspace, clean_rev=target, ay_rev=NEW)
                    copy_archived_pin_boundary(root)
                    subprocess.run(["git", "init", "-q", str(root)], check=True)
                    subprocess.run(["git", "-C", str(root), "add", "."], check=True)
                    capture = root / next(iter(PIN.ARCHIVED_PIN_INPUT_SHA256))
                    if damage == "content":
                        capture.write_text("no dependency pin remains\n")
                    else:
                        held = workspace / "same-payload.data"
                        capture.rename(held)
                        capture.symlink_to(held)
                    before = self._snapshot(root)
                    command = ["/bin/bash", str(root / "scripts/bump-dep-pin.sh"), mode, target]
                    if mode == "clean-ay":
                        command.append(NEW)
                    command += ["--offline", "--dry-run", "--no-guard-test"]
                    result = subprocess.run(command, cwd=root, env=self._environment(root),
                                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                    self.assertEqual(result.returncode, 1, result.stdout)
                    self.assertIn("pin input integrity failed", result.stdout)
                    self.assertNotIn("PHASE B", result.stdout)
                    self.assertNotIn("DRY RUN", result.stdout)
                    self.assertEqual(self._snapshot(root), before)


class ArchivedLockCensusTests(unittest.TestCase):
    """Historical reproducer inputs must not become live dependency-pin legs."""

    def test_lock_templates_preserve_pins_without_exempting_active_report_locks(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(["git", "init", "-q", os.fspath(root)], check=True)
            for relative, fixture_name in (
                ("reports/2026-11-06-source-identity-data/consumer.Cargo.lock.in", "consumer.Cargo.lock.in"),
                ("reports/2026-11-07-zero-sized-wide-operands/Cargo.lock.in", "zero-sized-wide-Cargo.lock.in"),
            ):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                fixture = ROOT / "scripts/tests/fixtures/captured-pin-boundary" / fixture_name
                path.write_bytes(fixture.read_bytes())
            subprocess.run(["git", "-C", os.fspath(root), "add", "."], check=True)
            for dep in ("clean", "ay"):
                self.assertEqual(PIN.undeclared_pin_sites(root, dep), [])

            # An actual tracked Cargo input remains subject to the complement
            # census even when it is placed beside historical report assets.
            live = "reports/2026-11-07-zero-sized-wide-operands/Cargo.lock"
            (root / live).write_bytes((root / (live + ".in")).read_bytes())
            subprocess.run(["git", "-C", os.fspath(root), "add", live], check=True)
            offenders = PIN.undeclared_pin_sites(root, "clean")
            self.assertTrue(offenders)
            self.assertEqual({path for path, _, _ in offenders}, {live})

    def _captured_inputs(self, root: Path) -> None:
        subprocess.run(["git", "init", "-q", os.fspath(root)], check=True)
        copy_archived_pin_boundary(root)
        subprocess.run(["git", "-C", os.fspath(root), "add", "."], check=True)

    def test_exact_captured_inputs_are_not_rewritten_live_pin_legs(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._captured_inputs(root)
            for dep in ("clean", "ay"):
                self.assertEqual(PIN.undeclared_pin_sites(root, dep), [])
            live = root / next(iter(PIN.ARCHIVED_PIN_INPUT_SHA256))
            live = live.with_name("Cargo.toml")
            live.write_text(CLEAN_DEP_LINE.format(rev=OLD))
            subprocess.run(["git", "-C", os.fspath(root), "add", "."], check=True)
            with self.assertRaisesRegex(PIN.PinError, "gained an input"):
                PIN.undeclared_pin_sites(root, "clean")

    def test_changed_captured_input_refuses_even_after_pins_are_removed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._captured_inputs(root)
            relative = next(iter(PIN.ARCHIVED_PIN_INPUT_SHA256))
            (root / relative).write_text("no dependency pin remains\n")
            with self.assertRaisesRegex(PIN.PinError, "content changed"):
                PIN.undeclared_pin_sites(root, "clean")

    def test_captured_input_symlink_refuses_identical_target_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._captured_inputs(root)
            relative = next(iter(PIN.ARCHIVED_PIN_INPUT_SHA256))
            path = root / relative
            target = root / "same-bytes.lock.in"
            path.rename(target)
            path.symlink_to(target)
            with self.assertRaisesRegex(PIN.PinError, "symlink"):
                PIN.undeclared_pin_sites(root, "clean")

    def test_captured_parent_directory_symlink_refuses(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._captured_inputs(root)
            relative = next(iter(PIN.ARCHIVED_PIN_INPUT_SHA256))
            directory = (root / relative).parent
            target = directory.with_name("captured-source.data")
            directory.rename(target)
            directory.symlink_to(target)
            with self.assertRaisesRegex(PIN.PinError, "symlink"):
                PIN.undeclared_pin_sites(root, "clean")

    def test_url_free_neighbor_workspace_cannot_activate_the_capture(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._captured_inputs(root)
            path = root / PIN.ARCHIVED_SOURCE_ROOT / "Cargo.toml"
            path.write_text('[workspace]\nmembers = ["crates/trust-ir-build"]\n')
            with self.assertRaisesRegex(PIN.PinError, "gained an input"):
                PIN.undeclared_pin_sites(root, "clean")

    def test_external_cargo_members_paths_globs_and_redirects_cannot_adopt_capture(self) -> None:
        for kind in ("member", "path", "glob", "redirect", "multiline", "case-alias"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                self._captured_inputs(root)
                target = PIN.ARCHIVED_SOURCE_ROOT + "/crates/trust-ir-build"
                if kind == "glob":
                    target = "reports/*/evidence/*/source/crates/*"
                elif kind == "case-alias":
                    target = target.upper()
                elif kind == "redirect":
                    (root / "activate").symlink_to(root / target, target_is_directory=True)
                    target = "activate"
                text = ('[dependencies]\ncaptured = { path = "./' + target + '" }\n'
                        if kind == "path" else '[workspace]\nmembers = ["' + target + '"]\n')
                if kind == "multiline":
                    text = '[workspace]\nmembers = ["""\n' + target + '"""]\n'
                (root / "Cargo.toml").write_text(text)
                subprocess.run(["git", "-C", str(root), "add", "Cargo.toml"], check=True)
                with self.assertRaisesRegex(PIN.PinError, "adopts"):
                    PIN.undeclared_pin_sites(root, "clean")

    def test_cargo_comments_versions_and_quoted_keys_do_not_activate_capture(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._captured_inputs(root)
            (root / "Cargo.toml").write_text(
                '# "quotes across\n# comment lines"\n'
                '[workspace]\nmembers = []\n'
                '[dependencies]\nexample = { version = "*" }\n'
                '[profile.dev.package."*"]\nopt-level = 3\n'
            )
            subprocess.run(["git", "-C", str(root), "add", "Cargo.toml"], check=True)
            self.assertEqual(PIN.undeclared_pin_sites(root, "clean"), [])
            target = PIN.ARCHIVED_SOURCE_ROOT + "/crates/trust-ir-build"
            (root / "Cargo.toml").write_text(
                '[workspace]\n"members" = ["ordinary=directory", "' + target + '"]\n'
            )
            with self.assertRaisesRegex(PIN.PinError, "adopts"):
                PIN.undeclared_pin_sites(root, "clean")

    def test_workspace_glob_cannot_hide_a_symlink_into_the_capture(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._captured_inputs(root)
            (root / "activate").mkdir()
            (root / "activate/snapshot").symlink_to(
                root / PIN.ARCHIVED_SOURCE_ROOT / "crates", target_is_directory=True)
            (root / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["activate/*/trust-ir-build"]\n')
            subprocess.run(["git", "-C", str(root), "add", "Cargo.toml", "activate"], check=True)
            with self.assertRaisesRegex(PIN.PinError, "adopts"):
                PIN.undeclared_pin_sites(root, "clean")

    def test_recursive_and_outside_globs_refuse_without_walking_foreign_trees(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._captured_inputs(root)
            boundary = root / PIN.ARCHIVED_SOURCE_ROOT
            for pattern in ("**", "../*/Cargo.toml"):
                with self.subTest(pattern=pattern), self.assertRaises(PIN.PinError):
                    PIN.inspect_cargo_pattern(root, pattern, root, boundary)


class RepositoryCoherenceTests(unittest.TestCase):
    """The live repository must satisfy its own leg table."""

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
                "crates/trust-ir-build/Cargo.toml": 6,
            },
        )
        self.assertIn(
            'assert_exact_manifest_pins("crates/trust-ir/Cargo.toml", TRUST_IR_MANIFEST, 1)',
            guard,
        )
        self.assertIn("TRUST_IR_BUILD_MANIFEST,\n        6,", guard)

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
        self.assertIn("pin_rewrite.py\" static-guard", gates)
        self.assertIn("gate dependency-pin-coherence", gates)
        self.assertIn("--test dependency_pin_coherence", gates)


if __name__ == "__main__":
    unittest.main()
