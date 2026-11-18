from __future__ import annotations

import contextlib
import builtins
import importlib.util
import io
import os
import sys
import tempfile
import unittest
from unittest import mock
from pathlib import Path
from typing import Iterator, Optional


ROOT = Path(__file__).resolve().parents[2]
CHECKER_PATH = ROOT / "scripts" / "check_trust_default_authority.py"
SPEC = importlib.util.spec_from_file_location("check_trust_default_authority", CHECKER_PATH)
assert SPEC is not None and SPEC.loader is not None
CHECKER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECKER
with mock.patch.object(sys, "path", [str(ROOT / "scripts"), *sys.path]):
    SPEC.loader.exec_module(CHECKER)


class TrustDefaultAuthorityTests(unittest.TestCase):
    TRUST = '[toolchain]\nchannel = "trust"\n'
    TRUST_SPELLINGS = (
        '[toolchain]\nchannel = "trust" # selected compiler\n',
        '[toolchain]\n"channel" = \'trust\'\n',
        'toolchain.channel = "trust"\n',
        '["toolchain"]\nchannel = "tr\\u0075st"\n',
        'toolchain = { channel = "trust" }\n',
        '[toolchain]\nchannel = """trust"""\n',
        '[metadata]\nchannel = "stable"\n[toolchain]\nchannel = "trust"\n',
    )
    COMMIT = "0123456789abcdef0123456789abcdef01234567"

    @staticmethod
    def temporary_directory():
        # Do not inherit an unsafe TMPDIR ancestor: the actual authority guard
        # must reject that hierarchy. /tmp's trusted sticky route permits each
        # private 0700 test root without changing caller-owned directories.
        # Canonical: macOS spells /tmp as a symlink to /private/tmp, and the
        # checker walks resolved components, so fixture paths must be resolved.
        return tempfile.TemporaryDirectory(prefix="trust-authority-test-",
                                           dir=os.path.realpath("/tmp"))

    @staticmethod
    def protected_directory(path: Path) -> None:
        missing = []
        while not path.exists():
            missing.append(path)
            path = path.parent
        for directory in reversed(missing):
            directory.mkdir(mode=0o755)

    def test_upstream_default_is_honestly_unverified(self) -> None:
        self.assertEqual(
            CHECKER.policy_issues('[toolchain]\nchannel = "1.97.1"\n', ""), []
        )

    def test_equivalent_toml_trust_pins_keep_authority_and_policy_checks(self) -> None:
        config = '[build]\nrustflags = ["-Ztrust-verify=off"]\n'
        for pin in self.TRUST_SPELLINGS:
            with self.subTest(pin=pin):
                self.assertEqual(CHECKER.toolchain_channel(pin), "trust")
                self.assertTrue(any("disables verification" in issue
                                    for issue in CHECKER.policy_issues(pin, config)))

    def test_equivalent_toml_trust_pins_cannot_skip_the_canary(self) -> None:
        resolved = CHECKER.ResolvedToolchain(Path('/fixture/trustc'), None, None, None, None, None)
        with self.temporary_directory() as temporary:
            root = Path(temporary)
            for pin in self.TRUST_SPELLINGS:
                (root / 'rust-toolchain.toml').write_text(pin, encoding='utf-8')
                with self.subTest(pin=pin), self.clean_authority_environment(), \
                        mock.patch.object(CHECKER, 'resolve_installed', return_value=resolved) as resolve, \
                        mock.patch.object(CHECKER, 'resolved_issues', return_value=[]), \
                        mock.patch.object(CHECKER, 'behavioral_issues', return_value=['canary']) as canary:
                    self.assertEqual(CHECKER.check(root, False), ['canary'])
                    resolve.assert_called_once_with(root)
                    canary.assert_called_once_with(resolved.rustc)

    def test_only_the_toolchain_table_selects_the_repository_channel(self) -> None:
        pin = '[metadata]\nchannel = "trust"\n[toolchain]\nchannel = "stable"\n'
        self.assertEqual(CHECKER.toolchain_channel(pin), "stable")
        with self.temporary_directory() as temporary:
            root = Path(temporary)
            (root / 'rust-toolchain.toml').write_text(pin, encoding='utf-8')
            with mock.patch.object(CHECKER, 'resolve_installed', side_effect=AssertionError('upstream default')):
                self.assertEqual(CHECKER.check(root, False), [])
                self.assertTrue(CHECKER.check(root, True))

    def test_absent_or_path_only_pin_stays_unverified_without_resolution(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary)
            path = root / 'rust-toolchain.toml'
            for pin in (None, '', '[toolchain]\npath = "/fixture/custom"\n'):
                if pin is not None:
                    path.write_text(pin, encoding='utf-8')
                with self.subTest(pin=pin), \
                        mock.patch.object(CHECKER, 'resolve_installed', side_effect=AssertionError('unverified default')):
                    self.assertEqual(CHECKER.check(root, False), [])
                    self.assertTrue(CHECKER.check(root, True))

    def test_malformed_toolchain_toml_never_becomes_an_unverified_pass(self) -> None:
        malformed = ('[toolchain\nchannel="trust"',
                     '[toolchain]\nchannel="trust"\nchannel="stable"\n',
                     'toolchain = true\n', '[toolchain]\nchannel = ["trust"]\n',
                     '[toolchain]\nchannel = 4\n', 'channel = "trust"\n')
        with self.temporary_directory() as temporary:
            root = Path(temporary)
            for pin in malformed:
                (root / 'rust-toolchain.toml').write_text(pin, encoding='utf-8')
                with self.subTest(pin=pin), \
                        mock.patch.object(CHECKER, 'resolve_installed', side_effect=AssertionError('malformed pin')):
                    self.assertTrue(CHECKER.policy_issues(pin, ''))
                    self.assertTrue(CHECKER.check(root, False))
                    code, out, err = self.run_main(root, [])
                    self.assertEqual(code, 1)
                    self.assertNotIn('PASS:', out)
                    self.assertIn('invalid rust-toolchain.toml', err)

    def test_vendored_parser_keeps_the_bootstrap_import_path(self) -> None:
        import_module = builtins.__import__
        def without_stdlib(name, *args, **kwargs):
            if name == 'tomllib':
                raise ModuleNotFoundError('forced old-Python parser path', name=name)
            return import_module(name, *args, **kwargs)
        name = 'authority_vendored_parser_control'
        spec = importlib.util.spec_from_file_location(name, CHECKER_PATH)
        module = importlib.util.module_from_spec(spec)
        try:
            sys.modules[name] = module
            with mock.patch.object(sys, 'path', [str(ROOT / 'scripts'), *sys.path]), \
                    mock.patch.object(builtins, '__import__', side_effect=without_stdlib):
                spec.loader.exec_module(module)
            self.assertEqual(module.tomllib.__name__, '_vendor.tomli')
            for pin in self.TRUST_SPELLINGS:
                self.assertEqual(module.toolchain_channel(pin), 'trust')
        finally:
            sys.modules.pop(name, None)

    def test_advisory_is_the_ramp_and_is_refused_at_the_destination(self) -> None:
        # THE WHOLE POINT OF THE TWO BARS. Advisory is accepted as a ramp
        # position because it is the only rung that exists today — strict fails
        # on Trust's own four-line README example — but it is REFUSED under
        # --require-verified-default, which is the "all batteries included"
        # destination and does not move. If this test ever passes advisory at
        # the destination, the destination has been given away.
        config = '[target.any]\nrustflags = ["-Ztrust-policy=advisory"]\n'
        self.assertEqual(CHECKER.policy_issues(self.TRUST, config), [])
        destination = CHECKER.policy_issues(self.TRUST, config, None, destination=True)
        self.assertTrue(any("not strict or certify" in issue for issue in destination))

    def test_split_flags_and_every_non_authoritative_policy_are_rejected(self) -> None:
        for config in (
            '[target.any]\nrustflags = ["-Z", "trust-verify=off"]\n',
            '[target.any]\nrustflags = ["-Z", "trust-policy=memory-safe"]\n',
            '[target.any]\nrustflags = ["-Ztrust-policy=unknown"]\n',
        ):
            with self.subTest(config=config):
                self.assertTrue(CHECKER.policy_issues(self.TRUST, config))

    def test_strict_and_certify_are_the_only_explicit_policies(self) -> None:
        for policy in ("strict", "certify"):
            config = f'[target.any]\nrustflags = ["-Z", "trust-policy={policy}"]\n'
            with self.subTest(policy=policy):
                self.assertEqual(CHECKER.policy_issues(self.TRUST, config), [])

    def test_the_destination_must_name_a_strict_policy_explicitly(self) -> None:
        config = '[target.any]\nrustflags = []\n'
        issues = CHECKER.policy_issues(self.TRUST, config, None, destination=True)
        self.assertTrue(any("must explicitly select a Trust policy" in i for i in issues))

    def test_an_absent_policy_on_the_ramp_is_left_to_the_behavioral_canary(self) -> None:
        # The Targo lane, not Cargo config, selects the policy a verified run
        # obeys (measured on 321aaeda7: `targo trust check` ran strict over a
        # configured advisory). With no configured policy the pin gets the
        # compiler default, and check() never passes without the canary proving
        # that default refutation-fatal. What the ramp may NOT do is carry an
        # off-switch or an unknown/ambiguous policy — those stay refused.
        self.assertEqual(CHECKER.policy_issues(self.TRUST, "", None), [])
        for config in (
            '[build]\nrustflags = ["-Ztrust-verify=off"]\n',
            '[build]\nrustflags = ["-Ztrust-policy=memory-safe"]\n',
            '[build]\nrustflags = ["-Ztrust-policy=strict", "-Ztrust-policy=advisory"]\n',
        ):
            with self.subTest(config=config):
                self.assertTrue(CHECKER.policy_issues(self.TRUST, config, None))

    def test_check_runs_the_canary_before_passing_a_policy_less_trust_pin(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary)
            (root / "rust-toolchain.toml").write_text(self.TRUST, encoding="utf-8")
            seen = []
            resolved = CHECKER.ResolvedToolchain(
                Path("/rustc"), None, None, None, None, None, None
            )
            original = (
                CHECKER.resolve_installed, CHECKER.resolved_issues, CHECKER.behavioral_issues
            )
            try:
                CHECKER.resolve_installed = lambda _root: resolved
                CHECKER.resolved_issues = lambda _resolved, require_seal=False: []
                CHECKER.behavioral_issues = lambda rustc: seen.append(rustc) or ["canary"]
                with self.clean_authority_environment():
                    self.assertEqual(CHECKER.check(root, False), ["canary"])
            finally:
                (
                    CHECKER.resolve_installed,
                    CHECKER.resolved_issues,
                    CHECKER.behavioral_issues,
                ) = original
            self.assertEqual(seen, [Path("/rustc")])

    def test_rustc_wrappers_and_alternate_compilers_are_rejected(self) -> None:
        for config in (
            '[build]\nrustc-wrapper = "/tmp/wrapper"\n',
            '[build]\nrustc-workspace-wrapper = "/tmp/wrapper"\n',
            '[build]\nrustc = "/tmp/rustc"\n',
            'build.rustc = "/tmp/rustc"\n',
            '[env]\nRUSTC = "/tmp/rustc"\n',
            '[env]\nRUSTC_WRAPPER = "/tmp/wrapper"\n',
            '[env]\nRUSTC_WORKSPACE_WRAPPER = "/tmp/wrapper"\n',
            '[env]\nCARGO_BUILD_RUSTC = "/tmp/rustc"\n',
            '[env]\n"RUSTC\\u005fWRAPPER" = "/tmp/wrapper"\n',
        ):
            with self.subTest(config=config):
                issues = CHECKER.policy_issues(self.TRUST, config)
                self.assertTrue(any("wrapper or alternate rustc" in issue for issue in issues))

    def test_env_inline_and_encoded_trust_flags_are_rejected(self) -> None:
        configs = (
            '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
            '[env]\nRUSTFLAGS = "-Z trust-verify=off"\n',
            '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
            '[env]\nRUSTDOCFLAGS = { value = "-Ztrust-policy=advisory", force = true }\n',
            '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
            '[env]\nCARGO_ENCODED_RUSTFLAGS = "-Z\\u001ftrust-verify=off"\n',
            '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
            '[env]\nRUSTFLAGS = "\\u002dZtrust-policy=memory-safe"\n',
        )
        for config in configs:
            with self.subTest(config=config):
                # Assert the flag is REFUSED, not how the refusal is worded: a
                # DIFFERENT policy smuggled through [env] is ambiguous whichever
                # value it names, an off-switch is refused as one, and that
                # must hold on the ramp too — ambience is a separate concern
                # from strictness.
                self.assertTrue(CHECKER.policy_issues(self.TRUST, config))
                self.assertTrue(
                    CHECKER.policy_issues(self.TRUST, config, None, destination=True)
                )

    # ay's live Trust block (~/ay/.cargo/config.toml, 2026-09-29): the SAME
    # certify policy and hardening knobs repeated for the host unit, the target
    # units and rustdoc.
    AY_FLAGS = (
        '["-Ztrust-verify=on", "-Ztrust-policy=certify", "-Ztrust-verify-level=2", '
        '"-Ztrust-verify-profile=unix_hardened", "-Ztrust-verify-include-dependencies=yes", '
        '"-Ztrust-ir-lower=strict"]'
    )
    AY_CONFIG = (
        "target-applies-to-host = true\n"
        "[unstable]\ntarget-applies-to-host = true\nhost-config = true\n"
        f"[host]\nrustflags = {AY_FLAGS}\n"
        f"[target.'cfg(all())']\nrustflags = {AY_FLAGS}\nrustdocflags = {AY_FLAGS}\n"
    )

    def test_identical_policy_copies_across_units_are_one_policy(self) -> None:
        # RED before 2026-09-29: "multiple Trust policies make the authority
        # claim ambiguous" (three copies of ONE value) plus nine "disables
        # verification" for the -Ztrust-verify-* knobs.
        self.assertEqual(CHECKER.policy_issues(self.TRUST, self.AY_CONFIG), [])
        self.assertEqual(
            CHECKER.policy_issues(self.TRUST, self.AY_CONFIG, None, destination=True), []
        )

    def test_genuinely_different_policies_stay_ambiguous_by_name(self) -> None:
        config = (
            '[host]\nrustflags = ["-Ztrust-policy=certify"]\n'
            '[target.any]\nrustflags = ["-Ztrust-policy=strict"]\n'
            'rustdocflags = ["-Ztrust-policy=certify"]\n'
        )
        for destination in (False, True):
            with self.subTest(destination=destination):
                issues = CHECKER.policy_issues(self.TRUST, config, None, destination=destination)
                self.assertIn(
                    "multiple distinct Trust policies make the authority claim ambiguous: "
                    "-Ztrust-policy=certify, -Ztrust-policy=strict",
                    issues,
                )

    def test_verify_knobs_are_not_activation_switches(self) -> None:
        # trustc: `-Ztrust-verify=` is "the sole verification activation
        # control". RED before 2026-09-29: any -Ztrust-verify-* was read as one.
        for knob in (
            "-Ztrust-verify-level=2",
            "-Ztrust-verify-profile=unix_hardened",
            "-Ztrust-verify-include-dependencies=yes",
        ):
            config = f'[build]\nrustflags = ["-Ztrust-verify=on", "{knob}"]\n'
            with self.subTest(knob=knob):
                self.assertEqual(CHECKER.policy_issues(self.TRUST, config), [])

    def test_unaudited_trust_flags_are_refused_by_name(self) -> None:
        # The audit is a closed table. `mir-only:` skips solver dispatch and was
        # ACCEPTED before 2026-09-29 (RED); `ay-path` swaps the solver and was
        # refused only because its name shares the activation prefix.
        for flag in (
            "-Ztrust-dump=mir-only:/tmp/sink",
            "-Ztrust-verify-ay-path=/tmp/solver",
            "-Ztrust-verify-level=0",
            "-Ztrust-verify-profile=default",
            "-Ztrust-ir-lower=off",
            "-Ztrust-sat-perturb=enum-ctor",
        ):
            config = f'[build]\nrustflags = ["-Ztrust-policy=strict", "{flag}"]\n'
            for destination in (False, True):
                with self.subTest(flag=flag, destination=destination):
                    issues = CHECKER.policy_issues(
                        self.TRUST, config, None, destination=destination
                    )
                    self.assertTrue(
                        any(issue.startswith(f"unaudited Trust flag in a verified default: {flag} ")
                            for issue in issues),
                        issues,
                    )

    def test_an_activation_other_than_on_is_named(self) -> None:
        for flag in ("-Ztrust-verify=off", "-Ztrust-verify"):
            config = f'[build]\nrustflags = ["{flag}"]\n'
            with self.subTest(flag=flag):
                self.assertIn(
                    f"at least one host, target, or rustdoc unit disables verification: {flag}",
                    CHECKER.policy_issues(self.TRUST, config),
                )

    def test_the_destination_policy_demand_states_what_the_line_binds(self) -> None:
        # RED before 2026-09-29: the demand did not say that `targo trust`
        # ignores the line it demands (measured on 321aaeda7).
        issues = CHECKER.policy_issues(self.TRUST, "", None, destination=True)
        demand = [i for i in issues if "must explicitly select a Trust policy" in i]
        self.assertEqual(len(demand), 1, issues)
        self.assertIn("binds rustup-proxied builds only", demand[0])
        self.assertIn("`targo trust` ignores it", demand[0])

    def run_main(self, root: Path, verdict: list[str], *extra: str) -> tuple[int, str, str]:
        original = CHECKER.check
        stdout, stderr = io.StringIO(), io.StringIO()
        try:
            CHECKER.check = lambda _root, _require: list(verdict)
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                code = CHECKER.main(["--root", os.fspath(root), *extra])
        finally:
            CHECKER.check = original
        return code, stdout.getvalue(), stderr.getvalue()

    def test_a_configured_policy_is_printed_with_its_scope_whatever_the_verdict(self) -> None:
        # RED before 2026-09-29: main() printed PASS/FAIL and nothing about
        # the configured policy's reach.
        with self.temporary_directory() as temporary:
            root = Path(temporary)
            (root / "rust-toolchain.toml").write_text(self.TRUST, encoding="utf-8")
            (root / ".cargo").mkdir(mode=0o755)
            (root / ".cargo" / "config.toml").write_text(self.AY_CONFIG, encoding="utf-8")
            for verdict, code_expected in (([], 0), (["seal missing"], 1)):
                with self.subTest(verdict=verdict):
                    code, out, err = self.run_main(root, verdict)
                    self.assertEqual(code, code_expected)
                    self.assertIn(
                        "NOTE: configured -Ztrust-policy=certify: an explicit -Ztrust-policy "
                        "line binds rustup-proxied builds only",
                        out,
                    )
                    self.assertIn("`targo trust` ignores it", out)
            # No configured policy, nothing claimed about one.
            (root / ".cargo" / "config.toml").write_text("", encoding="utf-8")
            _, out, _ = self.run_main(root, [])
            self.assertNotIn("binds rustup-proxied builds only", out)

    def test_comments_cannot_inject_or_hide_trust_flags(self) -> None:
        config = (
            '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
            '# RUSTFLAGS = "-Ztrust-verify=off"\n'
        )
        self.assertEqual(CHECKER.policy_issues(self.TRUST, config), [])

    def test_ambient_flags_and_compiler_overrides_are_rejected(self) -> None:
        config = '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
        environments = (
            {"RUSTC_WRAPPER": "/tmp/wrapper"},
            {"CARGO_TARGET_TEST_HOST_RUSTFLAGS": "-Ztrust-verify=off"},
            {"CARGO_ENCODED_RUSTFLAGS": "-Z\x1ftrust-policy=advisory"},
        )
        for environment in environments:
            with self.subTest(environment=environment):
                self.assertTrue(CHECKER.policy_issues(self.TRUST, config, environment))

    def test_legacy_and_ambiguous_cargo_configuration_fail_closed(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary)
            (root / "rust-toolchain.toml").write_text(self.TRUST, encoding="utf-8")
            cargo = root / ".cargo"
            cargo.mkdir(mode=0o755)
            legacy = cargo / "config"
            # The legacy spelling is still read by Cargo, so it is audited: an
            # off-switch there is refused like one in config.toml. (This half
            # used to assert only "some issue", which the installed toolchain
            # supplied by failing the seal; on a machine whose toolchain passes
            # the ramp it proved nothing about the legacy file.)
            legacy.write_text(
                '[build]\nrustflags = ["-Ztrust-verify=off"]\n', encoding="utf-8"
            )
            issues = CHECKER.check(root, False)
            self.assertTrue(any("disables verification" in issue for issue in issues), issues)

            (cargo / "config.toml").write_text(
                '[build]\nrustflags = ["-Ztrust-policy=strict"]\n', encoding="utf-8"
            )
            issues = CHECKER.check(root, False)
            self.assertTrue(any("precedence is ambiguous" in issue for issue in issues))

    def test_rustdoc_and_host_opt_outs_are_rejected(self) -> None:
        for config in (
            '[target.any]\nrustdocflags = ["-Ztrust-verify=off"]\n',
            '[host]\nrustflags = ["-Ztrust-verify=off"]\n',
        ):
            with self.subTest(config=config):
                self.assertTrue(CHECKER.policy_issues(self.TRUST, config))

    HOST = "test-host"

    def populate(self, root: Path, *, sealed: bool) -> Path:
        rustc = root / "bin" / "rustc"
        rustc.parent.mkdir(parents=True)
        rustc.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        for launcher in ("targo", "trustc"):
            (root / "bin" / launcher).write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        std = root / "lib" / "rustlib" / self.HOST / "lib" / "libstd-test.rlib"
        std.parent.mkdir(parents=True)
        std.write_bytes(b"std")
        driver = root / "lib" / "librustc_driver-test.dylib"
        driver.write_bytes(b"driver")
        executable, data = (0o555, 0o444) if sealed else (0o755, 0o644)
        for artifact in root.rglob("*"):
            runnable = artifact.is_dir() or artifact.parent == root / "bin"
            artifact.chmod(executable if runnable else data)
        root.chmod(executable)
        return rustc

    def lane(self, sysroot: Path, commit_hash: str = COMMIT, *, discriminated: bool = True) -> object:
        return CHECKER.LaneToolchain(
            sysroot / "bin" / "targo",
            discriminated,
            sysroot / "bin" / "trustc",
            sysroot,
            commit_hash,
        )

    def resolved(self, root: Path, commit_hash: str = COMMIT) -> object:
        """A complete SEALED toolchain: pin, lane and seal all name ``root``."""
        rustc = self.populate(root, sealed=True)
        return CHECKER.ResolvedToolchain(
            rustc, root, root, root, self.HOST, commit_hash, self.lane(root, commit_hash)
        )

    def caller_owned(self, root: Path, commit_hash: str = COMMIT, lane: object = None) -> object:
        """A complete RAMP toolchain: owner-writable, no seal named."""
        rustc = self.populate(root, sealed=False)
        return CHECKER.ResolvedToolchain(
            rustc, root, root, None, self.HOST, commit_hash,
            self.lane(root, commit_hash) if lane is None else lane,
        )

    def test_complete_read_only_sysroot_is_accepted(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary) / f"trust-{self.COMMIT}"
            root.mkdir(mode=0o755)
            resolved = self.resolved(root)
            self.assertEqual(CHECKER.resolved_issues(resolved), [])

    def test_missing_rustc_and_sysroot_fail_closed(self) -> None:
        missing = CHECKER.ResolvedToolchain(None, None, None, None, None, None)
        issues = CHECKER.resolved_issues(missing)
        self.assertTrue(any("rustc" in issue for issue in issues))
        self.assertTrue(any("sysroot" in issue for issue in issues))

    def test_mutable_build_trees_are_rejected_in_both_tiers(self) -> None:
        for relative in (
            "build/host/stage2", "build/aarch64-apple-darwin/stage1",
            "build.noindex/host/stage2", "build.noindex/aarch64-apple-darwin/stage1",
        ):
            for sealed in (True, False):
                with self.subTest(relative=relative, sealed=sealed), \
                        self.temporary_directory() as temporary:
                    tree = Path(temporary) / relative
                    self.protected_directory(tree)
                    resolved = self.resolved(tree) if sealed else self.caller_owned(tree)
                    issues = CHECKER.resolved_issues(resolved)
                    self.assertTrue(any("mutable x.py build tree" in issue for issue in issues))

    def test_logical_build_alias_cannot_hide_a_physical_noindex_stage(self) -> None:
        for sealed in (True, False):
            with self.subTest(sealed=sealed), self.temporary_directory() as temporary:
                base = Path(temporary)
                actual = base / "build.noindex" / self.HOST / "stage1"
                self.protected_directory(actual)
                if sealed:
                    self.resolved(actual)
                else:
                    self.caller_owned(actual)
                (base / "build").symlink_to(base / "build.noindex", target_is_directory=True)
                alias = base / "build" / self.HOST / "stage1"
                resolved = CHECKER.ResolvedToolchain(
                    alias / "bin" / "rustc", alias, alias, alias if sealed else None,
                    self.HOST, self.COMMIT, self.lane(alias),
                )
                issues = CHECKER.resolved_issues(resolved)
                self.assertTrue(any("mutable x.py build tree" in issue for issue in issues), issues)

    def test_similarly_named_directory_is_not_classified_as_a_build_tree(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary) / "build.noindex-tools" / self.HOST / "stage1"
            self.protected_directory(root)
            self.assertEqual(CHECKER.resolved_issues(self.caller_owned(root)), [])

    def test_commit_hash_must_match_the_canonical_directory_name(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary) / "trust-wrong"
            root.mkdir(mode=0o755)
            issues = CHECKER.resolved_issues(self.resolved(root))
            self.assertTrue(any("directory must be named" in issue for issue in issues))

    def test_writable_nested_std_and_driver_artifacts_are_rejected(self) -> None:
        for relative in (
            Path("lib/rustlib/test-host/lib/libstd-test.rlib"),
            Path("lib/librustc_driver-test.dylib"),
        ):
            with self.subTest(relative=relative), self.temporary_directory() as temporary:
                root = Path(temporary) / f"trust-{self.COMMIT}"
                root.mkdir(mode=0o755)
                resolved = self.resolved(root)
                (root / relative).chmod(0o644)
                issues = CHECKER.resolved_issues(resolved)
                self.assertTrue(any("writable artifact" in issue for issue in issues))

    def test_nested_symlink_escape_is_rejected(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            root = base / f"trust-{self.COMMIT}"
            root.mkdir(mode=0o755)
            resolved = self.resolved(root)
            outside = base / "mutable-driver"
            outside.write_bytes(b"outside")
            lib = root / "lib"
            lib.chmod(0o755)
            (lib / "librustc_driver-escape.dylib").symlink_to(outside)
            lib.chmod(0o555)
            issues = CHECKER.resolved_issues(resolved)
            self.assertTrue(any("symlinked artifact" in issue for issue in issues))

    def fake_compiler(self, directory: Path, body: str) -> Path:
        compiler = directory / "rustc"
        compiler.write_text(f"#!/bin/sh\n{body}\n", encoding="utf-8")
        compiler.chmod(0o755)
        return compiler

    def test_behavioral_canary_requires_positive_and_refutation_evidence(self) -> None:
        with self.temporary_directory() as temporary:
            directory = Path(temporary)
            compiler = self.fake_compiler(
                directory,
                """
case "$*" in
  *positive.rs*) exit 0 ;;
  *refutation.rs*)
    echo 'note: Trust verification: 0 proved, 1 failed, 0 unknown' >&2
    echo 'note: [div-zero] FAILED; counterexample: y = 0' >&2
    exit 1 ;;
  *) exit 91 ;;
esac
""",
            )
            self.assertEqual(CHECKER.behavioral_issues(compiler), [])

    def test_behavioral_canary_rejects_acceptance_and_nontrust_errors(self) -> None:
        bodies = (
            "exit 0",
            "case \"$*\" in *positive.rs*) exit 0 ;; *) echo syntax-error >&2; exit 1 ;; esac",
        )
        for body in bodies:
            with self.subTest(body=body), self.temporary_directory() as temporary:
                compiler = self.fake_compiler(Path(temporary), body)
                self.assertTrue(CHECKER.behavioral_issues(compiler))

    def test_symlink_cannot_be_the_sealed_root(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            actual = base / f"trust-{self.COMMIT}"
            actual.mkdir(mode=0o755)
            resolved = self.resolved(actual)
            alias = base / "trust-current"
            alias.symlink_to(actual, target_is_directory=True)
            issues = CHECKER.resolved_issues(
                CHECKER.ResolvedToolchain(
                    resolved.rustc,
                    resolved.sysroot,
                    alias,
                    alias,
                    resolved.host,
                    resolved.commit_hash,
                    resolved.lane,
                )
            )
            self.assertTrue(any("must be a versioned directory" in issue for issue in issues))

    def test_seal_named_by_the_short_prefix_the_producer_writes_is_accepted(self) -> None:
        # trust's `scripts/promote-toolchain.sh` seals to `trust-${REV:0:8}`, and
        # every artifact under ~/toolchains is that shape (trust-1979a7b8,
        # trust-6500fd4d). Demanding the full 40 hex made this clause impossible
        # to satisfy against a real promoted seal.
        with self.temporary_directory() as temporary:
            root = Path(temporary) / f"trust-{self.COMMIT[:8]}"
            root.mkdir(mode=0o755)
            issues = CHECKER.resolved_issues(self.resolved(root))
            self.assertFalse(
                any("must be named" in issue for issue in issues),
                f"8-hex seal name was rejected: {issues}",
            )

    def test_seal_name_must_still_be_a_prefix_of_the_reported_commit(self) -> None:
        # The relaxation is a PREFIX rule, not "any name": a seal must still name
        # the commit its compiler reports, so one cannot be relabelled to
        # impersonate another revision.
        with self.temporary_directory() as temporary:
            root = Path(temporary) / "trust-deadbeef"
            root.mkdir(mode=0o755)
            issues = CHECKER.resolved_issues(self.resolved(root))
            self.assertTrue(any("must be named" in issue for issue in issues))

    def test_seal_name_prefix_must_be_long_enough_to_mean_something(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary) / f"trust-{self.COMMIT[:4]}"
            root.mkdir(mode=0o755)
            issues = CHECKER.resolved_issues(self.resolved(root))
            self.assertTrue(any("must be named" in issue for issue in issues))


    # --- The RAMP tier: caller-owned, one compiler across pin and lane --------

    def test_caller_owned_toolchain_is_accepted_on_the_ramp(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary) / "9192"
            root.mkdir(mode=0o755)
            self.assertEqual(CHECKER.resolved_issues(self.caller_owned(root)), [])

    def test_the_destination_still_demands_a_named_seal(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary) / "9192"
            root.mkdir(mode=0o755)
            issues = CHECKER.resolved_issues(self.caller_owned(root), require_seal=True)
            self.assertTrue(any("TRUST_SEALED_SYSROOT" in issue for issue in issues))

    def test_a_named_seal_is_held_to_the_sealed_tier_even_on_the_ramp(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary) / f"trust-{self.COMMIT}"
            root.mkdir(mode=0o755)
            resolved = self.caller_owned(root)
            named = CHECKER.ResolvedToolchain(
                resolved.rustc, resolved.sysroot, resolved.rustup_link, root,
                resolved.host, resolved.commit_hash, resolved.lane,
            )
            issues = CHECKER.resolved_issues(named)
            self.assertTrue(any("writable artifact" in issue for issue in issues))

    def test_foreign_writable_artifacts_are_rejected_on_the_ramp(self) -> None:
        for relative in (
            Path("."),
            Path("lib/librustc_driver-test.dylib"),
            Path("lib/rustlib/test-host/lib/libstd-test.rlib"),
        ):
            for mode in (0o664, 0o646):
                with self.subTest(relative=relative, mode=oct(mode)), \
                        self.temporary_directory() as temporary:
                    root = Path(temporary) / "9192"
                    root.mkdir(mode=0o755)
                    resolved = self.caller_owned(root)
                    target = root / relative
                    target.chmod(mode | (0o111 if target.is_dir() else 0))
                    issues = CHECKER.resolved_issues(resolved)
                    self.assertTrue(
                        any("another principal can write" in issue for issue in issues), issues
                    )

    def test_symlinked_artifacts_are_rejected_on_the_ramp(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            root = base / "9192"
            root.mkdir(mode=0o755)
            resolved = self.caller_owned(root)
            outside = base / "substitute-driver"
            outside.write_bytes(b"outside")
            (root / "lib" / "librustc_driver-escape.dylib").symlink_to(outside)
            issues = CHECKER.resolved_issues(resolved)
            self.assertTrue(any("symlinked artifact" in issue for issue in issues))

    def test_pin_and_lane_must_be_one_compiler(self) -> None:
        other = "f" * 40
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            pinned = base / "pinned"
            lane_root = base / "lane"
            pinned.mkdir(mode=0o755)
            lane_root.mkdir(mode=0o755)
            self.populate(lane_root, sealed=False)
            resolved = self.caller_owned(pinned, lane=self.lane(lane_root, other))
            issues = CHECKER.resolved_issues(resolved)
            self.assertTrue(any("must be one compiler" in issue for issue in issues))

            (base / "again").mkdir(mode=0o755)
            same = self.caller_owned(base / "again", lane=self.lane(lane_root))
            self.assertEqual(CHECKER.resolved_issues(same), [])

    def test_a_separate_lane_tree_is_held_to_the_same_tier(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            pinned = base / "pinned"
            lane_root = base / "lane"
            pinned.mkdir(mode=0o755)
            lane_root.mkdir(mode=0o755)
            self.populate(lane_root, sealed=False)
            (lane_root / "lib" / "librustc_driver-test.dylib").chmod(0o666)
            resolved = self.caller_owned(pinned, lane=self.lane(lane_root))
            issues = CHECKER.resolved_issues(resolved)
            self.assertTrue(any("Targo lane sysroot" in issue for issue in issues), issues)

    def test_the_sealed_tier_requires_the_lane_inside_the_seal(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            root = base / f"trust-{self.COMMIT}"
            lane_root = base / "lane"
            root.mkdir(mode=0o755)
            lane_root.mkdir(mode=0o755)
            self.populate(lane_root, sealed=True)
            resolved = self.resolved(root)
            split = CHECKER.ResolvedToolchain(
                resolved.rustc, resolved.sysroot, resolved.rustup_link, resolved.sealed_root,
                resolved.host, resolved.commit_hash, self.lane(lane_root),
            )
            issues = CHECKER.resolved_issues(split)
            self.assertTrue(any("lane's trustc sysroot is not" in issue for issue in issues))

    def test_an_undiscriminated_or_missing_targo_fails_closed(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary) / "9192"
            root.mkdir(mode=0o755)
            resolved = self.caller_owned(root, lane=self.lane(root, discriminated=False))
            issues = CHECKER.resolved_issues(resolved)
            self.assertTrue(any("not Trust's targo" in issue for issue in issues))
            for lane in (None, CHECKER.LaneToolchain(None, False, None, None, None)):
                with self.subTest(lane=lane):
                    missing = CHECKER.ResolvedToolchain(
                        resolved.rustc, resolved.sysroot, resolved.rustup_link, None,
                        resolved.host, resolved.commit_hash, lane,
                    )
                    issues = CHECKER.resolved_issues(missing)
                    self.assertTrue(any("Trust targo was not found" in issue for issue in issues))

    def test_a_foreign_writable_lane_launcher_is_rejected(self) -> None:
        for launcher in ("targo", "trustc"):
            with self.subTest(launcher=launcher), self.temporary_directory() as temporary:
                base = Path(temporary)
                pinned = base / "pinned"
                shims = base / "shims"
                pinned.mkdir(mode=0o755)
                shims.mkdir(mode=0o755)
                for name in ("targo", "trustc"):
                    (shims / name).write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                    (shims / name).chmod(0o755)
                resolved = self.caller_owned(pinned)
                lane = CHECKER.LaneToolchain(
                    shims / "targo", True, shims / "trustc", pinned, self.COMMIT
                )
                clean = CHECKER.ResolvedToolchain(
                    resolved.rustc, resolved.sysroot, resolved.rustup_link, None,
                    resolved.host, resolved.commit_hash, lane,
                )
                self.assertEqual(CHECKER.resolved_issues(clean), [])
                (shims / launcher).chmod(0o777)
                issues = CHECKER.resolved_issues(clean)
                self.assertTrue(any(f"lane's {launcher} launcher" in issue for issue in issues))
                (shims / launcher).chmod(0o755)
                shims.chmod(0o777)
                issues = CHECKER.resolved_issues(clean)
                self.assertTrue(any("launcher" in issue for issue in issues))
                shims.chmod(0o755)

    def symlinked_lane(self, base: Path, launcher: str, link_target: Path) -> object:
        """A caller-owned RAMP toolchain whose ``launcher`` is a symlink to
        ``link_target`` (the other launcher stays a regular file)."""
        pinned = base / "pinned"
        shims = base / "shims"
        pinned.mkdir(mode=0o755)
        shims.mkdir(mode=0o755)
        for name in ("targo", "trustc"):
            if name == launcher:
                (shims / name).symlink_to(link_target)
            else:
                (shims / name).write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                (shims / name).chmod(0o755)
        resolved = self.caller_owned(pinned)
        lane = CHECKER.LaneToolchain(shims / "targo", True, shims / "trustc", pinned, self.COMMIT)
        return CHECKER.ResolvedToolchain(
            resolved.rustc, resolved.sysroot, resolved.rustup_link, None,
            resolved.host, resolved.commit_hash, lane,
        )

    @staticmethod
    def executable(path: Path, mode: int = 0o755) -> Path:
        TrustDefaultAuthorityTests.protected_directory(path.parent)
        path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        path.chmod(mode)
        return path

    def test_a_symlinked_launcher_is_followed_to_the_file_that_runs(self) -> None:
        # A caller-owned link is not a caller-owned launcher: `_is_caller_owned`
        # reads the LINK (lstat), so the target and its directory must be held
        # to the same bar, or the ramp's substitute for a seal has a hole.
        for launcher in ("targo", "trustc"):
            with self.subTest(launcher=launcher, case="clean target"), self.temporary_directory() as temporary:
                base = Path(temporary)
                real = self.executable(base / "store" / "bin" / launcher)
                resolved = self.symlinked_lane(base, launcher, real)
                self.assertEqual(CHECKER.resolved_issues(resolved), [])

            with self.subTest(launcher=launcher, case="0777 target"), self.temporary_directory() as temporary:
                base = Path(temporary)
                real = self.executable(base / "store" / "bin" / launcher, 0o777)
                resolved = self.symlinked_lane(base, launcher, real)
                link = resolved.lane.targo if launcher == "targo" else resolved.lane.rustc
                self.assertTrue(CHECKER._is_caller_owned(link))
                self.assertFalse(CHECKER._is_caller_owned(real))
                issues = CHECKER.resolved_issues(resolved)
                self.assertTrue(any(f"lane's {launcher} launcher" in issue for issue in issues), issues)

            with self.subTest(launcher=launcher, case="target in a 0777 directory"), self.temporary_directory() as temporary:
                base = Path(temporary)
                real = self.executable(base / "drop" / launcher)
                (base / "drop").chmod(0o777)
                try:
                    resolved = self.symlinked_lane(base, launcher, real)
                    issues = CHECKER.resolved_issues(resolved)
                    self.assertTrue(any(f"lane's {launcher} launcher" in issue for issue in issues), issues)
                finally:
                    (base / "drop").chmod(0o755)

            with self.subTest(launcher=launcher, case="relative multi-hop into a 0777 file"), self.temporary_directory() as temporary:
                base = Path(temporary)
                real = self.executable(base / "store" / "bin" / launcher, 0o777)
                hop = base / "store" / "current"
                hop.symlink_to(Path("bin") / launcher)
                resolved = self.symlinked_lane(base, launcher, Path("..") / "store" / "current")
                issues = CHECKER.resolved_issues(resolved)
                self.assertTrue(any(f"lane's {launcher} launcher" in issue for issue in issues), issues)

            with self.subTest(launcher=launcher, case="dangling or looping link"), self.temporary_directory() as temporary:
                base = Path(temporary)
                resolved = self.symlinked_lane(base, launcher, base / "shims" / launcher)
                issues = CHECKER.resolved_issues(resolved)
                self.assertTrue(any(f"lane's {launcher} launcher" in issue for issue in issues), issues)

    def test_a_launcher_under_a_symlinked_foreign_writable_directory_is_rejected(self) -> None:
        # The launcher's own name is a regular file, but its directory is a
        # caller-owned link into a directory another principal can write.
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            pinned = base / "pinned"
            pinned.mkdir(mode=0o755)
            drop = base / "drop"
            for name in ("targo", "trustc"):
                self.executable(drop / name)
            drop.chmod(0o777)
            try:
                shims = base / "shims"
                shims.symlink_to(drop)
                resolved = self.caller_owned(pinned)
                lane = CHECKER.LaneToolchain(shims / "targo", True, shims / "trustc", pinned, self.COMMIT)
                redirected = CHECKER.ResolvedToolchain(
                    resolved.rustc, resolved.sysroot, resolved.rustup_link, None,
                    resolved.host, resolved.commit_hash, lane,
                )
                issues = CHECKER.resolved_issues(redirected)
                self.assertTrue(any("lane's targo launcher" in issue for issue in issues), issues)
                self.assertTrue(any("lane's trustc launcher" in issue for issue in issues), issues)
            finally:
                drop.chmod(0o755)

    def test_a_launcher_grandparent_cannot_replace_a_protected_subtree(self) -> None:
        for launcher in ("targo", "trustc"):
            with self.subTest(launcher=launcher), self.temporary_directory() as temporary:
                base = Path(temporary)
                real = self.executable(base / "drop" / "protected" / "bin" / launcher)
                resolved = self.symlinked_lane(base, launcher, real)
                self.assertEqual(CHECKER.resolved_issues(resolved), [])
                (base / "drop").chmod(0o777)
                issues = CHECKER.resolved_issues(resolved)
                self.assertTrue(any(f"lane's {launcher} launcher" in i for i in issues), issues)

    def test_a_read_only_seal_still_needs_protected_replacement_ancestors(self) -> None:
        for sealed in (False, True):
            with self.subTest(sealed=sealed), self.temporary_directory() as temporary:
                base = Path(temporary)
                drop = base / "drop"
                drop.mkdir(mode=0o755)
                root = drop / f"trust-{self.COMMIT}"
                root.mkdir(mode=0o755)
                resolved = self.resolved(root) if sealed else self.caller_owned(root)
                self.assertEqual(CHECKER.resolved_issues(resolved), [])
                drop.chmod(0o777)
                issues = CHECKER.resolved_issues(resolved)
                self.assertTrue(any("path is not protected" in i for i in issues), issues)

    def test_a_safe_target_does_not_hide_a_writable_lexical_grandparent(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            real = self.executable(base / "safe" / "bin" / "targo")
            lexical = base / "drop" / "protected"
            self.protected_directory(lexical)
            (base / "drop").chmod(0o755)
            (lexical / "current").symlink_to(real.parent)
            launch = lexical / "current" / real.name
            self.assertIsNone(CHECKER._launcher_issue("targo", launch))
            (base / "drop").chmod(0o777)
            self.assertIsNotNone(CHECKER._launcher_issue("targo", launch))

    def test_an_intermediate_link_target_cannot_hide_its_lexical_ancestor(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            real = self.executable(base / "safe" / "targo")
            drop = base / "drop"
            drop.mkdir(mode=0o755)
            (drop / "jump").symlink_to(real)
            launch = base / "launch"
            launch.symlink_to(Path("drop") / "jump")
            self.assertIsNone(CHECKER._launcher_issue("targo", launch))
            drop.chmod(0o777)
            self.assertIsNotNone(CHECKER._launcher_issue("targo", launch))

    def test_trusted_sticky_hierarchy_protects_trusted_entries(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            real = self.executable(base / "sticky" / "nested" / "targo")
            (base / "sticky").chmod(0o1777)
            (base / "sticky" / "nested").chmod(0o1777)
            self.assertIsNone(CHECKER._launcher_issue("targo", real))
            launch = base / "sticky" / "launch"
            launch.symlink_to(Path("nested") / "targo")
            self.assertIsNone(CHECKER._launcher_issue("targo", launch))
            real.chmod(0o777)
            self.assertIsNotNone(CHECKER._launcher_issue("targo", launch))

    def test_sticky_does_not_trust_a_foreign_directory_or_symlink_owner(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            real = self.executable(base / "sticky" / "nested" / "targo")
            (base / "sticky").chmod(0o1777)
            launch = base / "sticky" / "launch"
            launch.symlink_to(Path("nested") / "targo")
            original = Path.lstat
            for foreign in (base / "sticky", launch):
                def lstat(path, *args, **kwargs):
                    info = original(path, *args, **kwargs)
                    if path == foreign:
                        fields = list(info)
                        fields[4] = max(os.getuid(), 0) + 1
                        return os.stat_result(fields)
                    return info
                with self.subTest(foreign=foreign), mock.patch.object(Path, "lstat", lstat):
                    self.assertIsNotNone(CHECKER._launcher_issue("targo", launch))

    def test_root_owned_protected_ancestors_remain_trusted(self) -> None:
        with self.temporary_directory() as temporary:
            real = self.executable(Path(temporary) / "owned" / "targo")
            original = Path.lstat
            def lstat(path, *args, **kwargs):
                info = original(path, *args, **kwargs)
                if path == real.parent:
                    fields = list(info)
                    fields[4] = 0
                    return os.stat_result(fields)
                return info
            with mock.patch.object(Path, "lstat", lstat):
                self.assertIsNone(CHECKER._launcher_issue("targo", real))

    def test_dotdot_does_not_erase_an_unsafe_visited_directory(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            real = self.executable(base / "safe" / "targo")
            drop = base / "drop"
            drop.mkdir(mode=0o755)
            launch = drop / ".." / "safe" / "targo"
            self.assertIsNone(CHECKER._launcher_issue("targo", launch))
            drop.chmod(0o777)
            self.assertEqual(launch.resolve(), real)
            self.assertIsNotNone(CHECKER._launcher_issue("targo", launch))

    def test_unreadable_ancestor_and_changed_link_fail_closed(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            real = self.executable(base / "protected" / "targo")
            original = Path.lstat
            def lstat(path, *args, **kwargs):
                if path == real.parent:
                    raise PermissionError("fixture ancestor refused")
                return original(path, *args, **kwargs)
            with mock.patch.object(Path, "lstat", lstat):
                self.assertIsNotNone(CHECKER._replacement_path_issue(real))
            launch = base / "launch"
            launch.symlink_to(real)
            readlink = os.readlink
            def replace(path, *args, **kwargs):
                target = readlink(path, *args, **kwargs)
                if path == launch:
                    launch.unlink()
                    launch.symlink_to(base / "absent")
                return target
            with mock.patch.object(os, "readlink", replace):
                self.assertIsNotNone(CHECKER._replacement_path_issue(launch))

    def test_clean_canary_environment_preserves_unrelated_values_and_restores_flags(self) -> None:
        values = {"RUSTC": "/fixture/compiler", "CARGO_BUILD_RUSTFLAGS": "-Ztrust-verify=off",
                  "RUSTDOCFLAGS": "-Ztrust-policy=advisory", "FIXTURE_UNRELATED": "kept"}
        with self.environment(**values):
            with self.clean_authority_environment():
                self.assertNotIn("RUSTC", os.environ)
                self.assertNotIn("CARGO_BUILD_RUSTFLAGS", os.environ)
                self.assertNotIn("RUSTDOCFLAGS", os.environ)
                self.assertEqual(os.environ["FIXTURE_UNRELATED"], "kept")
            for key, value in values.items():
                self.assertEqual(os.environ[key], value)

    def test_check_rejects_each_ambient_compiler_override_before_resolution(self) -> None:
        with self.temporary_directory() as temporary:
            root = Path(temporary)
            (root / "rust-toolchain.toml").write_text(self.TRUST, encoding="utf-8")
            with self.clean_authority_environment():
                for key in CHECKER.AMBIENT_RUSTC_OVERRIDES:
                    with self.subTest(key=key), self.environment(**{key: "/fixture/foreign-trustc"}):
                        with mock.patch.object(CHECKER, "resolve_installed", side_effect=AssertionError("must refuse before resolution")):
                            issues = CHECKER.check(root, False)
                        self.assertTrue(any("ambient rustc override" in i for i in issues), issues)

    def fake_targo(self, directory: Path, *, accepts_unverified: bool) -> Path:
        targo = directory / "targo"
        rejection = "" if accepts_unverified else (
            'case "$1" in --unverified) echo "error: unexpected argument" >&2; exit 2;; esac\n'
        )
        targo.write_text(f"#!/bin/sh\n{rejection}echo targo 0.0.0\n", encoding="utf-8")
        targo.chmod(0o755)
        trustc = directory / "trustc"
        trustc.write_text(
            "#!/bin/sh\n"
            'case "$*" in\n'
            f'  *sysroot*) echo "{directory}" ;;\n'
            f'  *) printf "commit-hash: {self.COMMIT}\\nhost: {self.HOST}\\n" ;;\n'
            "esac\n",
            encoding="utf-8",
        )
        trustc.chmod(0o755)
        return targo

    def test_resolve_lane_discriminates_targo_from_upstream_cargo(self) -> None:
        for accepts in (True, False):
            with self.subTest(accepts=accepts), self.temporary_directory() as temporary:
                directory = Path(temporary)
                targo = self.fake_targo(directory, accepts_unverified=accepts)
                previous = os.environ.get("TRUST_TARGO_BIN")
                os.environ["TRUST_TARGO_BIN"] = os.fspath(targo)
                try:
                    lane = CHECKER.resolve_lane(directory)
                finally:
                    if previous is None:
                        del os.environ["TRUST_TARGO_BIN"]
                    else:
                        os.environ["TRUST_TARGO_BIN"] = previous
                self.assertEqual(lane.targo, targo)
                self.assertEqual(lane.discriminated, accepts)
                self.assertEqual(lane.commit_hash, self.COMMIT)
                self.assertEqual(lane.sysroot, directory)

    @contextlib.contextmanager
    def clean_authority_environment(self) -> Iterator[None]:
        # Isolate the mocked canary assertion, not production policy. Preserve
        # unrelated environment and restore every removed value on exit.
        relevant = {
            key: None for key in os.environ
            if key in CHECKER.AMBIENT_RUSTC_OVERRIDES
            or key in {"RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS"}
            or (key.startswith("CARGO_") and key.endswith(("_RUSTFLAGS", "_RUSTDOCFLAGS")))
        }
        with self.environment(**relevant):
            yield

    @contextlib.contextmanager
    def environment(self, **values: Optional[str]) -> Iterator[None]:
        saved = {key: os.environ.get(key) for key in values}
        try:
            for key, value in values.items():
                if value is None:
                    os.environ.pop(key, None)
                else:
                    os.environ[key] = value
            yield
        finally:
            for key, value in saved.items():
                if value is None:
                    os.environ.pop(key, None)
                else:
                    os.environ[key] = value

    def fake_rustup(self, bin_directory: Path, toolchain: Path) -> Path:
        """A rustup that resolves ``which --toolchain trust rustc`` to a fake
        rustc inside ``toolchain`` reporting COMMIT and HOST."""
        rustc = toolchain / "bin" / "rustc"
        self.protected_directory(rustc.parent)
        rustc.write_text(
            "#!/bin/sh\n"
            'case "$*" in\n'
            f'  *sysroot*) echo "{toolchain}" ;;\n'
            f'  *) printf "commit-hash: {self.COMMIT}\\nhost: {self.HOST}\\n" ;;\n'
            "esac\n",
            encoding="utf-8",
        )
        rustc.chmod(0o755)
        self.protected_directory(bin_directory)
        rustup = bin_directory / "rustup"
        rustup.write_text(
            "#!/bin/sh\n"
            f'[ "$*" = "which --toolchain trust rustc" ] && echo "{rustc}" && exit 0\n'
            "exit 1\n",
            encoding="utf-8",
        )
        rustup.chmod(0o755)
        return rustc

    def test_rustup_off_path_is_found_in_the_cargo_home(self) -> None:
        # RED before 2026-09-29: an agent shell spawned without ~/.cargo/bin on
        # PATH got four FAILs about rustc, sysroot, link and commit-hash when
        # the only fact was that `rustup` was not on PATH.
        for layout in ("CARGO_HOME", "~/.cargo"):
            with self.subTest(layout=layout), self.temporary_directory() as temporary:
                base = Path(temporary)
                empty_path = base / "empty-path"
                empty_path.mkdir(mode=0o755)
                home = base / "home"
                cargo_home = base / "cargo-home" if layout == "CARGO_HOME" else home / ".cargo"
                rustc = self.fake_rustup(cargo_home / "bin", base / "toolchain")
                with self.environment(
                    PATH=os.fspath(empty_path),
                    HOME=os.fspath(home),
                    CARGO_HOME=os.fspath(cargo_home) if layout == "CARGO_HOME" else None,
                    TRUST_TARGO_BIN=None,
                ):
                    resolved = CHECKER.resolve_installed(base)
                self.assertIsNone(resolved.resolution_error)
                self.assertEqual(resolved.rustc, rustc)
                self.assertEqual(resolved.commit_hash, self.COMMIT)
                self.assertEqual(resolved.host, self.HOST)

    def test_native_targo_needs_no_rustup_but_checks_the_real_companion(self) -> None:
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            installed = self.caller_owned(base / "native")
            lane = installed.lane
            verbose = f"host: {self.HOST}\ncommit-hash: {self.COMMIT}\n"
            def run(args, root):
                if Path(args[0]) == lane.targo:
                    return verbose
                self.assertEqual(Path(args[0]), lane.sysroot / "bin" / "trustc")
                return str(lane.sysroot) if args[-1] == "sysroot" else verbose
            with mock.patch.object(CHECKER, "resolve_lane", return_value=lane), \
                    mock.patch.object(CHECKER, "_resolve_rustup", side_effect=AssertionError("native must not need rustup")), \
                    mock.patch.object(CHECKER, "_run", side_effect=run):
                resolved = CHECKER.resolve_installed(base)
            self.assertTrue(resolved.native)
            self.assertIsNone(resolved.rustup_link)
            self.assertEqual(CHECKER.resolved_issues(resolved), [])
            bad_lane = CHECKER.LaneToolchain(lane.targo, True, lane.rustc, lane.sysroot, "f" * 40)
            from dataclasses import replace
            issues = CHECKER.resolved_issues(replace(resolved, lane=bad_lane))
            self.assertTrue(any("must be one compiler" in issue for issue in issues))
            def mismatched_frontend(args, root):
                if Path(args[0]) == lane.targo:
                    return "commit-hash: " + "f" * 40 + "\n"
                return run(args, root)
            with mock.patch.object(CHECKER, "resolve_lane", return_value=lane), \
                    mock.patch.object(CHECKER, "_run", side_effect=mismatched_frontend):
                mismatched = CHECKER.resolve_installed(base)
            self.assertTrue(any("one compiler commit" in issue for issue in CHECKER.resolved_issues(mismatched)))
            lane.targo.chmod(0o777)
            issues = CHECKER.resolved_issues(resolved)
            self.assertTrue(any("launcher" in issue or "replacement" in issue for issue in issues))

    def test_a_missing_rustup_is_one_plain_failure(self) -> None:
        # RED before 2026-09-29: four symptom FAILs, none naming the cause.
        with self.temporary_directory() as temporary:
            base = Path(temporary)
            (base / "empty-path").mkdir(mode=0o755)
            (base / "empty-cargo-home").mkdir(mode=0o755)
            (base / "home").mkdir(mode=0o755)
            with self.environment(
                PATH=os.fspath(base / "empty-path"),
                HOME=os.fspath(base / "home"),
                CARGO_HOME=os.fspath(base / "empty-cargo-home"),
                TRUST_TARGO_BIN=None,
            ):
                issues = CHECKER.resolved_issues(CHECKER.resolve_installed(base))
            self.assertEqual(issues[0], CHECKER.RUSTUP_NOT_FOUND)
            self.assertIn("rustup not found", issues[0])
            for symptom in (
                "did not resolve an executable Trust rustc",
                "did not resolve an existing sysroot",
                "toolchain link is missing",
                "canonical 40-hex commit-hash",
            ):
                self.assertFalse(any(symptom in issue for issue in issues), issues)
            # The lane is a separate question and is still answered.
            self.assertTrue(any("Trust targo was not found" in issue for issue in issues), issues)

    def test_resolve_lane_refuses_an_explicit_binary_not_named_targo(self) -> None:
        with self.temporary_directory() as temporary:
            directory = Path(temporary)
            cargo = directory / "cargo"
            cargo.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            cargo.chmod(0o755)
            previous = os.environ.get("TRUST_TARGO_BIN")
            os.environ["TRUST_TARGO_BIN"] = os.fspath(cargo)
            try:
                lane = CHECKER.resolve_lane(directory)
            finally:
                if previous is None:
                    del os.environ["TRUST_TARGO_BIN"]
                else:
                    os.environ["TRUST_TARGO_BIN"] = previous
            self.assertIsNone(lane.targo)

if __name__ == "__main__":
    unittest.main()
