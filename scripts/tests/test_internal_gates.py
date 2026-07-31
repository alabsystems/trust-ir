from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCANNER_PATH = ROOT / "scripts" / "check_no_ignored_rust.py"
RUN_TARGO = ROOT / "scripts" / "run-targo.sh"

SPEC = importlib.util.spec_from_file_location("check_no_ignored_rust", SCANNER_PATH)
assert SPEC is not None and SPEC.loader is not None
SCANNER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SCANNER
SPEC.loader.exec_module(SCANNER)


class IgnoreScannerTests(unittest.TestCase):
    def kinds(self, source: str) -> list[str]:
        return [finding.kind for finding in SCANNER.scan_source(source)]

    def test_simple_and_multiline_cfg_attr_are_rejected(self) -> None:
        source = """
#[ignore = "slow"]
fn direct() {}

# [
    cfg_attr(
        feature = "qualification",
        ignore
    )
]
fn conditional() {}
"""
        findings = SCANNER.scan_source(source)
        self.assertEqual([finding.line for finding in findings], [2, 5])
        self.assertTrue(all("attribute" in finding.kind for finding in findings))

    def test_inner_cfg_attr_is_rejected(self) -> None:
        findings = SCANNER.scan_source(
            '#![cfg_attr(not(feature = "qualification"), ignore = "deferred")]\n'
        )
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].line, 1)

    def test_comments_and_literals_are_not_live_attributes(self) -> None:
        source = r'''
// #[ignore]
/* #[
    cfg_attr(any(), ignore)
] */
const COOKED: &str = "#[ignore]";
const RAW: &str = r###"#[cfg_attr(any(), ignore)]"###;
fn lifetime<'ignore>(value: &'ignore str) -> &'ignore str { value }
'''
        self.assertEqual(self.kinds(source), [])

    def test_non_executing_rustdoc_fences_are_rejected(self) -> None:
        source = '''
/// ```rust,ignore
/// deferred();
/// ```
fn line_doc() {}

/** ```ignore
 * deferred();
 * ```
 */
fn block_doc() {}

#[doc = "```rust,ignore\\ndeferred();\\n```"]
fn attribute_doc() {}

#[cfg_attr(feature = "docs", doc = "```ignore\\ndeferred();\\n```")]
fn conditional_attribute_doc() {}

/// ```no_run
/// compiled_but_not_executed();
/// ```
fn no_run_doc() {}
'''
        findings = SCANNER.scan_source(source)
        self.assertEqual(
            [finding.kind for finding in findings],
            ["non-executing rustdoc example"] * 5,
        )

    def test_active_rustdoc_is_allowed(self) -> None:
        self.assertEqual(
            self.kinds("/// ```rust\n/// active_and_executed();\n/// ```\nfn f() {}\n"),
            [],
        )

    def test_cli_scans_untracked_git_visible_rust_sources(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(["git", "init", "-q", os.fspath(root)], check=True)
            source = root / "candidate.rs"
            source.write_text("#[cfg_attr(any(), ignore)]\nfn deferred() {}\n", encoding="utf-8")
            rejected = subprocess.run(
                ["python3", "-B", os.fspath(SCANNER_PATH), "--root", os.fspath(root)],
                check=False,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            self.assertEqual(rejected.returncode, 1)
            self.assertIn(
                "candidate.rs:1: ignored Rust test attribute", rejected.stderr
            )

            source.write_text("#[test]\nfn active() {}\n", encoding="utf-8")
            accepted = subprocess.run(
                ["python3", "-B", os.fspath(SCANNER_PATH), "--root", os.fspath(root)],
                check=False,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            self.assertEqual(accepted.returncode, 0, accepted.stderr)


class TargoRunnerTests(unittest.TestCase):
    def make_fake(self, directory: Path, name: str = "targo") -> tuple[Path, Path]:
        binary = directory / name
        log = directory / "args"
        binary.write_text(
            '#!/bin/sh\nprintf "%s\\n" "$@" > "$FAKE_TARGO_LOG"\n',
            encoding="utf-8",
        )
        binary.chmod(0o755)
        return binary, log

    def run_wrapper(
        self, binary: Path, log: Path, *args: str
    ) -> subprocess.CompletedProcess[str]:
        env = os.environ.copy()
        env["TRUST_TARGO_BIN"] = os.fspath(binary)
        env["FAKE_TARGO_LOG"] = os.fspath(log)
        return subprocess.run(
            ["/bin/bash", os.fspath(RUN_TARGO), *args],
            check=False,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )

    def test_compile_command_uses_explicit_unverified_targo_lane(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            binary, log = self.make_fake(Path(temporary))
            result = self.run_wrapper(binary, log, "test", "--locked")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(log.read_text(encoding="utf-8"), "--unverified\ntest\n--locked\n")

    def test_format_command_uses_targo_without_compile_authorization(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            binary, log = self.make_fake(Path(temporary))
            result = self.run_wrapper(binary, log, "fmt", "--check", "--all")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(log.read_text(encoding="utf-8"), "fmt\n--check\n--all\n")

    def test_cargo_named_override_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            binary, log = self.make_fake(Path(temporary), "cargo")
            result = self.run_wrapper(binary, log, "test")
            self.assertEqual(result.returncode, 2)
            self.assertIn("must point to a binary named targo", result.stderr)
            self.assertFalse(log.exists())

    def test_empty_override_is_rejected_without_searching_path(self) -> None:
        env = os.environ.copy()
        env["TRUST_TARGO_BIN"] = ""
        result = subprocess.run(
            ["/bin/bash", os.fspath(RUN_TARGO), "test"],
            check=False,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self.assertEqual(result.returncode, 2)
        self.assertIn("TRUST_TARGO_BIN is empty", result.stderr)

    def test_upstream_cargo_on_path_is_not_a_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            cargo, log = self.make_fake(directory, "cargo")
            env = {
                "PATH": os.fspath(directory),
                "FAKE_TARGO_LOG": os.fspath(log),
            }
            result = subprocess.run(
                ["/bin/bash", os.fspath(RUN_TARGO), "test"],
                check=False,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            self.assertEqual(result.returncode, 2)
            self.assertIn("Trust targo was not found", result.stderr)
            self.assertTrue(cargo.exists())
            self.assertFalse(log.exists())

    def test_unknown_command_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            binary, log = self.make_fake(Path(temporary))
            result = self.run_wrapper(binary, log, "metadata")
            self.assertEqual(result.returncode, 2)
            self.assertIn("unsupported internal Targo gate command", result.stderr)
            self.assertFalse(log.exists())

    def test_internal_gate_scripts_route_rust_work_through_targo(self) -> None:
        for relative in (
            "scripts/ci-self-verify.sh",
            "scripts/ci_gates.sh",
            "scripts/bump-dep-pin.sh",
        ):
            source = (ROOT / relative).read_text(encoding="utf-8")
            self.assertIn("scripts/run-targo.sh", source)
            live_lines = [
                line
                for line in source.splitlines()
                if line.strip() and not line.lstrip().startswith("#")
            ]
            for line in live_lines:
                self.assertNotRegex(
                    line,
                    r"(^|[;&|()\s])cargo\s+"
                    r"(bench|build|check|clippy|doc|fix|run|rustc|rustdoc|test)\b",
                )


if __name__ == "__main__":
    unittest.main()
