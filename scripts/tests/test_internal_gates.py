from __future__ import annotations

import importlib.util
import json
import os
import shlex
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


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
    def test_fixture_interpreter_path_with_spaces_and_quotes(self) -> None:
        with tempfile.TemporaryDirectory(prefix="interpreter's path ") as temporary:
            root = Path(temporary)
            interpreter = root / "python interpreter"
            interpreter.symlink_to(sys.executable)
            with mock.patch.object(sys, "executable", os.fspath(interpreter)):
                binary, log = self.make_fake(root)
                self.make_rustup(root)
            result = self.run_wrapper(binary, log, "test", "argument with spaces")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(log.read_text()),
                             ["--unverified", "test", "argument with spaces"])
            rustup_log = root / "rustup-args"
            # Neither launcher may rely on python being available on PATH.
            result = self.run_isolated({
                "PATH": os.fspath(root),
                "FAKE_TARGO_LOG": os.fspath(log),
                "FAKE_RUSTUP_LOG": os.fspath(rustup_log),
                "FAKE_RUSTUP_TARGO": os.fspath(binary),
            }, "metadata")
            self.assertEqual(result.returncode, 0, result.stderr)
            # PATH finds targo first; invoke rustup directly to exercise its launcher.
            result = subprocess.run(
                [os.fspath(root / "rustup"), "which", "targo"],
                env={"PATH": "", "FAKE_RUSTUP_LOG": os.fspath(rustup_log),
                     "FAKE_RUSTUP_TARGO": os.fspath(binary)},
                capture_output=True, text=True, check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(rustup_log.read_text()), ["which", "targo"])

    def make_fake(
        self,
        directory: Path,
        name: str = "targo",
        *,
        exit_code: int = 0,
        discriminates: bool = True,
    ) -> tuple[Path, Path]:
        # A real targo answers `--unverified --version`; upstream Cargo named
        # targo rejects it. The probe is answered without touching the log, so
        # the log still records exactly the dispatched gate command.
        # Quote the interpreter with a shell launcher: an OS shebang splits
        # interpreter paths containing spaces.
        binary = directory / name
        log = directory / "args"
        binary.write_text(
            "#!/bin/sh\n"
            f"exec {shlex.quote(sys.executable)} - \"$@\" <<'PYTHON_FIXTURE'\n"
            "import json, os, sys\n"
            "if sys.argv[1:] == ['--unverified', '--version']:\n"
            f"    raise SystemExit({0 if discriminates else 1})\n"
            "with open(os.environ['FAKE_TARGO_LOG'], 'w', encoding='utf-8') as log:\n"
            "    json.dump(sys.argv[1:], log)\n"
            f"raise SystemExit({exit_code})\n"
            "PYTHON_FIXTURE\n",
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
            for command in ("bench", "build", "check", "doc", "fix",
                            "run", "rustc", "rustdoc", "test"):
                with self.subTest(command=command):
                    result = self.run_wrapper(binary, log, command, "--locked")
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(json.loads(log.read_text(encoding="utf-8")),
                                     ["--unverified", command, "--locked"])

    def test_lints_run_through_targo_tippy_without_a_lane_flag(self) -> None:
        # `targo tippy` is Trust's clippy and takes no lane flag; `clippy` is
        # kept as an alias so an older caller cannot reach upstream clippy.
        with tempfile.TemporaryDirectory() as temporary:
            binary, log = self.make_fake(Path(temporary))
            for command in ("clippy", "tippy"):
                with self.subTest(command=command):
                    result = self.run_wrapper(binary, log, command, "--locked", "--", "-D", "warnings")
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(json.loads(log.read_text(encoding="utf-8")),
                                     ["tippy", "--locked", "--", "-D", "warnings"])

    def test_upstream_cargo_named_targo_is_refused_before_dispatch(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            binary, log = self.make_fake(Path(temporary), discriminates=False)
            for command in ("test", "fmt", "metadata", "tippy"):
                with self.subTest(command=command):
                    result = self.run_wrapper(binary, log, command)
                    self.assertEqual(result.returncode, 2, result.stderr)
                    self.assertIn("is not Trust's targo", result.stderr)
                    self.assertFalse(log.exists(), "a refused binary must never be dispatched")

    def test_format_command_uses_targo_without_compile_authorization(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            binary, log = self.make_fake(Path(temporary))
            result = self.run_wrapper(binary, log, "fmt", "--check", "--all")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(log.read_text(encoding="utf-8")),
                             ["fmt", "--check", "--all"])

    def test_dependency_commands_make_no_compilation_authorization_claim(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            binary, log = self.make_fake(Path(temporary))
            for args in (
                ["metadata", "--format-version", "1", "--all-features", "--manifest-path", "dir with spaces/Cargo.toml"],
                ["update", "--manifest-path", "frontend/Cargo.toml", "-p", "clean-kernel"],
                ["generate-lockfile", "--manifest-path", "export/frontend/Cargo.toml"],
            ):
                with self.subTest(command=args[0]):
                    result = self.run_wrapper(binary, log, *args)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(json.loads(log.read_text(encoding="utf-8")), args)

    def test_arguments_are_forwarded_byte_exactly_without_shell_reinterpretation(self) -> None:
        with tempfile.TemporaryDirectory(prefix="targo path with spaces ") as temporary:
            binary, log = self.make_fake(Path(temporary))
            args = ["metadata", "", "line one\nline two", "$(not-executed)", "*", "semi;colon"]
            result = self.run_wrapper(binary, log, *args)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(log.read_text(encoding="utf-8")), args)

    def test_frontend_failure_status_is_preserved_in_both_lanes(self) -> None:
        for command in ("test", "metadata", "update", "fmt"):
            for status in (23, 127):
                with self.subTest(command=command, status=status):
                    with tempfile.TemporaryDirectory() as temporary:
                        binary, log = self.make_fake(Path(temporary), exit_code=status)
                        result = self.run_wrapper(binary, log, command)
                        self.assertEqual(result.returncode, status, result.stderr)
                        prefix = ["--unverified"] if command == "test" else []
                        self.assertEqual(json.loads(log.read_text(encoding="utf-8")), prefix + [command])

    @staticmethod
    def make_rustup(directory: Path, *, status: int = 0) -> Path:
        binary = directory / "rustup"
        binary.write_text(
            "#!/bin/sh\n"
            f"exec {shlex.quote(sys.executable)} - \"$@\" <<'PYTHON_FIXTURE'\n"
            "import json, os, sys\n"
            "with open(os.environ['FAKE_RUSTUP_LOG'], 'w', encoding='utf-8') as log:\n"
            "    json.dump(sys.argv[1:], log)\n"
            "print(os.environ['FAKE_RUSTUP_TARGO'])\n"
            f"raise SystemExit({status})\n"
            "PYTHON_FIXTURE\n",
            encoding="utf-8",
        )
        binary.chmod(0o755)
        return binary

    @staticmethod
    def run_isolated(env: dict[str, str], *args: str) -> subprocess.CompletedProcess[str]:
        # No workstation PATH/rustup/override can satisfy a synthetic test.
        return subprocess.run(
            ["/bin/bash", os.fspath(RUN_TARGO), *args],
            check=False, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )

    def test_explicit_selection_precedes_path_and_rustup(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            explicit = root / "explicit path"
            search = root / "search"
            explicit.mkdir()
            search.mkdir()
            binary, log = self.make_fake(explicit)
            self.make_fake(search, exit_code=71)
            self.make_rustup(search, status=72)
            rustup_log = root / "rustup-args"
            result = self.run_isolated({
                "PATH": os.fspath(search),
                "TRUST_TARGO_BIN": os.fspath(binary),
                "FAKE_TARGO_LOG": os.fspath(log),
                "FAKE_RUSTUP_LOG": os.fspath(rustup_log),
                "FAKE_RUSTUP_TARGO": os.fspath(binary),
            }, "metadata")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(log.read_text(encoding="utf-8")), ["metadata"])
            self.assertFalse(rustup_log.exists())

    def test_path_selection_precedes_rustup(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            binary, log = self.make_fake(directory)
            self.make_rustup(directory, status=72)
            rustup_log = directory / "rustup-args"
            result = self.run_isolated({
                "PATH": os.fspath(directory),
                "FAKE_TARGO_LOG": os.fspath(log),
                "FAKE_RUSTUP_LOG": os.fspath(rustup_log),
                "FAKE_RUSTUP_TARGO": os.fspath(binary),
            }, "update")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(log.read_text(encoding="utf-8")), ["update"])
            self.assertFalse(rustup_log.exists())

    def test_rustup_resolution_selects_only_successful_exact_trust_tool(self) -> None:
        for status in (0, 17):
            with self.subTest(status=status):
                with tempfile.TemporaryDirectory() as temporary:
                    root = Path(temporary)
                    search = root / "search"
                    installed = root / "installed tool"
                    search.mkdir()
                    installed.mkdir()
                    binary, log = self.make_fake(installed)
                    self.make_rustup(search, status=status)
                    rustup_log = root / "rustup-args"
                    result = self.run_isolated({
                        "PATH": os.fspath(search),
                        "FAKE_TARGO_LOG": os.fspath(log),
                        "FAKE_RUSTUP_LOG": os.fspath(rustup_log),
                        "FAKE_RUSTUP_TARGO": os.fspath(binary),
                    }, "metadata")
                    self.assertEqual(json.loads(rustup_log.read_text(encoding="utf-8")),
                                     ["which", "--toolchain", "trust", "targo"])
                    if status == 0:
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertEqual(json.loads(log.read_text(encoding="utf-8")), ["metadata"])
                    else:
                        self.assertEqual(result.returncode, 2, result.stderr)
                        self.assertIn("Trust targo was not found", result.stderr)
                        self.assertFalse(log.exists(), "failed resolver stdout grants no selection")

    def test_invalid_explicit_path_does_not_fall_back_to_available_targo(self) -> None:
        for kind in ("empty", "missing", "nonexecutable"):
            with self.subTest(kind=kind):
                with tempfile.TemporaryDirectory() as temporary:
                    directory = Path(temporary)
                    binary, log = self.make_fake(directory)
                    bad = directory / "override" / "targo"
                    if kind == "nonexecutable":
                        bad.parent.mkdir()
                        bad.write_text("not executable\n", encoding="utf-8")
                    result = self.run_isolated({
                        "PATH": os.fspath(directory),
                        "TRUST_TARGO_BIN": "" if kind == "empty" else os.fspath(bad),
                        "FAKE_TARGO_LOG": os.fspath(log),
                    }, "metadata")
                    self.assertEqual(result.returncode, 2, result.stderr)
                    self.assertFalse(log.exists())
                    self.assertTrue(binary.is_file())

    def test_missing_command_is_usage_error_without_resolving_a_tool(self) -> None:
        result = self.run_isolated({"PATH": "/nonexistent-targo-test-path"})
        self.assertEqual(result.returncode, 2)
        self.assertIn("usage: scripts/run-targo.sh", result.stderr)

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
            result = self.run_wrapper(binary, log, "publish")
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
                    r"(bench|build|check|clippy|doc|fix|run|rustc|rustdoc|test|metadata|update)\b",
                )


if __name__ == "__main__":
    unittest.main()
