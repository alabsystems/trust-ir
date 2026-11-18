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
with mock.patch.object(sys, "path", [os.fspath(ROOT / "scripts"), *sys.path]):
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

    def test_cooked_doc_strings_are_checked_after_rust_unescaping(self) -> None:
        contents = [r'\x60\x60\x60ignore', r'\u{60}\u{060}\u{0_60}no_run',
                    r'```\x69gnore', r'```no_\u{72}un',
                    '```ig\\\n \t\r\nnore', '```no_\\\r\n  run']
        for content in contents:
            for attribute in ['#[doc = "' + content + '"]',
                              '#[cfg_attr(any(), doc = "' + content + '")]']:
                with self.subTest(attribute=attribute):
                    findings = SCANNER.scan_source('\n' + attribute + '\nfn f() {}')
                    self.assertEqual([f.kind for f in findings],
                                     ["non-executing rustdoc example"])
                    self.assertEqual([f.line for f in findings], [2])

    def test_raw_and_escaped_backslash_doc_text_is_not_unescaped_twice(self) -> None:
        samples = [r'#[doc = r"\x60\x60\x60ignore"] fn f() {}',
                   r'#[doc = r#"```\x69gnore"#] fn f() {}',
                   r'#[doc = "\\x60\\x60\\x60ignore"] fn f() {}',
                   r'const DATA: &str = "\x60\x60\x60ignore";',
                   r'// #[doc = "\x60\x60\x60ignore"]',
                   r'#[doc(alias = "\x60\x60\x60ignore")] fn f() {}',
                   '#[doc = "```ig\\\n\u2003nore"] fn f() {}',
                   r'#[doc = "An ordinary Unicode string: é λ \\n"] fn f() {}']
        for source in samples:
            with self.subTest(source=source):
                self.assertEqual(self.kinds(source), [])

    def test_active_rustdoc_is_allowed(self) -> None:
        self.assertEqual(
            self.kinds("/// ```rust\n/// active_and_executed();\n/// ```\nfn f() {}\n"),
            [],
        )

    def test_non_executing_tilde_fences_are_rejected_in_live_docs(self) -> None:
        for opening in ['~~~ignore', '~~~~~no_run', '~~~rust,ignore',
                        '~~~rust~no_run', '~~~custom`ignore']:
            samples = ['/// ' + opening + '\n/// fn skipped() {}\n/// ~~~\nfn f() {}',
                       '/** ' + opening + '\nfn skipped() {}\n~~~\n*/ fn f() {}',
                       '#[doc = "' + opening + '\\nfn skipped() {}\\n~~~"] fn f() {}',
                       '#[cfg_attr(any(), doc = r"' + opening + '\n~~~")] fn f() {}']
            for source in samples:
                with self.subTest(source=source):
                    findings = SCANNER.scan_source(source)
                    self.assertEqual([f.kind for f in findings],
                                     ["non-executing rustdoc example"])
                    self.assertEqual([f.line for f in findings], [1])
        self.assertEqual(self.kinds(r'#[doc = "\x7e\x7e\x7e\u{69}gnore"] fn f() {}'),
                         ["non-executing rustdoc example"])

    def test_active_or_data_tilde_fences_are_allowed(self) -> None:
        samples = ['/// ~~~rust\n/// fn active() {}\n/// ~~~\nfn f() {}',
                   '/// ~~ignore\nfn f() {}', '/// ~`~ignore\nfn f() {}',
                   '/// ~~\n/// ~ignore\nfn f() {}',
                   '/// ~~~\n/// ignore\n/// ~~~\nfn f() {}',
                   '/// ~~~ignoreless\nfn f() {}',
                   '/** ~~~ */\n// ignore\nfn f() {}',
                   '// ~~~ignore\n/** clean docs */ fn f() {}',
                   '/** ~~~\nignore\n~~~\n*/ fn f() {}',
                   '/* ~~~ignore */', 'const DATA: &str = "~~~no_run";',
                   r'const DATA: &str = r"/// ~~~ignore";',
                   r'#[doc = r"\x7e\x7e\x7eignore"] fn f() {}']
        for source in samples:
            with self.subTest(source=source):
                self.assertEqual(self.kinds(source), [])

    def test_fence_family_order_keeps_the_earliest_source_line(self) -> None:
        for first, second in [('~~~ignore', '```no_run'), ('```ignore', '~~~no_run')]:
            source = '/** docs\n' + first + '\n' + second + '\n*/ fn f() {}'
            with self.subTest(first=first):
                findings = SCANNER.scan_source(source)
                self.assertEqual([f.line for f in findings], [2])

    def test_fence_search_keeps_span_bounds_and_zero_offset(self) -> None:
        source = '~~~ignore\n~~~no_run\n~~~ignore'
        middle = source.index('~~~no_run')
        self.assertEqual(SCANNER._non_executing_fence(source), 0)
        self.assertIsNone(SCANNER._non_executing_fence(source, middle, middle + 3))
        self.assertEqual(SCANNER._non_executing_fence(source, middle, middle + 9), middle)

    def test_doc_fence_text_in_literals_and_ordinary_comments_is_data(self) -> None:
        samples = [
            'const DATA: &str = r#"\n/// ```ignore\n"#;',
            'const DATA: &str = r##"/** ```no_run */"##;',
            'const DATA: &str = "/*! ```ignore */";',
            'const DATA: &[u8] = br#"\n//! ```no_run\n"#;',
            '/*\n/// ```ignore\n*/',
            '/* outer /** ```no_run */ end */',
            '//// ```ignore\n',
            '/*** ```no_run */',
        ]
        for source in samples:
            with self.subTest(source=source):
                self.assertEqual(self.kinds(source), [])

    def test_live_doc_fences_after_code_and_nested_comments_are_rejected(self) -> None:
        samples = [
            ('fn before() {} /// ```ignore\nfn after() {}', 1),
            ('/** docs /* nested */\n * ```no_run\n */\nfn f() {}', 2),
            ('/*! docs /* nested */\n * ```ignore\n */', 2),
            ('//! ```no_run\nfn f() {}', 1),
            ("fn before<'a>() {} /** Rust's example:\n * ```ignore\n */\nfn after() {}", 2),
            ('/*!*\n * ```no_run\n */', 2),
        ]
        for source, line in samples:
            with self.subTest(source=source):
                findings = SCANNER.scan_source(source)
                self.assertEqual([f.kind for f in findings], ["non-executing rustdoc example"])
                self.assertEqual([f.line for f in findings], [line])

    def test_collecting_doc_spans_preserves_the_reference_mask(self) -> None:
        samples = [
            'const DATA: &str = r#"\n/// ```ignore\n"#; // ordinary\n',
            '/** docs /* nested */\n * ```no_run\n */\nfn f() {}',
            '/* ordinary /** ```ignore */ */\n#[ignore]\nfn f() {}',
            '/// ```ignore\nfn f() {}\n//! ```no_run\n',
            "fn f<'a>(x: &'a str) { let c = '\\n'; let b = b'x'; }",
            "fn before<'a>() {} /** Rust's example:\n * ```ignore\n */\nfn after() {}",
        ]
        for source in samples:
            with self.subTest(source=source):
                docs = []
                masked = SCANNER.mask_non_code(source, doc_comments=docs)
                self.assertEqual(masked, SCANNER._mask_non_code_reference(source))
                self.assertEqual(masked, SCANNER.mask_non_code(source))

    def test_lifetimes_do_not_hide_later_attributes_or_doc_comments(self) -> None:
        sources = [
            ("fn before<'a>() {} #[test] #[ignore] fn after() { let _ = \"Rust's\"; }",
             "ignored Rust test attribute"),
            ("fn before<'寿>() {} /** Rust's example:\n * ```ignore\n */\nfn after() {}",
             "non-executing rustdoc example"),
        ]
        for source, kind in sources:
            with self.subTest(source=source):
                self.assertEqual(self.kinds(source), [kind])
        source = (r'''fn before() { let _ = 'r: loop { break 'r"\""; }; }'''
                  + '\n/// ```ignore\nfn after() {}')
        self.assertEqual(self.kinds(source), ["non-executing rustdoc example"])

    def test_literal_suffixes_and_identifiers_do_not_hide_live_docs(self) -> None:
        prefixes = [
            r'""r"\""', r'r""r"\""', r"'x'r" + r'"\""',
            r'b""r"\""', r'c""r"\""', r'123r"\""',
            r'wordr"\""', r'r#r"\""', '寿r' + r'"\""',
            '""寿r' + r'"\""', r'""r#"\""',
            "'r" + r'"\""', "'br" + r'"\""', "'cr" + r'"\""',
            "'r#r" + r'"\""', "'寿r" + r'"\""',
            r'k#r"\""',
        ]
        for prefix in prefixes:
            source = ('macro_rules! eat { ($($tokens:tt)*) => {} }\n'
                      'eat!(' + prefix + ');\n/// ```ignore\nfn f() {}')
            with self.subTest(prefix=prefix):
                self.assertEqual(self.kinds(source), ["non-executing rustdoc example"])
                self.assertEqual(SCANNER.mask_non_code(source),
                                 SCANNER._mask_non_code_reference(source))

    def test_legacy_edition_prefixes_cannot_hide_live_refusals(self) -> None:
        prefixes = ['k#r' + '"' + '\\' + '"' * 3,
                    'cr' + '"' + '\\' + '"' * 2,
                    "'r#r" + '"' + '\\' + '"' * 3]
        for prefix in prefixes:
            source = ('macro_rules! eat { ($($tt:tt)*) => {} }\n'
                      'eat!(' + prefix + ');\n')
            with self.subTest(prefix=prefix):
                self.assertEqual(self.kinds(source + '/// ```ignore\nfn f() {}'),
                                 ["non-executing rustdoc example"])
                self.assertEqual(self.kinds(source + '#[ignore]\nfn f() {}'),
                                 ["ignored Rust test attribute"])
                for module in (False, True):
                    for modern in (False, True):
                        self.assertEqual(
                            SCANNER.mask_non_code(source, module_root=module, rust_2021=modern),
                            SCANNER._mask_non_code_reference(source, module_root=module, rust_2021=modern))

    def test_initial_frontmatter_is_data_and_cannot_hide_live_docs(self) -> None:
        for preamble in ['', '\ufeff', '\n\n', '#!/bin/rustrun\n',
                         '\ufeff#!/bin/rustrun\n']:
            for contents in ['"', '/* unterminated', '/// ```ignore']:
                source = preamble + '---cargo\n' + contents + '\n---\n#![feature(frontmatter)]\n'
                with self.subTest(preamble=preamble, contents=contents):
                    self.assertEqual(SCANNER._scan_source_in_context(source, True), [])
                    self.assertEqual(self.kinds(source + '/// ```no_run\nfn f() {}'),
                                     ["non-executing rustdoc example"]
                                     * (2 if contents.startswith('///') else 1))
                    self.assertEqual(self.kinds(source + '#[ignore]\nfn f() {}'),
                                     (["non-executing rustdoc example"]
                                      if contents.startswith('///') else [])
                                     + ["ignored Rust test attribute"])
                    self.assertEqual(SCANNER.mask_non_code(source),
                                     SCANNER._mask_non_code_reference(source))
        source = '---- Cargo.toml \t\n"\n---- \t\n/// ```ignore\nfn f() {}'
        self.assertEqual(self.kinds(source), ["non-executing rustdoc example"])

    def test_frontmatter_is_not_recognized_after_rust_code(self) -> None:
        source = 'fn before() {}\n---\n/// ```ignore\n---\nfn after() {}'
        self.assertEqual(self.kinds(source), ["non-executing rustdoc example"])

    def test_expression_include_interpretation_keeps_real_ignored_items(self) -> None:
        source = '---\n{\nmod m { #[test] #[ignore] fn f() {} }\n0i32\n}\n---\n1'
        self.assertEqual(self.kinds(source), ["ignored Rust test attribute"])

    def test_clean_islands_cannot_hide_later_rust_refusals(self) -> None:
        bodies = ['-- "\n', '/- " } /- nested -/ -/',
                  'def s := "} \\\""', 'def s := r#"} \""#',
                  "def c := '}'", "def h' := { field := 1 }",
                  'def «brace}name» := 1']
        for body in bodies:
            for prefix in ['', 'pub ', 'pub(crate) ', 'mod m { ',
                           'fn before() { mod m { ']:
                suffix = ' } }' if prefix.startswith('fn') else ' }' if prefix.startswith('mod') else ''
                source = prefix + 'clean { ' + body + '\n}' + suffix + '\n'
                with self.subTest(body=body, prefix=prefix):
                    self.assertEqual(self.kinds(source + '/// ```ignore\nfn f() {}'),
                                     ["non-executing rustdoc example"])
                    self.assertEqual(self.kinds(source + '#[ignore]\nfn f() {}'),
                                     ["ignored Rust test attribute"])
                    masked = SCANNER.mask_non_code(source, module_root=True)
                    self.assertEqual(len(masked), len(source))
                    self.assertEqual(masked.count('\n'), source.count('\n'))
                    self.assertEqual(masked, SCANNER._mask_non_code_reference(source, module_root=True))

    def test_ordinary_rust_named_clean_keeps_its_code(self) -> None:
        samples = ['struct clean { field: i32 }', 'impl clean { fn f() {} }',
                   'static X: clean = clean { field: 1 };',
                   'const X: clean = clean { field: 1 };',
                   'fn f() -> clean { clean { field: 1 } }',
                   'fn f() { let clean { field } = x; }',
                   'stringify!(mod m { clean { field: 1 } });',
                   'macro_rules! m { () => { mod x { clean { field: 1 } } } }',
                   'macro m(args) { mod x { clean { field: 1 } } }',
                   'r#clean { field: 1 }']
        for source in samples:
            with self.subTest(source=source):
                self.assertEqual(SCANNER.mask_non_code(source, module_root=True), source)

    def test_malformed_clean_body_is_a_refusal(self) -> None:
        for source in ['clean { /- unclosed', 'clean { "unclosed', 'clean { { }']:
            with self.subTest(source=source):
                with self.assertRaises(ValueError):
                    SCANNER.scan_source(source)

    def test_rust_whitespace_and_initial_bom_preserve_literal_boundaries(self) -> None:
        # Rust uses Pattern_White_Space, rather than Python's whitespace set.
        for whitespace in ['\t', '\v', '\f', '\r', ' ', '\x85',
                           '\u200e', '\u200f', '\u2028', '\u2029', '\ufeff']:
            source = whitespace + 'r"\n/// ```ignore\n";\n'
            with self.subTest(whitespace=repr(whitespace)):
                self.assertEqual(self.kinds(source), [])
                self.assertEqual(SCANNER.mask_non_code(source),
                                 SCANNER._mask_non_code_reference(source))

    def test_shebang_contents_do_not_hide_live_docs(self) -> None:
        for bom in ['', '\ufeff']:
            for contents in ['#!/usr/bin/env r"', '#! /* unterminated', '#! /// ```ignore']:
                source = bom + contents + '\n/// ```no_run\nfn f() {}'
                with self.subTest(bom=bool(bom), contents=contents):
                    findings = SCANNER.scan_source(source)
                    self.assertEqual([f.kind for f in findings],
                                     ["non-executing rustdoc example"])
                    self.assertEqual([f.line for f in findings], [2])
                    self.assertEqual(SCANNER.mask_non_code(source),
                                     SCANNER._mask_non_code_reference(source))

    def test_inner_attributes_after_initial_trivia_remain_live(self) -> None:
        for trivia in [' ', ' /* ordinary /* nested */ end */ ',
                       ' // ordinary\n', '\u200e']:
            source = '#!' + trivia + '[cfg_attr(any(), ignore)]\nfn f() {}'
            with self.subTest(trivia=trivia):
                self.assertEqual(self.kinds(source), ["ignored Rust test attribute"])
        self.assertEqual(self.kinds('#\u200e!\u200f[ignore]\nfn f() {}'),
                         ["ignored Rust test attribute"])

    def test_closed_char_literals_keep_their_full_masked_span(self) -> None:
        literals = [r"'a'", r"'\''", r"'\\'", r"'\n'", r"'\x2f'",
                    r"'\u{1______0__F__F__F__F}'", "'é'", "b'/'"]
        for literal in literals:
            with self.subTest(literal=literal):
                source = "let c = " + literal + ";"
                expected = "let c = " + " " * len(literal) + ";"
                self.assertEqual(SCANNER.mask_non_code(source), expected)
                self.assertEqual(SCANNER._mask_non_code_reference(source), expected)

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

            source.write_text('clean { /- unclosed', encoding="utf-8")
            refused = subprocess.run(
                ["python3", "-B", os.fspath(SCANNER_PATH), "--root", os.fspath(root)],
                capture_output=True, text=True, check=False,
            )
            self.assertEqual(refused.returncode, 2)
            self.assertIn('candidate.rs: failed to scan source:', refused.stderr)


class RustSourceInputTests(unittest.TestCase):
    def test_actual_regular_to_fifo_replacement_is_refused(self) -> None:
        if not hasattr(os, "mkfifo") or not hasattr(os, "O_NONBLOCK"):
            return
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "source.rs"
            path.write_text("fn f() {}\n", encoding="utf-8")
            code = '''
import os, sys
from unittest import mock
from pathlib import Path
sys.path.insert(0, sys.argv[1])
from check_no_ignored_rust import read_rust_source
real_stat = Path.stat
path = Path(sys.argv[2])
def replace_after_stat(candidate, *args, **kwargs):
    result = real_stat(candidate, *args, **kwargs)
    if os.fspath(candidate) == os.fspath(path):
        path.unlink()
        os.mkfifo(path)
    return result
with mock.patch.object(Path, "stat", replace_after_stat):
    try:
        read_rust_source(path)
    except OSError as error:
        assert "regular file" in str(error), error
    else:
        raise AssertionError("replacement FIFO was accepted")
'''
            result = subprocess.run([sys.executable, "-B", "-c", code,
                                     os.fspath(ROOT / "scripts"), os.fspath(path)],
                                    capture_output=True, text=True, timeout=2, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_cached_fifo_source_is_refused_without_waiting_for_a_writer(self) -> None:
        if not hasattr(os, "mkfifo"):
            return
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(["git", "init", "-q", temporary], check=True)
            path = root / "tracked.rs"
            path.write_text("fn f() {}\n", encoding="utf-8")
            subprocess.run(["git", "-C", temporary, "add", "tracked.rs"], check=True)
            path.unlink()
            os.mkfifo(path)
            result = subprocess.run(
                [sys.executable, "-B", os.fspath(SCANNER_PATH), "--root", temporary],
                capture_output=True, text=True, timeout=2, check=False,
            )
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assertIn("Rust source must be a regular file", result.stderr)

    def test_regular_source_and_symlink_keep_utf8_and_newline_behavior(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "source.rs"
            path.write_bytes('fn é() {}\r\n'.encode('utf-8'))
            self.assertEqual(SCANNER.read_rust_source(path), 'fn é() {}\n')
            link = path.with_name("link.rs")
            link.symlink_to(path)
            self.assertEqual(SCANNER.read_rust_source(link), path.read_text(encoding="utf-8"))

    def test_regular_source_without_optional_open_flags(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "source.rs"
            path.write_text("fn f() {}\n", encoding="utf-8")
            with mock.patch.dict(os.__dict__):
                for name in ("O_NONBLOCK", "O_BINARY"):
                    os.__dict__.pop(name, None)
                self.assertEqual(SCANNER.read_rust_source(path), path.read_text(encoding="utf-8"))


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
