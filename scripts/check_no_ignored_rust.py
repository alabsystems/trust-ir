#!/usr/bin/env python3
"""Reject ignored Rust tests and non-executing rustdoc examples.

The scanner operates on Git-visible Rust sources (tracked plus untracked,
non-ignored files).  It masks Rust comments and literals before parsing
attribute token trees, so multiline attributes, `cfg_attr(..., ignore)`, and
rustdoc `ignore`/`no_run` fences are caught without treating examples in
comments or string literals as live attributes.
Without inclusion context it conservatively checks both ordinary Rust and
Trust module interpretations, retaining a refusal from either one.
"""

from __future__ import annotations

import argparse
from bisect import bisect_left
import os
import re
import stat
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Sequence

if __package__:
    from .check_lean_runtime_boundary import island_end
    from .rust_string_literals import decode_rust_string
else:
    from check_lean_runtime_boundary import island_end
    from rust_string_literals import decode_rust_string


IGNORE_IDENT = re.compile(r"\bignore\b")
_BACKTICK_NON_EXECUTING_FENCE = re.compile(r"```[^\n`]*\b(?:ignore|no_run)\b")
_NON_EXECUTING_FLAG = re.compile(r"\b(?:ignore|no_run)\b")
RAW_STRING_START = re.compile(r"(?:br|cr|r)(?P<hashes>#{0,255})\"")
# Rust's Pattern_White_Space differs from Python's whitespace classification.
RUST_WHITESPACE = "\t\n\v\f\r \u0085\u200e\u200f\u2028\u2029"
_SPACE = "[" + re.escape(RUST_WHITESPACE) + "]"
ATTRIBUTE_START = re.compile("#" + _SPACE + "*!?" + _SPACE + r"*\[")
_DOC_VALUE = re.compile(r"\bdoc" + _SPACE + "*=")
# A conservative superset of non-ASCII identifier characters avoids depending
# on Python's Unicode XID version. Rust rejects other non-ASCII code tokens.
_NON_ASCII_WORD = r"[^\x00-\x7f\u0085\u200e\u200f\u2028\u2029\ufeff]"
_WORD_START = r"(?:[A-Za-z_]|" + _NON_ASCII_WORD + ")"
_WORD_CONTINUE = r"(?:[A-Za-z0-9_]|" + _NON_ASCII_WORD + ")"
_IDENTIFIER = re.compile(_WORD_START + _WORD_CONTINUE + "*")
_WORD = re.compile(_WORD_CONTINUE + "+")
_RAW_IDENTIFIER = re.compile("r#" + _WORD_START + _WORD_CONTINUE + "*")
_PREFIXED_IDENTIFIER = re.compile("[rk]#" + _WORD_START + _WORD_CONTINUE + "*")


@dataclass(frozen=True)
class Finding:
    line: int
    kind: str


def _non_executing_fence(source: str, start: int = 0,
                         end: Optional[int] = None) -> Optional[int]:
    """First forbidden fence marker in [start, end), retaining source offsets.

    Tilde info strings allow marker characters, including backticks. Search
    only the first tilde opener per line and jump past that line on failure,
    so long/repeated tilde runs do not cause repeated suffix rescans.
    The existing conservative backtick rule is unchanged.
    """
    end = len(source) if end is None else end
    backtick = _BACKTICK_NON_EXECUTING_FENCE.search(source, start, end)
    first = backtick.start() if backtick is not None else None
    tilde = source.find("~~~", start, end)
    while tilde >= 0 and (first is None or tilde < first):
        newline = source.find("\n", tilde, end)
        line_end = end if newline < 0 else newline
        if _NON_EXECUTING_FLAG.search(source, tilde + 3, line_end) is not None:
            return tilde
        tilde = source.find("~~~", line_end + 1, end)
    return first


@dataclass(frozen=True)
class _StringLiteral:
    start: int
    content_start: int
    content_end: int
    raw: bool




def _blank(masked: List[str], start: int, end: int) -> None:
    """Blank a source range while preserving newlines and byte offsets."""

    masked[start:end] = [ch if ch in "\r\n" else " " for ch in masked[start:end]]


def _string_literal_end(source: str, quote: int) -> int:
    index = quote + 1
    while index < len(source):
        if source[index] == "\\":
            index += 2
            continue
        if source[index] == '"':
            return index + 1
        index += 1
    return len(source)


def _char_literal_end(source: str, quote: int) -> int:
    """Recognize a directly closed char, never a later lifetime apostrophe."""
    end = quote + 1
    if end >= len(source) or source[end] in "'\r\n":
        return quote + 1
    if source[end] == "\\":
        end += 1
        if end >= len(source):
            return quote + 1
        if source[end] in "'\"nrt\\0":
            end += 1
        elif source[end] == "x":
            digits = source[end + 1:end + 3]
            if len(digits) != 2 or any(ch not in "0123456789abcdefABCDEF" for ch in digits):
                return quote + 1
            end += 3
        elif source.startswith("u{", end):
            end += 2
            digits = 0
            while end < len(source) and source[end] in "0123456789abcdefABCDEF_":
                digits += source[end] != "_"
                if digits > 6:
                    return quote + 1
                end += 1
            if not digits or end >= len(source) or source[end] != "}":
                return quote + 1
            end += 1
        else:
            return quote + 1
    else:
        end += 1
    return end + 1 if end < len(source) and source[end] == "'" else quote + 1


def _literal_suffix_end(source: str, end: int) -> int:
    suffix = _IDENTIFIER.match(source, end)
    return suffix.end() if suffix is not None else end


def _line_doc(source: str, index: int) -> bool:
    return source.startswith("//!", index) or (
        source.startswith("///", index) and not source.startswith("////", index)
    )


def _block_doc(source: str, index: int) -> bool:
    return source.startswith("/*!", index) or (
        source.startswith("/**", index) and not source.startswith(("/***", "/**/"), index)
    )


def _block_comment_end(source: str, index: int) -> tuple[int, bool]:
    depth = 1
    end = index + 2
    while end < len(source) and depth:
        if source.startswith("/*", end):
            depth += 1
            end += 2
        elif source.startswith("*/", end):
            depth -= 1
            end += 2
        else:
            end += 1
    return end, depth == 0


def _initial_non_code_end(source: str) -> int:
    """Skip an initial BOM and Rust's shebang, preserving inner attributes.

    Like rustc_lexer's strip_shebang, only ordinary comments and Rust
    whitespace are trivia when deciding whether the token after `#!` is `[`.
    """
    start = int(source.startswith("\ufeff"))
    if not source.startswith("#!", start):
        return start
    cursor = start + 2
    while cursor < len(source):
        if source[cursor] in RUST_WHITESPACE:
            cursor += 1
        elif source.startswith("//", cursor) and not _line_doc(source, cursor):
            end = source.find("\n", cursor + 2)
            cursor = len(source) if end < 0 else end
        elif source.startswith("/*", cursor) and not _block_doc(source, cursor):
            cursor, _ = _block_comment_end(source, cursor)
        else:
            break
    if source.startswith("[", cursor):
        return start
    end = source.find("\n", start + 2)
    return len(source) if end < 0 else end


def _code_word_end(source: str, index: int, rust_2021: bool = True) -> int:
    if source[index] == "'":
        # A failed char match can be a lifetime. Its final `r` is not a
        # separate raw-string prefix, even when a string immediately follows.
        word = ((_RAW_IDENTIFIER.match(source, index + 1) if rust_2021 else None)
                or _IDENTIFIER.match(source, index + 1))
    else:
        prefixed = _PREFIXED_IDENTIFIER if rust_2021 else _RAW_IDENTIFIER
        word = prefixed.match(source, index) or _WORD.match(source, index)
    return word.end() if word is not None else index + 1


class _RustContext:
    """Trust module-item recognition, retaining three tokens per frame."""
    def __init__(self) -> None:
        self.frames: list[tuple[str, list[str]]] = [("module", [])]
        self.macro_depth = 0

    def emit(self, token: str) -> None:
        history = self.frames[-1][1]
        prev3, prev2, prev = [""] * (3 - len(history)) + history
        ident = lambda value: value.startswith(("id:", "raw:"))
        if token in ("(", "[", "{"):
            macro = (prev in ("!", "#")
                     or (ident(prev) and prev2 in ("!", "id:macro"))
                     or (token == "{" and prev == "group:("
                         and ident(prev2) and prev3 == "id:macro"))
            kind = ("macro" if macro else "module"
                    if token == "{" and ident(prev) and prev2 == "id:mod" else "other")
            self.frames.append((kind, []))
            self.macro_depth += kind == "macro"
            return
        if token in (")", "]", "}"):
            if len(self.frames) > 1:
                kind, _ = self.frames.pop()
                self.macro_depth -= kind == "macro"
            token = "group:" + {")": "(", "]": "[", "}": "{"}[token]
            history = self.frames[-1][1]
        history.append(token)
        del history[:-3]

    def at_item(self) -> bool:
        kind, history = self.frames[-1]
        return (kind == "module" and self.macro_depth == 0
                and (not history or history[-1] in (";", "doc", "id:pub")
                     or history[-1].startswith("group:")))


def _ordinary_trivia_end(source: str, index: int) -> int:
    while index < len(source):
        if source[index] in RUST_WHITESPACE:
            index += 1
        elif source.startswith("//", index) and not _line_doc(source, index):
            end = source.find("\n", index + 2)
            index = len(source) if end < 0 else end
        elif source.startswith("/*", index) and not _block_doc(source, index):
            end, terminated = _block_comment_end(source, index)
            if not terminated:
                return index
            index = end
        else:
            break
    return index


def _code_token(source: str, index: int, masked: List[str], context: _RustContext,
                module_root: bool, rust_2021: bool) -> int:
    end = _code_word_end(source, index, rust_2021)
    word = source[index:end]
    if word == "clean" and module_root and context.at_item():
        brace = _ordinary_trivia_end(source, end)
        if source.startswith("{", brace):
            close = island_end(source, brace + 1)
            _blank(masked, end, brace)
            _blank(masked, brace + 1, close - 1)
            context.emit("id:clean")
            context.emit("{")
            context.emit("}")
            return close
    token = ("raw:" + word if _PREFIXED_IDENTIFIER.fullmatch(word) else
             "id:" + word if _IDENTIFIER.fullmatch(word) else word)
    context.emit(token)
    return end


def _frontmatter_end(source: str, index: int) -> int:
    """Skip complete initial Rust frontmatter, whose contents are not Rust.

    The first newline-plus-opening-fence closes it, as in rustc_lexer. Fence
    and infostring validity remain the compiler's job; no later code is
    searched for an opener, and incomplete forms are left for ordinary scanning.
    """
    start = index
    while start < len(source) and source[start] in RUST_WHITESPACE:
        start += 1
    if not source.startswith("---", start):
        return index
    opening_end = start + 3
    while opening_end < len(source) and source[opening_end] == "-":
        opening_end += 1
    terminator = "\n" + source[start:opening_end]
    closing = source.find(terminator, opening_end)
    if closing < 0:
        return index
    end = source.find("\n", closing + len(terminator))
    return len(source) if end < 0 else end


# Every position at which `_mask_non_code_reference`'s loop can act: a
# comment opener, a literal start, or a whole word/raw identifier. Consuming
# words and literal suffixes prevents an internal `r` from starting a raw string.
# The leftmost match is the first index the reference loop would act at, so
# jumping there and running ONE step of the same rules is the same scan.
_MASK_STOP = re.compile(
    r"""//|/\*|(?:br|cr|r)#{0,255}"|[bc]?"|b?'|"""
    + _PREFIXED_IDENTIFIER.pattern + "|" + _WORD.pattern
    + r"|[^\t\n\v\f\r \u0085\u200e\u200f\u2028\u2029]"
)


def mask_non_code(source: str, doc_comments: Optional[List[tuple[int, int]]] = None,
                  *, module_root: bool = False, rust_2021: bool = True,
                  string_literals: Optional[List[_StringLiteral]] = None) -> str:
    """Replace Rust comments and literals with spaces, preserving newlines.

    The same token rules as `_mask_non_code_reference`, using a regex to
    skip whitespace between tokens. By default this is ordinary Rust;
    module_root also recognizes initial frontmatter and Trust Clean islands.
    If supplied, `doc_comments` receives the content spans of live Rust doc
    comments; collecting them does not change the masked output."""

    masked = list(source)
    index = _initial_non_code_end(source)
    if module_root:
        index = _frontmatter_end(source, index)
    _blank(masked, 0, index)
    context = _RustContext()
    n = len(source)
    while index < n:
        stop = _MASK_STOP.search(source, index)
        if stop is None:
            break
        index = stop.start()
        if source.startswith("//", index):
            end = source.find("\n", index + 2)
            if end < 0:
                end = n
            if doc_comments is not None and _line_doc(source, index):
                doc_comments.append((index + 3, end))
            if _line_doc(source, index):
                context.emit("doc")
            _blank(masked, index, end)
            index = end
            continue

        if source.startswith("/*", index):
            end, terminated = _block_comment_end(source, index)
            if doc_comments is not None and _block_doc(source, index):
                doc_comments.append((index + 3, end - 2 if terminated else end))
            if _block_doc(source, index):
                context.emit("doc")
            _blank(masked, index, end)
            index = end
            continue

        raw = RAW_STRING_START.match(source, index)
        if raw is not None and (rust_2021 or not source.startswith("cr", index)):
            terminator = '"' + raw.group("hashes")
            end = source.find(terminator, raw.end())
            if string_literals is not None and source[index] == "r":
                string_literals.append(_StringLiteral(index, raw.end(),
                                                      n if end < 0 else end, True))
            end = n if end < 0 else end + len(terminator)
            end = _literal_suffix_end(source, end)
            _blank(masked, index, end)
            context.emit("literal")
            index = end
            continue

        if source[index] == '"' or (
            source[index] in ("bc" if rust_2021 else "b")
            and index + 1 < n
            and source[index + 1] == '"'
        ):
            quote = index if source[index] == '"' else index + 1
            end = _string_literal_end(source, quote)
            if string_literals is not None and index == quote:
                string_literals.append(_StringLiteral(index, quote + 1, end - 1, False))
            end = _literal_suffix_end(source, end)
            _blank(masked, index, end)
            context.emit("literal")
            index = end
            continue

        if source[index] == "'" or (
            source[index] == "b"
            and index + 1 < n
            and source[index + 1] == "'"
        ):
            quote = index if source[index] == "'" else index + 1
            end = _char_literal_end(source, quote)
            if end > quote + 1:
                end = _literal_suffix_end(source, end)
                _blank(masked, index, end)
                context.emit("literal")
                index = end
                continue

        index = _code_token(source, index, masked, context, module_root, rust_2021)

    return "".join(masked)


def _mask_non_code_reference(source: str, *, module_root: bool = False,
                             rust_2021: bool = True) -> str:
    """The simple reference traversal for `mask_non_code`, sharing literal
    recognition. scripts/tests/test_gate_select.py compares the traversal
    results; direct scanner controls hold the literal rules themselves."""

    masked = list(source)
    index = _initial_non_code_end(source)
    if module_root:
        index = _frontmatter_end(source, index)
    _blank(masked, 0, index)
    context = _RustContext()
    while index < len(source):
        if source.startswith("//", index):
            end = source.find("\n", index + 2)
            if end < 0:
                end = len(source)
            if _line_doc(source, index):
                context.emit("doc")
            _blank(masked, index, end)
            index = end
            continue

        if source.startswith("/*", index):
            end, _ = _block_comment_end(source, index)
            if _block_doc(source, index):
                context.emit("doc")
            _blank(masked, index, end)
            index = end
            continue

        raw = RAW_STRING_START.match(source, index)
        if raw is not None and (rust_2021 or not source.startswith("cr", index)):
            terminator = '"' + raw.group("hashes")
            end = source.find(terminator, raw.end())
            end = len(source) if end < 0 else end + len(terminator)
            end = _literal_suffix_end(source, end)
            _blank(masked, index, end)
            context.emit("literal")
            index = end
            continue

        if source[index] == '"' or (
            source[index] in ("bc" if rust_2021 else "b")
            and index + 1 < len(source)
            and source[index + 1] == '"'
        ):
            quote = index if source[index] == '"' else index + 1
            end = _literal_suffix_end(source, _string_literal_end(source, quote))
            _blank(masked, index, end)
            context.emit("literal")
            index = end
            continue

        if source[index] == "'" or (
            source[index] == "b"
            and index + 1 < len(source)
            and source[index + 1] == "'"
        ):
            quote = index if source[index] == "'" else index + 1
            end = _char_literal_end(source, quote)
            if end > quote + 1:
                end = _literal_suffix_end(source, end)
                _blank(masked, index, end)
                context.emit("literal")
                index = end
                continue

        if source[index] in RUST_WHITESPACE:
            index += 1
        else:
            index = _code_token(source, index, masked, context, module_root, rust_2021)

    return "".join(masked)


def _attribute_ranges(masked: str) -> Iterable[tuple[int, int]]:
    """Yield balanced Rust attribute ranges from already-masked source."""

    cursor = 0
    pairs = {"]": "[", ")": "(", "}": "{"}
    while True:
        match = ATTRIBUTE_START.search(masked, cursor)
        if match is None:
            return
        start = match.start()
        index = match.end()
        stack = ["["]
        while index < len(masked) and stack:
            char = masked[index]
            if char in "[({":
                stack.append(char)
            elif char in "])}":
                if pairs[char] == stack[-1]:
                    stack.pop()
                else:
                    # Malformed Rust will be rejected by the compiler. Stop at
                    # this delimiter so the scanner cannot consume later attrs.
                    stack.clear()
            index += 1
        yield start, index
        cursor = max(index, match.end())


def _scan_source_in_context(source: str, module_root: bool,
                             rust_2021: bool = True) -> List[Finding]:
    findings: List[Finding] = []
    doc_comments: List[tuple[int, int]] = []
    string_literals: List[_StringLiteral] = []
    masked = mask_non_code(source, doc_comments=doc_comments,
                           module_root=module_root, rust_2021=rust_2021,
                           string_literals=string_literals)
    string_starts = [literal.start for literal in string_literals]

    for start, end in _attribute_ranges(masked):
        attribute = masked[start:end]
        if IGNORE_IDENT.search(attribute):
            findings.append(
                Finding(
                    line=source.count("\n", 0, start) + 1,
                    kind="ignored Rust test attribute",
                )
            )

        # `#[doc = "..."]` is a rustdoc source even though its string literal
        # was masked above. Inspect only doc attributes in the original text.
        identifiers = re.findall(r"[A-Za-z_][A-Za-z0-9_]*", attribute)
        if "doc" in identifiers:
            raw_attribute = source[start:end]
            literal_fence = False
            for value in _DOC_VALUE.finditer(attribute):
                position = bisect_left(string_starts, start + value.end())
                if position == len(string_literals):
                    continue
                literal = string_literals[position]
                if literal.start >= end or masked[start + value.end():literal.start].strip(RUST_WHITESPACE):
                    continue
                content = source[literal.content_start:literal.content_end]
                rendered = content if literal.raw else decode_rust_string(content)
                if _non_executing_fence(rendered) is not None:
                    literal_fence = True
                    break
            if _non_executing_fence(raw_attribute) is not None or literal_fence:
                findings.append(
                    Finding(
                        line=source.count("\n", 0, start) + 1,
                        kind="non-executing rustdoc example",
                    )
                )

    for start, end in doc_comments:
        fence = _non_executing_fence(source, start, end)
        if fence is not None:
            findings.append(
                Finding(
                    line=source.count("\n", 0, fence) + 1,
                    kind="non-executing rustdoc example",
                )
            )

    return sorted(set(findings), key=lambda finding: (finding.line, finding.kind))


def scan_source(source: str) -> List[Finding]:
    # A .rs file may be a module or an expression included by include!.
    # Its edition is also unknown: pre-2021 splits forced keywords, C strings
    # and raw lifetimes. Retain refusals from every supported interpretation.
    return sorted({finding for module in (False, True) for modern in (False, True)
                   for finding in _scan_source_in_context(source, module, modern)},
                  key=lambda finding: (finding.line, finding.kind))


def git_visible_rust_files(root: Path) -> Sequence[Path]:
    result = subprocess.run(
        [
            "git",
            "-C",
            os.fspath(root),
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
        ],
        check=True,
        stdout=subprocess.PIPE,
    )
    return [
        root / os.fsdecode(relative)
        for relative in result.stdout.split(b"\0")
        if relative and relative.endswith(b".rs")
    ]


def read_rust_source(path: Path) -> str:
    """Read regular UTF-8 source, following the compiler's symlink behavior.

    Nonblocking open also protects against replacement by a FIFO where the
    platform provides O_NONBLOCK. Descriptor type is checked before reading.
    """
    if not stat.S_ISREG(path.stat().st_mode):
        raise OSError("Rust source must be a regular file")
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_BINARY", 0)
    descriptor = os.open(path, flags)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise OSError("Rust source must be a regular file")
        with os.fdopen(descriptor, "r", encoding="utf-8", closefd=False) as stream:
            return stream.read()
    finally:
        os.close(descriptor)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="repository root (defaults to this script's parent repository)",
    )
    args = parser.parse_args(argv)
    root = args.root.resolve()

    found = False
    try:
        paths = git_visible_rust_files(root)
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"failed to enumerate Git-visible Rust sources: {error}", file=sys.stderr)
        return 2

    for path in paths:
        try:
            source = read_rust_source(path)
        except (OSError, UnicodeError) as error:
            print(f"{path}: failed to read Rust source: {error}", file=sys.stderr)
            return 2
        try:
            findings = scan_source(source)
        except ValueError as error:
            print(f"{path.relative_to(root)}: failed to scan source: {error}", file=sys.stderr)
            return 2
        for finding in findings:
            relative = path.relative_to(root)
            print(f"{relative}:{finding.line}: {finding.kind}", file=sys.stderr)
            found = True

    if found:
        print(
            "Ignored Rust tests and non-executing docs are forbidden; use an active bounded "
            "invariant or an explicitly resource-qualified runner.",
            file=sys.stderr,
        )
        return 1

    print("Rust sources contain no ignored tests or non-executing rustdoc examples.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
