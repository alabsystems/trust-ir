#!/usr/bin/env python3
"""Reject ignored Rust tests and non-executing rustdoc examples.

The scanner operates on Git-visible Rust sources (tracked plus untracked,
non-ignored files).  It masks Rust comments and literals before parsing
attribute token trees, so multiline attributes, `cfg_attr(..., ignore)`, and
rustdoc `ignore`/`no_run` fences are caught without treating examples in
comments or string literals as live attributes.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Sequence


ATTRIBUTE_START = re.compile(r"#\s*!?\s*\[")
IGNORE_IDENT = re.compile(r"\bignore\b")
NON_EXECUTING_FENCE = re.compile(r"```[^\n`]*\b(?:ignore|no_run)\b")
DOC_LINE = re.compile(r"(?m)^[ \t]*//[/!](?![/])(.*)$")
DOC_BLOCK = re.compile(r"(?s)/\*[*!](?!\*)(.*?)\*/")
RAW_STRING_START = re.compile(r"(?:br|cr|r)(?P<hashes>#{0,255})\"")


@dataclass(frozen=True)
class Finding:
    line: int
    kind: str


def _blank(masked: List[str], start: int, end: int) -> None:
    """Blank a source range while preserving newlines and byte offsets."""

    for index in range(start, end):
        if masked[index] not in "\r\n":
            masked[index] = " "


def _quoted_literal_end(source: str, quote: int, delimiter: str) -> int:
    index = quote + 1
    while index < len(source):
        if source[index] == "\\":
            index += 2
            continue
        if source[index] == delimiter:
            return index + 1
        if source[index] in "\r\n" and delimiter == "'":
            return quote + 1
        index += 1
    return len(source)


def mask_non_code(source: str) -> str:
    """Replace Rust comments and literals with spaces, preserving newlines."""

    masked = list(source)
    index = 0
    while index < len(source):
        if source.startswith("//", index):
            end = source.find("\n", index + 2)
            if end < 0:
                end = len(source)
            _blank(masked, index, end)
            index = end
            continue

        if source.startswith("/*", index):
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
            _blank(masked, index, end)
            index = end
            continue

        raw = RAW_STRING_START.match(source, index)
        if raw is not None:
            terminator = '"' + raw.group("hashes")
            end = source.find(terminator, raw.end())
            end = len(source) if end < 0 else end + len(terminator)
            _blank(masked, index, end)
            index = end
            continue

        if source[index] == '"' or (
            source[index] in "bc"
            and index + 1 < len(source)
            and source[index + 1] == '"'
        ):
            quote = index if source[index] == '"' else index + 1
            end = _quoted_literal_end(source, quote, '"')
            _blank(masked, index, end)
            index = end
            continue

        if source[index] == "'" or (
            source[index] == "b"
            and index + 1 < len(source)
            and source[index + 1] == "'"
        ):
            quote = index if source[index] == "'" else index + 1
            end = _quoted_literal_end(source, quote, "'")
            if end > quote + 1:
                _blank(masked, index, end)
                index = end
                continue

        index += 1

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


def scan_source(source: str) -> List[Finding]:
    findings: List[Finding] = []
    masked = mask_non_code(source)

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
            if NON_EXECUTING_FENCE.search(raw_attribute):
                findings.append(
                    Finding(
                        line=source.count("\n", 0, start) + 1,
                        kind="non-executing rustdoc example",
                    )
                )

    for match in DOC_LINE.finditer(source):
        if NON_EXECUTING_FENCE.search(match.group(1)):
            findings.append(
                Finding(
                    line=source.count("\n", 0, match.start()) + 1,
                    kind="non-executing rustdoc example",
                )
            )
    for match in DOC_BLOCK.finditer(source):
        fence = NON_EXECUTING_FENCE.search(match.group(1))
        if fence is not None:
            findings.append(
                Finding(
                    line=source.count("\n", 0, match.start(1) + fence.start()) + 1,
                    kind="non-executing rustdoc example",
                )
            )

    return sorted(set(findings), key=lambda finding: (finding.line, finding.kind))


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
            source = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            print(f"{path}: failed to read Rust source: {error}", file=sys.stderr)
            return 2
        for finding in scan_source(source):
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
