#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Rust cooked-string decoding shared by source guards; no compiler verdict."""

from __future__ import annotations

import re

_UNICODE_ESCAPE = re.compile(r"\{([0-9a-fA-F][0-9a-fA-F_]*)\}")


def decode_rust_string(content: str) -> str:
    """Decode cooked string contents once, using Rust's escape rules."""
    content = content.replace("\r\n", "\n")
    simple = {"0": "\0", "t": "\t", "n": "\n", "r": "\r",
              '"': '"', "'": "'", "\\": "\\"}
    result: list[str] = []
    index = 0
    while index < len(content):
        char = content[index]
        index += 1
        if char != "\\":
            result.append(char)
            continue
        if index >= len(content):
            raise ValueError("incomplete Rust string escape in Rust string literal")
        escape = content[index]
        index += 1
        if escape in simple:
            result.append(simple[escape])
        elif escape == "\n":
            while index < len(content) and content[index] in "\t\n\r ":
                index += 1
        elif escape == "x":
            digits = content[index:index + 2]
            if re.fullmatch(r"[0-7][0-9a-fA-F]", digits) is None:
                raise ValueError("invalid Rust ASCII escape in Rust string literal")
            result.append(chr(int(digits, 16)))
            index += 2
        elif escape == "u":
            unicode = _UNICODE_ESCAPE.match(content, index)
            digits = unicode[1].replace("_", "") if unicode else ""
            if not 1 <= len(digits) <= 6:
                raise ValueError("invalid Rust Unicode escape in Rust string literal")
            value = int(digits, 16)
            if value > 0x10FFFF or 0xD800 <= value <= 0xDFFF:
                raise ValueError("invalid Rust Unicode scalar in Rust string literal")
            result.append(chr(value))
            index = unicode.end()
        else:
            raise ValueError("invalid Rust string escape in Rust string literal")
    return "".join(result)


_LITERAL_INCLUDE = re.compile(
    r'\binclude(?:_str|_bytes)?\s*!\s*'
    r'(?P<open>[([{])\s*(?P<literal>"")\s*,?\s*(?P<close>[)\]}])'
)


def literal_include_positions(code: str) -> list[int]:
    """Find literal include arguments within matching Rust macro delimiters."""
    closes = {"(": ")", "[": "]", "{": "}"}
    return [match.start("literal") for match in _LITERAL_INCLUDE.finditer(code)
            if closes[match["open"]] == match["close"]]
