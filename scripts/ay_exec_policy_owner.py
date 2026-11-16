# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""One independently owned source package in AY's selected library graph.

This validates source ownership and locked edges only. It grants no admission,
installed policy, resource, execution, proof or platform-permission authority.
"""
from __future__ import annotations

import re


AY_URL = "https://github.com/alabsystems/ay.git"
REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"
NAME = "trust-exec-policy"
VERSION = "0.13.0"
# The AY workspace version whose selected graph carries this package as its one
# independently versioned owner. Accepting the owner only at this version makes
# an AY pin move re-review it. Publication transform T6 moves it with the public
# AY pin, after the public AY's own manifests show the same owner.
OWNER_AY_VERSION = "0.28.2"


class OwnerError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise OwnerError("AY exec-policy source owner: " + message)


def identity(row):
    return row.get("name"), row.get("version"), row.get("source")


# Rust split_whitespace follows Unicode White_Space. Python str.split also
# recognizes U+001C..U+001F, which must stay inside a Rust dependency token.
_RUST_WHITESPACE = re.compile(r"[\t-\r \u0085\u00a0\u1680\u2000-\u200a\u2028\u2029\u202f\u205f\u3000]+")


_RUST_TRIM = re.compile(
    r"\A(?:" + _RUST_WHITESPACE.pattern + r")|(?:" + _RUST_WHITESPACE.pattern + r")\Z")


def rust_trim(raw):
    """Trim Rust White_Space at line edges without rewriting interior bytes."""
    return _RUST_TRIM.sub("", raw)


def _dependency_fields(raw):
    require(isinstance(raw, str), "malformed dependency")
    return [field for field in _RUST_WHITESPACE.split(raw) if field]


def resolve(raw, packages):
    fields = _dependency_fields(raw)
    require(1 <= len(fields) <= 3, "malformed dependency")
    requested = None
    if len(fields) == 3:
        require(fields[2].startswith("(") and fields[2].endswith(")"),
                "malformed dependency source")
        requested = fields[2][1:-1]

    def source_matches(value):
        if requested is None or requested == value:
            return True
        if not isinstance(value, str) or not requested.startswith("git+") or "#" in requested:
            return False
        base, separator, precise = value.rpartition("#")
        return bool(separator) and base == requested and re.fullmatch(r"[0-9a-f]{40}", precise) is not None

    selected = [row for row in packages if row.get("name") == fields[0]
                and (len(fields) < 2 or row.get("version") == fields[1])
                and source_matches(row.get("source"))]
    require(len(selected) == 1, "ambiguous or missing dependency")
    return selected[0]


def locked_identity(packages, revision, ay_version):
    """Check the actual required ay-sys -> policy -> existing libc route.

    Older AY epochs may lack the policy altogether. Presence never follows
    from a name alone: both selected rows and the exact incoming edge are owed.
    Other same-named packages at other sources remain independently owned.
    """
    require(isinstance(packages, list) and all(isinstance(row, dict) for row in packages),
            "malformed package inventory")
    require(all(isinstance(row.get("dependencies", []), list)
                and all(isinstance(edge, str) for edge in row.get("dependencies", []))
                for row in packages), "malformed locked dependency array")
    source = f"git+{AY_URL}?rev={revision}#{revision}"
    vendors = [row for row in packages if row.get("name") == NAME
               and str(row.get("source", "")).startswith("git+" + AY_URL)]
    owners = [row for row in packages if row.get("name") == "ay-sys" and row.get("source") == source]
    incoming = []
    for row in packages:
        for edge in row.get("dependencies", []):
            fields = _dependency_fields(edge)
            if fields and fields[0] == NAME:
                target = resolve(edge, packages)
                if target in vendors:
                    incoming.append((row, target))
    if not vendors and not incoming:
        return None
    require(ay_version == OWNER_AY_VERSION and len(vendors) == 1 and len(owners) == 1,
            "unsupported AY version or duplicate/missing actual owner")
    vendor, owner = vendors[0], owners[0]
    require(identity(vendor) == (NAME, VERSION, source)
            and owner.get("version") == ay_version,
            "source/version disagrees with the selected AY owner")
    require(len(incoming) == 1 and incoming[0][0] is owner and incoming[0][1] is vendor,
            "requires exactly the actual ay-sys incoming edge")
    require(set(vendor) == {"name", "version", "source", "dependencies"},
            "unexpected package metadata")
    edges = vendor["dependencies"]
    require(isinstance(edges, list) and len(edges) == 1, "requires the sole libc dependency")
    libc = resolve(edges[0], packages)
    require(libc.get("name") == "libc" and libc.get("source") == REGISTRY
            and isinstance(libc.get("version"), str)
            and re.fullmatch(r"0\.2\.(?:0|[1-9][0-9]*)", libc["version"]) is not None,
            "requires a canonical registry libc 0.2 package")
    return identity(vendor)
