#!/usr/bin/env python3
"""Allocate and check TrustIr's contended wire namespaces (`wire-allocations.toml`).

Three namespaces on the wire are linear counters: the next binary format
version, the next tag byte of each wire enum, and the next version of each
`trust_ir.*.vN` digest domain / schema tag.  Every number in use has a row in
the registry, added in the commit that adds the code.  This tool writes a row
(`reserve`), says what the next free number is (`next`), moves a ready feature
to the lowest open version (`takeover`), and runs the toolchain-free half of
the registry gate (`check`).

`check` CHECKS what needs no compiler — it is a source scan, not a proof: the
grammar, ordering and uniqueness rules; that every `VERSION` /
`*_FORMAT_VERSION` constant in `binary.rs` has a landed row; that every
VERSIONED IDENTITY string (`<name>.vN` / `<name>-vN`) under `crates/*/src` and
`frontend/src` has a row or sits in an exempted foreign namespace; that every
enum `binary.rs` matches to or from a literal tag byte is a registered tag
space; and that the compiled half is still HOOKED IN.  The compiled half — the
tag bytes the codec REALLY writes and the versions the reader REALLY accepts —
is `trust-ir`'s `binary::wire_census` test module, which repeats these scans.

`check` also holds every `owner` to its grammar, and resolves every owner PIN
(`<lane>@<commit>`) against the development history: the commit must be in
HEAD's history and must be the one that landed the claim.  A bare lane label
cannot be resolved without the network, so `owners` asks the remote which open
claims name a lane that was deleted from it, or are on its main under a lane
that is no branch there or here (gate 0 runs it, and prints SKIP when the
remote cannot be asked), and `pin <lane>` pins that lane's open claims to the
commits that landed them.
"""

from __future__ import annotations

import argparse
import datetime
import functools
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple, Union
from urllib.parse import urlsplit

REGISTRY = "wire-allocations.toml"
TABLES = ("wire_version", "enum_tag", "digest_domain", "scan_exempt")
COUNTED = ("wire_version", "enum_tag", "digest_domain")
VERSION_STATUSES = ("retired", "burned", "landed", "reserved")
TAG_STATUSES = ("landed", "reserved")
DOMAIN_STATUSES = ("burned", "landed", "reserved")
KEYS = {
    "wire_version": ("number", "feature", "constant", "status", "owner", "date", "note"),
    "enum_tag": ("enum", "tag", "variant", "since", "status", "owner", "note"),
    "digest_domain": ("domain", "version", "sep", "status", "binds", "owner", "note"),
    "scan_exempt": ("scan", "name", "reason"),
}

Value = Union[int, str]
KEY = re.compile(r"[a-z_]+\Z")
# A NEW identity is canonical; the legacy spellings are registered because they
# exist and their counters must be locked too, not so anyone mints another.
CANONICAL_DOMAIN = re.compile(r"trust_ir\.[A-Za-z0-9_.\-]*\Z")
IDENTITY = r"[A-Za-z0-9_.\-@:]"
# CLOSED WORLD, anchored on the SUFFIX: a run of identity characters ending in
# `.vN` / `-vN` directly before a closing quote (or the `\0` of a byte-string
# magic).  A prefix-anchored scan was blind to `trust-ir.satres.cnf.v2`, to the
# root separator `trust-ir.sha256-domain.v1`, and to a `concat!` fragment.
VERSIONED_LITERAL = re.compile(rf'(?<!{IDENTITY})({IDENTITY}*[.\-]v[0-9]+)(?:\\0)?"')
SPLIT_LITERAL = re.compile(rf"({IDENTITY}*)([.\-])v([0-9]+)\Z")
OWN_NAMESPACES = ("trust_ir.", "trust-ir.")
SCRATCH = "trust_ir.test."
# OWNERS.  `owner` is a free-text lane label — the branch or roadmap increment
# that holds the claim — or that label PINNED to a commit, `<lane>@<commit>`.
# A branch can be deleted while its claim is open; a pin names the commit that
# landed the claim on main, which every full clone of main can resolve.
OWNER = re.compile(r"([^\s@]+)(?:@([0-9a-f]{7,40}))?\Z")
# The commit that added this registry to main.  Present: this checkout carries
# the development history, so every owner pin MUST resolve.  Absent (an
# exported snapshot, whose history is its own; a shallow clone; no git): a pin
# can only be checked for form, and `check` says so instead of passing quietly.
DEVELOPMENT_ANCHOR = "5c3f25604fe196a8c43c4e3f08944963356a1110"
CENSUS_HOOK = "#[cfg(test)]\nmod wire_census;\n"
CENSUS_FILE = "crates/trust-ir/src/binary/wire_census.rs"
# The live census tests gate 10 requires to have RUN (scripts/ci_gates.sh reads
# this list through `required-census-tests`), so a name filter that matches
# nothing cannot pass.
REQUIRED_CENSUS_TESTS = (
    "registry_has_exactly_the_three_namespaces_and_the_exemption_table",
    "the_two_wire_version_ledgers_agree_number_by_number",
    "every_wire_version_is_registered_and_its_status_is_what_the_reader_does",
    "every_tag_the_codec_writes_is_registered_and_no_two_variants_share_one",
    "every_tag_space_the_codec_spells_is_registered",
    "every_versioned_identity_string_in_the_sources_is_registered",
)
VERSION_CONSTANT = re.compile(
    r"^\s*(?:pub(?:\(crate\))? )?const ([A-Z_0-9]+): u32 = ([0-9]+);", re.M
)


# TWO LEDGERS, ONE COUNTER.  The wire version is recorded both here and in
# `crates/trust-ir/wire_versions.tsv` (`binary::wire_version_ledger`).  Two
# files for one counter disagree silently (git sees no conflict across
# files), so they are bound number by number, this tool writes BOTH, and
# `sync` copies a row made in only one.
VERSION_LEDGER = "crates/trust-ir/wire_versions.tsv"
LEDGER_STATUS = {"retired": "retired", "shipped": "landed", "refused": "burned", "reserved": "reserved"}
TWO_LEDGERS = (
    f"Two ledgers claim this one counter ({REGISTRY} and {VERSION_LEDGER}), and a reservation in only "
    "one of them is invisible to the other's tool. `python3 scripts/wire_alloc.py sync` copies an open "
    "reservation across; `reserve version` and `takeover` write both."
)


class RegistryError(Exception):
    pass


def parse_version_ledger(tsv: str) -> Dict[int, Tuple[str, int, List[str]]]:
    """number -> (status in THIS registry's words, line, the row's columns)."""
    rows: Dict[int, Tuple[str, int, List[str]]] = {}
    for line, raw in enumerate(tsv.splitlines(), start=1):
        if not raw.strip() or raw.startswith("#"):
            continue
        columns = raw.split("\t")
        if not columns[0].isdigit() or len(columns) < 2 or columns[1] not in LEDGER_STATUS:
            raise RegistryError(f"{VERSION_LEDGER}:{line}: expected `<version>TAB<status>TAB...`")
        if int(columns[0]) in rows:
            raise RegistryError(f"{VERSION_LEDGER}:{line}: v{columns[0]} has two rows")
        rows[int(columns[0])] = (LEDGER_STATUS[columns[1]], line, columns)
    return rows


def check_ledgers_agree(tables: Dict[str, List[Row]], tsv: str) -> List[str]:
    try:
        theirs = parse_version_ledger(tsv)
    except RegistryError as error:
        return [str(error)]
    if not theirs:
        return [f"{VERSION_LEDGER} has no rows. {TWO_LEDGERS}"]
    floor = min(theirs)
    ours = {row.fields.get("number"): row.fields.get("status") for row in tables["wire_version"]}
    held = {row.fields.get("number"): row.fields for row in tables["wire_version"]}
    errors = []
    for number, (status, line, columns) in sorted(theirs.items()):
        # Same number, same status, DIFFERENT holder: the race itself, in the
        # one shape a number-by-number comparison cannot see. An open number
        # has ONE owner and ONE constant, and both files must name them.
        if status == "reserved" and ours.get(number) == "reserved" and len(columns) == 5:
            mine = held[number]
            constant = mine.get("constant")
            named = isinstance(constant, str) and re.search(rf"(?<![A-Za-z0-9_]){re.escape(constant)}(?![A-Za-z0-9_])", columns[2])
            if mine.get("owner") != columns[4] or (constant is not None and not named):
                errors.append(
                    f"wire v{number} is reserved in BOTH ledgers, for different holders: {REGISTRY} says owner "
                    f"`{mine.get('owner')}`" + (f", constant `{constant}`" if constant else "") + f"; {VERSION_LEDGER}:{line} "
                    f"says owner `{columns[4]}`, feature `{columns[2]}`. One of you does not hold this number: "
                    "the later reservation moves to the next free one."
                )
        if number not in ours:
            errors.append(
                f"wire v{number} is `{status}` in {VERSION_LEDGER}:{line} and has NO row in {REGISTRY}. {TWO_LEDGERS}"
            )
        elif ours[number] != status:
            errors.append(
                f"wire v{number}: {REGISTRY} says `{ours[number]}`, {VERSION_LEDGER}:{line} says `{status}` "
                f"(in this registry's words). {TWO_LEDGERS}"
            )
    for number, status in sorted(ours.items()):
        predates = isinstance(number, int) and number < floor and status == "retired"
        if number not in theirs and not predates:
            errors.append(f"wire v{number} is `{status}` in {REGISTRY} and has NO row in {VERSION_LEDGER}. {TWO_LEDGERS}")
    return errors


def ledger_row(number: int, feature: str, constant: Optional[str], owner: str) -> str:
    """A `reserved` row as `binary::wire_version_ledger` requires it: the feature
    NAMES the constant, the reserving commit is `self`, the owner is not `-`."""
    text = feature if not constant or constant in feature else f"{feature}: {constant}"
    if "\t" in text + owner or not owner or owner == "-":
        raise RegistryError(f"{VERSION_LEDGER}: an owner is required, and no column may contain a TAB")
    return f"{number}\treserved\t{text}\tself\t{owner}"


def ledger_with(tsv: str, row: str) -> str:
    return tsv + ("" if tsv.endswith("\n") or not tsv else "\n") + row + "\n"


def ledger_renumbered(tsv: str, moved: Dict[int, int]) -> str:
    """Apply a takeover's `old -> new` numbering to the other ledger's rows,
    keeping the file ascending: each moved row lands in its new number's slot."""
    rows = parse_version_ledger(tsv)
    missing = [number for number in moved if number not in rows]
    if missing:
        raise RegistryError(f"{VERSION_LEDGER} has no row for v{missing[0]}; run `wire_alloc.py sync` first")
    lines = tsv.splitlines()
    for old, new in moved.items():
        lines[rows[new][1] - 1] = "\t".join([str(new)] + rows[old][2][1:])
    return "\n".join(lines) + "\n"


CONSTANT_IN_FEATURE = re.compile(r"\b([A-Z][A-Z0-9_]*_FORMAT_VERSION)\b")


def sync(text: str, tsv: str, today: str) -> Tuple[str, str, List[str]]:
    """Copy each OPEN reservation that only one ledger has into the other.
    Anything else the two disagree about needs a human, and `check` says what."""
    tables = parse(text)
    theirs = parse_version_ledger(tsv)
    ours = {row.get("number", int): row for row in tables["wire_version"]}
    done: List[str] = []
    for number in sorted(set(theirs) - set(ours)):
        status, _, columns = theirs[number]
        if status != "reserved" or number != max(ours) + 1 or len(columns) != 5:
            continue
        feature = columns[2].replace('"', "'").replace("\\", "/")
        fields: List[Tuple[str, Value]] = [("number", number), ("feature", feature)]
        named = CONSTANT_IN_FEATURE.search(columns[2])
        if named:
            fields.append(("constant", named.group(1)))
        fields += [("status", "reserved"), ("owner", columns[4]), ("date", today)]
        text = insert_row(text, "wire_version", render(fields), None)
        ours[number] = parse(text)["wire_version"][-1]
        done.append(f"wire v{number}: {VERSION_LEDGER} -> {REGISTRY}")
    for number in sorted(set(ours) - set(theirs)):
        row = ours[number]
        if row.fields.get("status") != "reserved" or number != max(theirs, default=0) + 1:
            continue
        constant = row.fields.get("constant")
        tsv = ledger_with(tsv, ledger_row(number, str(row.fields["feature"]), constant if isinstance(constant, str) else None, str(row.fields["owner"])))
        theirs = parse_version_ledger(tsv)
        done.append(f"wire v{number}: {REGISTRY} -> {VERSION_LEDGER}")
    return text, tsv, done


class Row:
    def __init__(self, line: int, fields: Dict[str, Value]) -> None:
        self.line = line
        self.fields = fields

    def get(self, key: str, kind: type) -> Value:
        value = self.fields.get(key)
        if not isinstance(value, kind):
            raise RegistryError(f"line {self.line}: `{key}` must be a {kind.__name__}")
        return value


def parse_fields(inner: str, line: int) -> Dict[str, Value]:
    fields: Dict[str, Value] = {}
    rest = inner
    while True:
        key, sep, after = rest.partition(" = ")
        if not sep or not KEY.match(key):
            raise RegistryError(f"line {line}: expected `key = value` in `{rest}`")
        value: Value
        if after.startswith('"'):
            end = after.find('"', 1)
            if end < 0:
                raise RegistryError(f"line {line}: unterminated string for `{key}`")
            value = after[1:end]
            if "\\" in value:
                raise RegistryError(f"line {line}: escapes are not allowed in `{key}`")
            after = after[end + 1 :]
        else:
            digits, comma, tail = after.partition(",")
            if not re.match(r"(0|[1-9][0-9]*)\Z", digits):
                raise RegistryError(f"line {line}: `{key}` is not a plain integer")
            value = int(digits)
            after = comma + tail
        if key in fields:
            raise RegistryError(f"line {line}: key `{key}` given twice")
        fields[key] = value
        if not after:
            return fields
        if not after.startswith(", "):
            raise RegistryError(f"line {line}: expected `, ` after `{key}`")
        rest = after[2:]


def parse(text: str) -> Dict[str, List[Row]]:
    """The same strict one-row-per-line TOML subset `wire_census.rs` parses."""

    tables: Dict[str, List[Row]] = {}
    current: Optional[str] = None
    for number, raw in enumerate(text.splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if current is None:
            if not line.endswith(" = [") or not KEY.match(line[: -len(" = [")]):
                raise RegistryError(f"line {number}: expected `name = [`, got `{line}`")
            current = line[: -len(" = [")]
            if current in tables:
                raise RegistryError(f"line {number}: table `{current}` opened twice")
            tables[current] = []
        elif line == "]":
            current = None
        else:
            if not (line.startswith("{ ") and line.endswith(" },")):
                raise RegistryError(
                    f"line {number}: a row is `{{ key = value, ... }},` on one line"
                )
            tables[current].append(Row(number, parse_fields(line[2:-3], number)))
    if current is not None:
        raise RegistryError(f"table `{current}` is never closed with `]`")
    return tables


def scan_version_constants(binary_src: str) -> List[Tuple[str, int]]:
    return [
        (name, int(value))
        for name, value in VERSION_CONSTANT.findall(binary_src)
        if name == "VERSION" or name.endswith("_FORMAT_VERSION")
    ]


TEST_GATE = re.compile(r"#\[cfg\((?:test|all\(test,.*)\)\]\Z")
MODULE = re.compile(r"(?:pub(?:\(crate\))? )?mod \w+ ?([;{])\Z")


def production_lines(src: str) -> List[str]:
    """`src` as lines with every `#[cfg(test)]` / `#[cfg(all(test, ..))]` MODULE
    blanked (line numbers preserved).  Test code is not in the artifact, so it
    spells nothing that ships.  Only MODULES are blanked; any other test-gated
    item stays in view, which can only fail closed.  Relies on rustfmt's layout
    (the closing brace sits at the item's own indentation), which the
    `workspace-format` gate holds; an unclosed module is an error."""

    lines = src.split("\n")
    out = list(lines)
    i = 0
    while i < len(lines):
        if TEST_GATE.match(lines[i].strip()):
            indent = lines[i][: len(lines[i]) - len(lines[i].lstrip())]
            j = i + 1
            while j < len(lines) and lines[j].lstrip().startswith("#["):
                j += 1
            module = MODULE.match(lines[j][len(indent) :]) if j < len(lines) and lines[j].startswith(indent) else None
            end = None
            if module and module.group(1) == ";":
                end = j
            elif module:
                close = indent + "}"
                end = next((k for k in range(j + 1, len(lines)) if lines[k] == close), None)
                if end is None:
                    raise RegistryError(f"line {i + 1}: a test module is never closed at its own indentation")
            if end is not None:
                for k in range(i, end + 1):
                    out[k] = ""
                i = end + 1
                continue
        i += 1
    return out


def scan_literals(root: Path) -> List[str]:
    """Every versioned identity spelled under `crates/*/src` and `frontend/src`
    (doc comments included: a documented identity is a claimed one), skipping
    `tests.rs`, `tests/` and inline test modules."""

    found = set()
    sources = sorted((root / "crates").glob("*/src")) + [root / "frontend" / "src"]
    for src in sources:
        if not src.is_dir():
            continue
        for path in sorted(src.rglob("*.rs")):
            relative = path.relative_to(src).parts
            if path.name == "tests.rs" or "tests" in relative[:-1]:
                continue
            try:
                found.update(_source_literals(path.read_text(encoding="utf-8")))
            except RegistryError as error:
                raise RegistryError(f"{path.relative_to(root)}: {error}") from None
    return sorted(found)


@functools.lru_cache(maxsize=4096)
def _source_literals(text: str) -> Tuple[str, ...]:
    """`literals_in(production_lines(text))`, once per distinct source text
    (both are pure; the script tests scan the same tree many times). An
    error is raised every time: lru_cache keeps no exception."""
    return tuple(literals_in(production_lines(text)))


def literals_in(lines: Sequence[str]) -> List[str]:
    return [
        literal
        for line in lines
        for literal in VERSIONED_LITERAL.findall(line)
        if not literal.startswith(SCRATCH)
    ]


ENUM_PATH = re.compile(r"\b([A-Z][A-Za-z0-9_]*)::(?=[A-Z])")
NOT_ENUM_PATHS = ("BinaryError", "Self")
LITERAL_ARM = re.compile(r"\s*([0-9]+(?:\s*\|\s*[0-9]+)*)\s*(?: if .*?)?=>\s*(.*)\Z")
WRITES_LITERAL = re.compile(r"write_u8\([^)]*,\s*[0-9]+\s*\)")


# A level-generic carrier (amendment S) is spelled `TyG::` / `InstG::` /
# `ConstantG::` in the generic codec; its tag space is the level-R alias.
LEVEL_GENERIC = {"TyG": "Ty", "InstG": "Inst", "ConstantG": "Constant"}


def enum_paths(text: str) -> List[str]:
    return [LEVEL_GENERIC.get(name, name) for name in ENUM_PATH.findall(text) if name not in NOT_ENUM_PATHS]


def indent_of(line: str) -> int:
    return len(line) - len(line.lstrip())


def enclosing_match(lines: Sequence[str], site: int) -> Optional[int]:
    """The header of the `match` enclosing line `site`, stepping OUT one block
    at a time so a `match` nested in an earlier arm is never mistaken for it."""

    level = indent_of(lines[site])
    for j in range(site - 1, -1, -1):
        stripped = lines[j].strip()
        if not stripped or stripped.startswith("//") or indent_of(lines[j]) >= level:
            continue
        if stripped.endswith("{") and re.search(r"\bmatch\b", stripped):
            return j
        level = indent_of(lines[j])
        if level == 0:
            return None
    return None


def scan_tag_spaces(binary_src: str) -> Tuple[Dict[str, int], List[int]]:
    """See `_scan_tag_spaces`; a fresh copy of its memoized answer."""
    spaces, unattributed = _scan_tag_spaces_memo(binary_src)
    return dict(spaces), list(unattributed)


@functools.lru_cache(maxsize=64)
def _scan_tag_spaces_memo(binary_src: str) -> Tuple[Tuple[Tuple[str, int], ...], Tuple[int, ...]]:
    spaces, unattributed = _scan_tag_spaces(binary_src)
    return tuple(spaces.items()), tuple(unattributed)


def _scan_tag_spaces(binary_src: str) -> Tuple[Dict[str, int], List[int]]:
    """(enum -> first evidence line, unattributable refusal lines).

    The list of tag spaces the census samples is hand-kept, and on the day it
    landed it was one short (`DiagnosticSeverity`, written inline).  So the
    codec SOURCE is scanned for every way it spells "a literal tag byte <-> an
    enum variant", in both directions: `tag_enum!` heads; REFUSAL ARMS (every
    `BinaryError::InvalidTag(..)` closes a tag match, which names its enum(s),
    or is a `0 => None / 1 => Some` presence byte, or is unattributable); and
    WRITE ARMS (`Enum::Variant.. => <literal>` / `=> write_u8(.., <literal>)`).
    The same scan, line for line, is `scan_tag_spaces` in wire_census.rs."""

    lines = production_lines(binary_src)
    i = 0
    while i < len(lines):
        if lines[i].startswith("macro_rules! "):
            end = next((k for k in range(i + 1, len(lines)) if lines[k] == "}"), None)
            if end is None:
                raise RegistryError(f"line {i + 1}: `macro_rules!` is never closed")
            for k in range(i, end + 1):
                lines[k] = ""
            i = end
        i += 1

    spelled: Dict[str, int] = {}
    refusals: List[int] = []
    for index, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("//"):
            continue
        if line.startswith("tag_enum!("):
            parts = line[len("tag_enum!(") :].split(",")
            if len(parts) < 3 or not parts[2].strip():
                raise RegistryError(f"line {index + 1}: unreadable `tag_enum!` head")
            spelled.setdefault(parts[2].strip(), index + 1)
        if "BinaryError::InvalidTag(" in stripped and "=> write!(" not in stripped:
            refusals.append(index)
        if " => " in stripped:
            pattern, rhs = stripped.split(" => ", 1)
            while pattern.startswith("Some(") or pattern.startswith("&"):
                pattern = pattern[5:] if pattern.startswith("Some(") else pattern[1:]
            path = re.match(r"[A-Za-z0-9_:]*", pattern).group(0)
            rhs = rhs.rstrip(",")
            following = next((l.strip() for l in lines[index + 1 :] if l.strip()), "")
            literal = (
                rhs.isdigit()
                or WRITES_LITERAL.match(rhs) is not None
                or (rhs == "{" and WRITES_LITERAL.match(following) is not None)
            )
            if literal and enum_paths(path):
                spelled.setdefault(enum_paths(path)[0], index + 1)
    unattributed: List[int] = []
    for site in refusals:
        header = enclosing_match(lines, site)
        if header is None:
            unattributed.append(site + 1)
            continue
        arm_indent = indent_of(lines[header]) + 4
        arms = [
            (re.split(r"\s*\|\s*", m.group(1)), m.group(2).strip())
            for m in (LITERAL_ARM.match(l) for l in lines[header + 1 : site] if indent_of(l) == arm_indent)
            if m
        ]
        named = sorted(
            {name for l in lines[header : site + 1] if not l.lstrip().startswith("//") for name in enum_paths(l)}
        )
        presence = (
            [a for a, _ in arms] == [["0"], ["1"]]
            and arms[0][1].rstrip(",") in ("None", "Ok(None)", "false", "Ok(false)")
        )
        if named:
            for name in named:
                spelled.setdefault(name, header + 1)
        elif not presence:
            unattributed.append(site + 1)
    return spelled, unattributed


def check(
    tables: Dict[str, List[Row]],
    binary_src: str,
    domains: Sequence[str],
    version_ledger: Optional[str] = None,
) -> List[str]:
    """`domains` is every versioned identity the sources spell (`scan_literals`);
    `version_ledger` is the text of the OTHER wire-version ledger (the CLI always
    passes it; None skips the binding, for tests of everything else)."""

    errors: List[str] = []

    def guarded(row: Row, table: str, body) -> None:
        try:
            unknown = [key for key in row.fields if key not in KEYS[table]]
            if unknown:
                raise RegistryError(f"line {row.line}: unknown key `{unknown[0]}`")
            body()
        except RegistryError as error:
            errors.append(str(error))

    if sorted(tables) != sorted(TABLES):
        errors.append(f"registry tables must be exactly {sorted(TABLES)}, found {sorted(tables)}")
        return errors

    # --- owners: a lane label, or one pinned to a commit ------------------
    for table in COUNTED:
        for row in tables[table]:
            owner = row.fields.get("owner")
            if owner is not None and (not isinstance(owner, str) or not OWNER.match(owner)):
                errors.append(
                    f"line {row.line}: owner `{owner}` is neither a lane label (no space, no `@`) nor "
                    "a pinned one, `<lane>@<commit>` with a 7-40 digit lowercase hex commit"
                )

    # --- wire versions -----------------------------------------------------
    status_of: Dict[int, str] = {}
    constants: Dict[str, int] = {}
    for index, row in enumerate(tables["wire_version"], start=1):

        def body(row: Row = row, index: int = index) -> None:
            number = row.get("number", int)
            status = row.get("status", str)
            if status not in VERSION_STATUSES:
                raise RegistryError(f"line {row.line}: status `{status}` not in {VERSION_STATUSES}")
            if not row.get("feature", str) or not row.get("owner", str):
                raise RegistryError(f"line {row.line}: `feature` and `owner` are required")
            if number != index:
                errors.append(
                    f"line {row.line}: wire versions must be unique, strictly increasing and "
                    f"gap-free — expected {index}, found {number}"
                )
            status_of[number] = status
            if "constant" in row.fields:
                constants[row.get("constant", str)] = number

        guarded(row, "wire_version", body)
    declared = scan_version_constants(binary_src)
    latest = dict(declared).get("VERSION")
    if latest is None:
        errors.append("binary.rs declares no literal `VERSION` constant")
    for name, number in declared:
        if status_of.get(number) != "landed":
            errors.append(
                f"binary.rs declares `{name} = {number}` but {REGISTRY} has no `landed` "
                f"wire_version row numbered {number} — reserve FIRST"
            )
        if name != "VERSION" and constants.get(name) != number:
            errors.append(
                f"binary.rs declares `{name} = {number}` but no wire_version row carries "
                f'`constant = "{name}"` at number {number}'
            )
    for name, number in constants.items():
        value = dict(declared).get(name)
        if value is None and status_of.get(number) != "reserved":
            errors.append(f"wire_version {number} names `{name}`, which binary.rs does not declare")
        elif value is not None and value != number:
            errors.append(f"wire_version {number} names `{name}`, which binary.rs declares as {value}")
    landed = [number for number, status in status_of.items() if status == "landed"]
    if latest is not None and (not landed or max(landed) != latest):
        errors.append(f"VERSION is {latest} but the highest landed wire_version row is {max(landed, default=None)}")
    for number, status in status_of.items():
        if status == "reserved" and latest is not None and number <= latest:
            errors.append(f"wire version {number} is reserved but VERSION is already {latest}")
    if version_ledger is not None:
        errors.extend(check_ledgers_agree(tables, version_ledger))

    # --- enum tags ---------------------------------------------------------
    closed: set = set()
    previous: Optional[Tuple[str, int]] = None
    variants: set = set()
    for row in tables["enum_tag"]:

        def body(row: Row = row) -> None:
            nonlocal previous
            enum, tag = row.get("enum", str), row.get("tag", int)
            variant, since = row.get("variant", str), row.get("since", int)
            status = row.get("status", str)
            if status not in TAG_STATUSES:
                raise RegistryError(f"line {row.line}: status `{status}` not in {TAG_STATUSES}")
            if tag > 255:
                raise RegistryError(f"line {row.line}: `tag` exceeds one byte")
            if previous is not None and previous[0] == enum:
                if tag <= previous[1]:
                    errors.append(
                        f"line {row.line}: {enum} tag {tag} does not follow tag {previous[1]} — "
                        "tags are unique and strictly increasing within an enum"
                    )
            elif previous is not None:
                closed.add(previous[0])
                if enum in closed:
                    errors.append(f"line {row.line}: rows of enum {enum} must be contiguous")
            previous = (enum, tag)
            if (enum, variant) in variants:
                errors.append(f"line {row.line}: {enum}::{variant} has two rows")
            variants.add((enum, variant))
            if since not in status_of:
                errors.append(f"line {row.line}: `since = {since}` is not a registered wire version")
            elif status == "landed" and status_of[since] == "reserved":
                errors.append(f"line {row.line}: {enum}::{variant} is landed but v{since} is only reserved")

        guarded(row, "enum_tag", body)

    # --- scan exemptions ---------------------------------------------------
    literal_prefixes: Dict[str, int] = {}
    exempt_spaces: Dict[str, int] = {}
    last_exempt: Optional[Tuple[str, str]] = None
    for row in tables["scan_exempt"]:

        def body(row: Row = row) -> None:
            nonlocal last_exempt
            scan, name = row.get("scan", str), row.get("name", str)
            if not row.get("reason", str):
                raise RegistryError(f"line {row.line}: an exemption must give its `reason`")
            if scan == "literal":
                own = any(o.startswith(name) or name.startswith(o) for o in OWN_NAMESPACES)
                if len(name) < 3 or name[-1] not in ".-:":
                    errors.append(
                        f"line {row.line}: a `literal` exemption is a NAMESPACE PREFIX — at least three "
                        f"characters, ending in `.`, `-` or `:` — not `{name}`"
                    )
                elif own:
                    errors.append(
                        f"line {row.line}: `{name}` overlaps TrustIr's own namespace {list(OWN_NAMESPACES)}, "
                        "which this registry allocates; it cannot be exempted"
                    )
                else:
                    literal_prefixes[name] = row.line
            elif scan == "tag-space":
                if re.match(r"[A-Z][A-Za-z0-9]*\Z", name):
                    exempt_spaces[name] = row.line
                else:
                    errors.append(f"line {row.line}: a `tag-space` exemption names a Rust enum, not `{name}`")
            else:
                errors.append(f'line {row.line}: scan `{scan}` is not one of ["literal", "tag-space"]')
            if last_exempt is not None and last_exempt >= (scan, name):
                errors.append(f"line {row.line}: scan_exempt rows must be unique and sorted by (scan, name)")
            last_exempt = (scan, name)

        guarded(row, "scan_exempt", body)

    # --- tag spaces: the hand-kept list, cross-checked against the source -----
    registered_spaces = {row.fields.get("enum") for row in tables["enum_tag"]}
    try:
        spelled_spaces, unattributed = scan_tag_spaces(binary_src)
    except RegistryError as error:
        errors.append(f"binary.rs: {error}")
        spelled_spaces, unattributed = {}, []
    for name, line in sorted(spelled_spaces.items()):
        if name not in registered_spaces and name not in exempt_spaces:
            errors.append(
                f"binary.rs:{line}: the codec matches a literal tag byte to or from `{name}::..`, but "
                f"`{name}` is not a registered tag space. Register every tag it writes in {REGISTRY} and give "
                f"it a probe and a TAG_SPACES row in binary/wire_census.rs. If `{name}` is NOT a wire enum, "
                f'say so: {{ scan = "tag-space", name = "{name}", reason = "<why>" }},'
            )
    for line in unattributed:
        errors.append(
            f"binary.rs:{line}: a closed tag match (it refuses unknown bytes with `InvalidTag`) names no "
            "enum and is not a `0 => None / 1 => Some` presence byte, so the census cannot tell which tag "
            "space it decodes. Name the enum in the match arms."
        )
    for name in sorted(n for n in registered_spaces if isinstance(n, str) and n not in spelled_spaces):
        errors.append(
            f"the tag-space scan no longer sees `{name}`, a registered tag space: the way binary.rs spells "
            "it has left the scanner's patterns (scan_tag_spaces), so the scan can no longer vouch that NO "
            "space is missing"
        )
    for name, line in exempt_spaces.items():
        if name in registered_spaces or name not in spelled_spaces:
            errors.append(
                f"line {line}: the `tag-space` exemption for `{name}` exempts nothing (it is registered, "
                "or binary.rs no longer spells it): delete the row"
            )

    # --- the compiled half is still hooked in -----------------------------
    # Gate 10 selects the census by test NAME. If a merge drops this one line,
    # that filter matches nothing and `cargo test` exits 0 over zero tests.
    if CENSUS_HOOK not in binary_src:
        errors.append(
            "binary.rs no longer declares `#[cfg(test)] mod wire_census;`: the compiled census "
            f"({CENSUS_FILE}) is orphaned and every tag-byte and reader-status check is OFF"
        )

    # --- digest domains ----------------------------------------------------
    registered: Dict[str, Tuple[str, int]] = {}
    seps: Dict[str, str] = {}
    settled: set = set()
    reserved_rows: List[Tuple[str, str, int]] = []
    last: Optional[Tuple[str, int]] = None
    for row in tables["digest_domain"]:

        def body(row: Row = row) -> None:
            nonlocal last
            domain, version = row.get("domain", str), row.get("version", int)
            status = row.get("status", str)
            if status not in DOMAIN_STATUSES:
                raise RegistryError(f"line {row.line}: status `{status}` not in {DOMAIN_STATUSES}")
            if not row.get("binds", str):
                raise RegistryError(f"line {row.line}: `binds` must say what the digest binds")
            sep = row.get("sep", str) if "sep" in row.fields else "."
            if "sep" in row.fields and sep != "-":
                raise RegistryError(f'line {row.line}: `sep` is "-" or absent (meaning "."), not "{sep}"')
            full = f"{domain}{sep}v{version}"
            split = SPLIT_LITERAL.match(full)
            if not domain or not split or (split.group(1), split.group(2), int(split.group(3))) != (domain, sep, version):
                errors.append(f"line {row.line}: `{full}` is not a `<name>.vN` / `<name>-vN` identity")
            if seps.setdefault(domain, sep) != sep:
                errors.append(f"line {row.line}: `{domain}` is spelled with two different separators")
            if status == "reserved":
                reserved_rows.append((domain, sep, row.line))
            else:
                settled.add(domain)
            if last is not None and last >= (domain, version):
                errors.append(
                    f"line {row.line}: digest_domain rows must be unique and sorted by (domain, version)"
                )
            last = (domain, version)
            registered[full] = (status, row.line)

        guarded(row, "digest_domain", body)
    for domain, sep, line in reserved_rows:
        if domain not in settled and not (CANONICAL_DOMAIN.match(domain) and sep == "."):
            errors.append(
                f"line {line}: a NEW identity is spelled `trust_ir.<dotted.name>.vN`, not `{domain}`: "
                "only a bump of an existing legacy-spelled name keeps its spelling"
            )
    used: set = set()
    for literal in domains:
        prefix = next((p for p in literal_prefixes if literal.startswith(p)), None)
        if prefix is not None:
            used.add(prefix)
            continue
        status_line = registered.get(literal)
        if status_line is None:
            errors.append(
                f"the sources spell the versioned identity `{literal}` but {REGISTRY} has no digest_domain "
                "row for it — reserve FIRST. A version-suffixed FRAGMENT counts: an identity assembled with "
                "`concat!` or `format!` is one nobody can register. If another repository allocates this "
                'name, exempt its namespace: { scan = "literal", name = "<namespace prefix>", reason = "<who allocates it>" },'
            )
        elif status_line[0] != "landed":
            errors.append(
                f"line {status_line[1]}: `{literal}` is spelled in the sources but its row is `{status_line[0]}`"
            )
    for literal, (status, line) in registered.items():
        if status == "landed" and literal not in domains:
            errors.append(f"line {line}: `{literal}` is landed but no source spells it (retire it as burned)")
    for prefix, line in literal_prefixes.items():
        if prefix not in used:
            errors.append(f"line {line}: the `literal` exemption `{prefix}` exempts nothing the sources spell: delete the row")
    return errors


def git(root: Path, *args: str, timeout: Optional[float] = None) -> Optional[subprocess.CompletedProcess]:
    """`git -C root ...`, or None where there is no git to ask (or it did not
    answer within `timeout` seconds)."""
    try:
        return subprocess.run(
            ["git", "-C", str(root), *args], capture_output=True, text=True, check=False, timeout=timeout,
            env={**os.environ, "GIT_TERMINAL_PROMPT": "0"},
        )
    except (OSError, subprocess.TimeoutExpired):
        return None


def has_development_history(root: Path, anchor: Optional[str] = None) -> bool:
    """Does `root` carry this repository's development history (`anchor`, by
    default DEVELOPMENT_ANCHOR, read when called)?"""
    found = git(root, "cat-file", "-e", f"{DEVELOPMENT_ANCHOR if anchor is None else anchor}^{{commit}}")
    return found is not None and found.returncode == 0


def owner_pins(tables: Dict[str, List[Row]]) -> List[Tuple[str, Row, str, str]]:
    """(table, row, lane, pin) of every pinned owner, in all three namespaces."""
    pins = []
    for table in COUNTED:
        for row in tables[table]:
            owner = row.fields.get("owner")
            match = OWNER.match(owner) if isinstance(owner, str) else None
            if match and match.group(2):
                pins.append((table, row, match.group(1), match.group(2)))
    return pins


def table_of(fields: Dict[str, Value]) -> Optional[str]:
    for key, table in (("number", "wire_version"), ("enum", "enum_tag"), ("domain", "digest_domain")):
        if key in fields:
            return table
    return None


def same_claim(table: str, claim: Dict[str, Value], row: Dict[str, Value]) -> bool:
    """Is `row` (a registry row, or a version-ledger row as `ledger_feature`) a
    row for `claim`?  Matched on what a renumbering leaves alone: a takeover
    moves a wire version's number and its tags' `since`, never the constant,
    the feature, the enum or the variant."""
    if table == "wire_version":
        constant = claim.get("constant")
        if "ledger_feature" in row:
            column = str(row["ledger_feature"])
            if isinstance(constant, str):
                return re.search(rf"(?<![A-Za-z0-9_]){re.escape(constant)}(?![A-Za-z0-9_])", column) is not None
            return column == claim.get("feature") or column.startswith(f"{claim.get('feature')}: ")
        if table_of(row) != table:
            return False
        if isinstance(constant, str):
            return row.get("constant") == constant
        return row.get("feature") == claim.get("feature")
    if table_of(row) != table:
        return False
    if table == "enum_tag":
        return row.get("enum") == claim.get("enum") and row.get("variant") == claim.get("variant")
    return row.get("domain") == claim.get("domain") and row.get("version") == claim.get("version")


def ledger_rows_changed(root: Path, commit: str) -> Optional[List[Tuple[str, Dict[str, Value]]]]:
    """('+' or '-', fields) of every row `commit` adds or removes in either
    ledger, against its FIRST parent (a merge onto main is judged by what it
    brought to main; a root commit, against nothing).  None when git cannot say."""
    parent = git(root, "rev-parse", "--verify", "--quiet", f"{commit}^1")
    if parent is None:
        return None
    common = ("--no-ext-diff", "--no-textconv", "--no-color", "--no-renames", "--src-prefix=a/", "--dst-prefix=b/", "-U0")
    if parent.returncode == 0:
        diff = git(root, "diff", *common, parent.stdout.strip(), commit, "--", REGISTRY, VERSION_LEDGER)
    else:
        diff = git(root, "show", *common, "--format=", commit, "--", REGISTRY, VERSION_LEDGER)
    if diff is None or diff.returncode != 0:
        return None
    rows: List[Tuple[str, Dict[str, Value]]] = []
    current: Optional[str] = None
    for line in diff.stdout.splitlines():
        if line.startswith(("+++ ", "--- ")):
            if line.startswith("+++ "):
                current = line[len("+++ b/") :] if line.startswith("+++ b/") else None
            continue
        if not line.startswith(("+", "-")):
            continue
        sign, body = line[0], line[1:]
        if current == REGISTRY:
            text = body.strip()
            if text.startswith("{ ") and text.endswith(" },"):
                try:
                    rows.append((sign, parse_fields(text[2:-3], 0)))
                except RegistryError:
                    continue
        elif current == VERSION_LEDGER and not body.startswith("#"):
            columns = body.split("\t")
            if len(columns) == 5 and columns[0].isdigit():
                rows.append((sign, {"number": int(columns[0]), "ledger_feature": columns[2]}))
    return rows


def introduces(table: str, claim: Dict[str, Value], changed: Sequence[Tuple[str, Dict[str, Value]]]) -> bool:
    """Did the commit whose ledger changes are `changed` INTRODUCE `claim`: add
    a row for it and remove none?  A takeover, a note edit or a pin rewrites
    the row (one line out, one in) and introduces nothing."""
    added = any(sign == "+" and same_claim(table, claim, row) for sign, row in changed)
    removed = any(sign == "-" and same_claim(table, claim, row) for sign, row in changed)
    return added and not removed


def unresolved_pins(
    tables: Dict[str, List[Row]], root: Path, anchor: Optional[str] = None
) -> Tuple[Dict[int, str], str]:
    """({row line: why its pin does not resolve}, what was established).

    Where `root` carries the development history (`anchor`, by default
    DEVELOPMENT_ANCHOR, is a commit there), a pin must name exactly one commit,
    that commit must be in HEAD's history (a commit on main, which no branch
    deletion can take away; a branch tip that survives in this clone's object
    store is the fragile name a pin replaces), and it must be the commit that
    LANDED the claim: one that introduced a row for it in either ledger.  Any
    other commit on main would make the audit green while naming nothing about
    the claim.  Where the history is absent, a pin is checked for FORM only and
    the result says so."""

    pins = owner_pins(tables)
    if not pins:
        return {}, "no owner is pinned"
    if not has_development_history(root, anchor):
        named = DEVELOPMENT_ANCHOR if anchor is None else anchor
        return {}, (
            f"{len(pins)} owner pin(s) checked for FORM ONLY: this checkout does not carry the "
            f"development history ({named[:8]} is absent), so no pin was resolved"
        )
    problems: Dict[int, str] = {}
    changes: Dict[str, Optional[List[Tuple[str, Dict[str, Value]]]]] = {}
    for table, row, lane, pin in pins:
        owner = f"{lane}@{pin}"
        found = git(root, "rev-parse", "--verify", "--quiet", f"{pin}^{{commit}}")
        if found is None or found.returncode != 0:
            problems[row.line] = (
                f"line {row.line}: owner `{owner}` pins `{pin}`, which is no commit here (or an "
                f"ambiguous abbreviation): pin the commit that landed this claim on main (`wire_alloc.py pin {lane}`)"
            )
            continue
        commit = found.stdout.strip()
        ancestor = git(root, "merge-base", "--is-ancestor", commit, "HEAD")
        if ancestor is None or ancestor.returncode != 0:
            problems[row.line] = (
                f"line {row.line}: owner `{owner}` pins {commit[:12]}, which is not in HEAD's "
                "history. A pin must name a commit on main (the one that landed the claim), which "
                "every full clone resolves; a branch tip can be deleted, which is what a pin replaces"
            )
            continue
        if commit not in changes:
            changes[commit] = ledger_rows_changed(root, commit)
        changed = changes[commit]
        if changed is None:
            problems[row.line] = f"line {row.line}: owner `{owner}`: git could not show what {commit[:12]} changed"
        elif not introduces(table, row.fields, changed):
            problems[row.line] = (
                f"line {row.line}: owner `{owner}` pins {commit[:12]}, which is on main but did not land "
                f"{claim_name(table, row)}: it introduced no row for it in {REGISTRY} or {VERSION_LEDGER}. "
                f"A pin names the commit that landed its claim; `wire_alloc.py pin {lane}` finds it"
            )
    return problems, f"{len(pins)} owner pin(s) name the commit in HEAD's history that landed their claim"


def landing_commit(root: Path, table: str, row: Row) -> Optional[str]:
    """The most recent commit in HEAD's history that introduced a row for this
    claim (the newest, so a number released and claimed again names its
    current claim), or None."""
    fields = row.fields
    if table == "wire_version":
        needle = str(fields.get("constant") or fields.get("feature"))
    elif table == "enum_tag":
        needle = f'variant = "{fields.get("variant")}"'
    else:
        needle = f'domain = "{fields.get("domain")}", version = {fields.get("version")}'
    listed = git(root, "log", "--format=%H", f"-S{needle}", "HEAD", "--", REGISTRY, VERSION_LEDGER)
    if listed is None or listed.returncode != 0:
        return None
    for commit in listed.stdout.split():
        changed = ledger_rows_changed(root, commit)
        if changed is not None and introduces(table, fields, changed):
            return commit
    return None


def pin_lane(text: str, tsv: str, root: Path, lane: str) -> Tuple[str, str, List[str]]:
    """Pin every OPEN claim whose owner is the bare `lane` to the commit that
    landed it, in both wire-version ledgers.  Refused, changing nothing, when
    a claim's landing commit cannot be found (an uncommitted reservation)."""
    if not OWNER.match(lane) or "@" in lane:
        raise RegistryError(f"`{lane}` is not a bare lane label")
    if not has_development_history(root):
        raise RegistryError(
            f"this checkout does not carry the development history ({DEVELOPMENT_ANCHOR[:8]} is absent): "
            "there is no landing commit to pin to"
        )
    tables = parse(text)
    lines = text.splitlines()
    ledger = tsv.splitlines()
    ledger_line = {number: line for number, (_, line, _) in parse_version_ledger(tsv).items()}
    done: List[str] = []
    for table in COUNTED:
        for row in tables[table]:
            if row.fields.get("status") != "reserved" or row.fields.get("owner") != lane:
                continue
            commit = landing_commit(root, table, row)
            if commit is None:
                raise RegistryError(
                    f"line {row.line}: no commit in HEAD's history introduced {claim_name(table, row)}; "
                    "commit the reservation first, or pin it by hand to the commit that landed it"
                )
            pinned = f"{lane}@{commit[:12]}"
            lines[row.line - 1] = render([(k, pinned if k == "owner" else v) for k, v in row.fields.items()])
            number = row.fields.get("number")
            if table == "wire_version" and number in ledger_line:
                columns = ledger[ledger_line[number] - 1].split("\t")
                if len(columns) == 5 and columns[4] == lane:
                    columns[4] = pinned
                    ledger[ledger_line[number] - 1] = "\t".join(columns)
            done.append(f"{claim_name(table, row)}: owner `{pinned}`")
    if not done:
        raise RegistryError(f"no open claim is owned by the bare lane `{lane}`")
    return "\n".join(lines) + "\n", "\n".join(ledger) + "\n", done


def claim_name(table: str, row: Row) -> str:
    fields = row.fields
    if table == "wire_version":
        return f"wire v{fields.get('number')}"
    if table == "enum_tag":
        return f"{fields.get('enum')} tag {fields.get('tag')}"
    return f"{fields.get('domain')}{fields.get('sep', '.')}v{fields.get('version')}"


# The remote branch names this clone's audits have seen, kept in the clone's
# own git directory: a lane once seen on the remote and now absent from it was
# DELETED, even after a pruning fetch removed its remote-tracking ref.
SEEN_LANES = "wire-alloc-seen-remote-branches"
# Listing the remote is the audit's one network call; past this it is NOT
# JUDGED (exit 2), never a hang in gate 0.
REMOTE_TIMEOUT_SECONDS = 120
# The branch claims land on.  An open claim that is on the remote's MAIN_BRANCH
# under a bare label no branch carries resolves only in the clone that wrote it.
MAIN_BRANCH = "main"
MERGED_FROM_REMOTE = (
    r"^Merge remote-tracking branch '{remote}/{lane}'",
    r"^Merge pull request #[0-9]+ from [^/\s]+/{lane}$",
)


def seen_lanes(root: Path, remote: str, now: Sequence[str]) -> set:
    """The branches of `remote` this clone has ever seen, `now` included, and
    remember `now` for the next audit.  Best effort: no git directory, no memory."""
    found = git(root, "rev-parse", "--path-format=absolute", "--git-common-dir")
    if found is None or found.returncode != 0:
        return set(now)
    path = Path(found.stdout.strip()) / SEEN_LANES
    prefix = f"{remote}\t"
    try:
        recorded = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        recorded = []
    known = {line[len(prefix) :] for line in recorded if line.startswith(prefix)}
    others = [line for line in recorded if line and not line.startswith(prefix)]
    union = known | set(now)
    if union != known:
        try:
            scratch = path.with_name(f"{SEEN_LANES}.{os.getpid()}")
            scratch.write_text("".join(f"{line}\n" for line in others + [prefix + name for name in sorted(union)]), encoding="utf-8")
            os.replace(scratch, path)
        except OSError:
            pass
    return union


def remote_branches(root: Path, remote: str) -> Tuple[Optional[Dict[str, str]], str]:
    """Ask GitHub through AGH; reject ambiguous GitHub URLs, and use Git elsewhere."""
    configured = git(root, "remote", "get-url", remote)
    url = configured.stdout.strip() if configured is not None and configured.returncode == 0 else remote
    scp = re.fullmatch(r"(?:[^/@:]+@)?(?:github\.com|ssh\.github\.com|www\.github\.com)\.?:(.+)", url, re.I)
    try:
        parsed = urlsplit(url)
    except ValueError:
        return None, "invalid remote URL"
    host = (parsed.hostname or "").lower().rstrip(".")
    github = scp is not None or host in ("github.com", "ssh.github.com", "www.github.com")
    if github:
        if scp is None:
            ports = {"https": (None, 443), "http": (None, 80),
                     "ssh": (None, 22), "git": (None, 9418)}
            if host == "ssh.github.com":
                ports = {"ssh": (None, 443)}
            try:
                port = parsed.port
            except ValueError:
                return None, "invalid GitHub repository port"
            if (parsed.scheme not in ports or port not in ports[parsed.scheme]
                    or parsed.query or parsed.fragment):
                return None, "unsupported GitHub repository URL"
        path = scp.group(1) if scp is not None else parsed.path.lstrip("/")
        path = path.rstrip("/")
        if path.endswith(".git"):
            path = path[:-4]
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+", path):
            return None, "unsupported GitHub repository URL"
        try:
            listed = subprocess.run(
                ["agh", "branches", path], cwd=root, capture_output=True,
                text=True, check=False, timeout=REMOTE_TIMEOUT_SECONDS,
            )
        except (OSError, subprocess.TimeoutExpired):
            return None, "AGH unavailable or branch request timed out"
        if listed.returncode != 0:
            return None, listed.stderr.strip() or f"AGH rc {listed.returncode}"
        try:
            branches = json.loads(listed.stdout)
            if not isinstance(branches, list):
                raise ValueError("expected a complete branch array")
            tips = {}
            for branch in branches:
                name, sha = branch["name"], branch["sha"]
                if (not isinstance(name, str) or not name or name in tips
                        or any(ord(char) <= 32 or ord(char) == 127 for char in name)
                        or not isinstance(sha, str) or not re.fullmatch(r"[0-9a-f]{40}", sha)):
                    raise ValueError("invalid or duplicate branch")
                tips[name] = sha
            return tips, ""
        except (ValueError, TypeError, KeyError):
            return None, "AGH returned an invalid branch response"
    listed = git(root, "ls-remote", "--heads", remote, timeout=REMOTE_TIMEOUT_SECONDS)
    if listed is None or listed.returncode != 0:
        detail = (f"no git, or no answer in {REMOTE_TIMEOUT_SECONDS} s" if listed is None
                  else listed.stderr.strip() or f"rc {listed.returncode}")
        return None, detail
    return {
        ref[len("refs/heads/"):]: tip
        for tip, ref in (line.split("\t", 1) for line in listed.stdout.splitlines() if "\t" in line)
    }, ""


def audit_owners(
    tables: Dict[str, List[Row]], root: Path, remote: str, anchor: Optional[str] = None
) -> Tuple[int, List[str]]:
    """(exit code, report) for `owners`: where the owner of each OPEN claim
    can be found.  A pin resolves as `check` resolves it.  A bare lane label is
    looked up as a branch on `remote`: ASKED, not remembered, because a
    remote-tracking ref outlives its branch until a pruning fetch.  A lane the
    remote no longer has was DELETED when this clone has evidence it was there:
    its remote-tracking ref, an earlier audit that saw it (kept in the clone's
    git directory, so a pruning fetch does not erase it), or a merge of it from
    the remote in HEAD's history.

    A bare lane that is no branch on the remote, was never seen there and is no
    local branch either is UNPINNED ON MAIN when one of its claims is already on
    the remote's MAIN_BRANCH (the commit that introduced the claim's row is in
    the history of the tip the remote reported, or else of this clone's
    remote-tracking ref of it): a lane that commits straight to main, one that
    never pushed its branch, and a roadmap label all leave such a claim, and
    only the clone that wrote the label can resolve it.  `pin` is the fix
    there too.  A claim not on the remote's main yet (an unpushed lane, an
    uncommitted reservation), or on a tip this clone has not fetched, is `not
    seen here`: listed, not failed.

    Exit 1 on a definite defect (a deleted lane, a pin that does not resolve,
    an unpinned claim on main), 2 when nothing can be judged (no development
    history, or the remote cannot be asked), else 0."""

    if not has_development_history(root, anchor):
        named = DEVELOPMENT_ANCHOR if anchor is None else anchor
        return 2, [f"this checkout does not carry the development history ({named[:8]} is absent); nothing was judged"]
    remote_tips, detail = remote_branches(root, remote)
    if remote_tips is None:
        return 2, [f"cannot list the branches of `{remote}` ({detail}); nothing was judged"]
    remote_heads = set(remote_tips)
    seen = seen_lanes(root, remote, sorted(remote_heads))
    merges = git(root, "log", "--merges", "--format=%s", "HEAD")
    merge_subjects = merges.stdout if merges is not None and merges.returncode == 0 else ""
    problems, _ = unresolved_pins(tables, root, anchor)
    claims: Dict[str, List[Tuple[str, Row]]] = {}
    names: Dict[int, str] = {}
    for table in COUNTED:
        for row in tables[table]:
            owner = row.fields.get("owner")
            if row.fields.get("status") == "reserved" and isinstance(owner, str):
                claims.setdefault(owner, []).append((table, row))
                names[row.line] = claim_name(table, row)

    def has_ref(ref: str) -> bool:
        found = git(root, "show-ref", "--verify", "--quiet", ref)
        return found is not None and found.returncode == 0

    def merged_from_remote(lane: str) -> bool:
        return any(
            re.search(pattern.format(remote=re.escape(remote), lane=re.escape(lane)), merge_subjects, re.M)
            for pattern in MERGED_FROM_REMOTE
        )

    main_tips: List[Optional[str]] = []

    def remote_main() -> Optional[str]:
        """The remote's MAIN_BRANCH as this clone has it: the tip the remote
        reported if that commit is here, else the remote-tracking ref."""
        if not main_tips:
            found = None
            for name in (remote_tips.get(MAIN_BRANCH), f"refs/remotes/{remote}/{MAIN_BRANCH}"):
                if name:
                    parsed = git(root, "rev-parse", "--verify", "--quiet", f"{name}^{{commit}}")
                    if parsed is not None and parsed.returncode == 0:
                        found = parsed.stdout.strip()
                        break
            main_tips.append(found)
        return main_tips[0]

    def on_remote_main(table: str, row: Row) -> bool:
        tip = remote_main()
        landed = landing_commit(root, table, row) if tip is not None else None
        if landed is None:
            return False
        ancestor = git(root, "merge-base", "--is-ancestor", landed, tip)
        return ancestor is not None and ancestor.returncode == 0

    report, deleted, untraced, unseen = [], [], [], 0
    for owner, rows in sorted(claims.items()):
        match = OWNER.match(owner)
        lane, pin = (match.group(1), match.group(2)) if match else (owner, None)
        if pin is not None:
            where = "PIN UNRESOLVED" if any(row.line in problems for _, row in rows) else "pinned"
        elif lane in remote_heads:
            where = f"branch on {remote}"
        elif has_ref(f"refs/remotes/{remote}/{lane}") or lane in seen or merged_from_remote(lane):
            where = f"DELETED from {remote}"
            deleted.append(lane)
        elif has_ref(f"refs/heads/{lane}"):
            where = "local branch only"
        elif any(on_remote_main(table, row) for table, row in rows):
            where = "UNPINNED ON MAIN"
            untraced.append(lane)
        else:
            where = "not seen here"
        unseen += where == "not seen here"
        report.append(f"{where:>20}  {owner}: {', '.join(names[row.line] for _, row in rows)}")
    unresolved = sum(line.lstrip().startswith("PIN UNRESOLVED") for line in report)
    if deleted:
        report.append(
            f"{len(deleted)} lane(s) holding open claims were deleted from {remote}, so those claims name nothing "
            "anyone can trace. Pin each to the commit that landed its claims on main, in both wire-version "
            "ledgers: " + "; ".join(f"`python3 scripts/wire_alloc.py pin {lane}`" for lane in deleted)
            + ". Or release the claims as the registry header says."
        )
    if untraced:
        report.append(
            f"{len(untraced)} lane(s) hold open claims that are on {remote}'s {MAIN_BRANCH} under a label that is no "
            f"branch on {remote} or here and is not pinned (a lane that commits straight to main, one that never "
            "pushed its branch, or a roadmap label), so only the clone that wrote the label can trace them. Pin "
            "each to the commit that put its claims on main, in both wire-version ledgers: "
            + "; ".join(f"`python3 scripts/wire_alloc.py pin {lane}`" for lane in untraced)
            + ". Or release a claim instead (docs/wire-allocation.md), and record either choice, with its "
            "reasoning, in docs/wire-allocation-decisions.md."
        )
    if unresolved:
        report.append(f"{unresolved} pinned owner(s) do not resolve: `wire_alloc.py check` says why.")
    if unseen:
        report.append(
            f"{unseen} owner(s) were never seen on {remote} or here, and none of their claims is on {remote}'s "
            f"{MAIN_BRANCH} as this clone has it (a lane that has not pushed yet, or an uncommitted reservation). "
            "Not judged."
        )
    return (1 if deleted or untraced or unresolved else 0), report


def next_free(tables: Dict[str, List[Row]], namespace: str, name: Optional[str]) -> int:
    if namespace == "version":
        return max(row.get("number", int) for row in tables["wire_version"]) + 1
    if namespace == "tag":
        tags = [row.get("tag", int) for row in tables["enum_tag"] if row.fields.get("enum") == name]
        if not tags:
            raise RegistryError(
                f"enum `{name}` has no rows: a NEW tag space also needs a census probe in "
                "crates/trust-ir/src/binary/wire_census.rs (TAG_SPACES)"
            )
        return max(tags) + 1
    versions = [
        row.get("version", int) for row in tables["digest_domain"] if row.fields.get("domain") == name
    ]
    return max(versions, default=0) + 1


def render(fields: Sequence[Tuple[str, Value]]) -> str:
    parts = []
    for key, value in fields:
        if isinstance(value, str):
            if '"' in value or "\\" in value:
                raise RegistryError(f"`{key}` may not contain a quote or a backslash")
            parts.append(f'{key} = "{value}"')
        else:
            parts.append(f"{key} = {value}")
    return "  { " + ", ".join(parts) + " },"


def insert_row(text: str, table: str, row: str, after_line: Optional[int]) -> str:
    """Insert `row` after 1-based `after_line`, or as the last row of `table`."""

    lines = text.splitlines()
    if after_line is None:
        start = lines.index(f"{table} = [")
        after_line = next(i for i in range(start, len(lines)) if lines[i] == "]")
    lines.insert(after_line, row)
    return "\n".join(lines) + "\n"


def reserve(text: str, args: argparse.Namespace) -> Tuple[str, str]:
    tables = parse(text)
    owner = args.owner
    if args.namespace == "version":
        number = next_free(tables, "version", None)
        fields: List[Tuple[str, Value]] = [("number", number), ("feature", args.feature)]
        if args.constant:
            fields.append(("constant", args.constant))
        fields += [("status", "reserved"), ("owner", owner), ("date", args.date)]
        row = render(fields)
        return insert_row(text, "wire_version", row, None), row
    if args.namespace == "tag":
        tag = next_free(tables, "tag", args.enum)
        row = render(
            [
                ("enum", args.enum),
                ("tag", tag),
                ("variant", args.variant),
                ("since", args.since),
                ("status", "reserved"),
                ("owner", owner),
            ]
        )
        last = max(r.line for r in tables["enum_tag"] if r.fields.get("enum") == args.enum)
        return insert_row(text, "enum_tag", row, last), row
    version = next_free(tables, "domain", args.domain)
    existing = [r for r in tables["digest_domain"] if r.fields.get("domain") == args.domain]
    if not existing and not CANONICAL_DOMAIN.match(args.domain):
        raise RegistryError(
            f"`{args.domain}` is not a `trust_ir.*` domain: a NEW identity is spelled "
            "`trust_ir.<dotted.name>.vN` (only a bump of an existing legacy-spelled name keeps its spelling)"
        )
    fields = [("domain", args.domain), ("version", version)]
    if existing and "sep" in existing[0].fields:
        fields.append(("sep", existing[0].fields["sep"]))
    row = render(fields + [("status", "reserved"), ("binds", args.binds), ("owner", owner)])
    smaller = [
        r.line
        for r in tables["digest_domain"]
        if (r.fields.get("domain"), r.fields.get("version")) < (args.domain, version)
    ]
    if smaller:
        return insert_row(text, "digest_domain", row, max(smaller)), row
    first = text.splitlines().index("digest_domain = [") + 1
    return insert_row(text, "digest_domain", row, first), row


def takeover(text: str, feature: str) -> Tuple[str, List[str], Dict[int, int]]:
    """Move the reserved wire version of `feature` to the LOWEST open number.

    Read gates are cumulative (`version >= N`), so a blob numbered N + 1 claims
    everything N carries: wire versions can only LAND in number order.  A line
    that is ready while an earlier reservation is still open therefore takes
    the lowest open number, and every reservation it passes moves up by one —
    their relative order is kept.  Reserved `enum_tag` rows follow through
    `since`.  The displaced lines find out mechanically: the first time they
    merge main, the census reports their constant against a row that now
    carries another number."""

    tables = parse(text)
    lines = text.splitlines()
    open_rows = [r for r in tables["wire_version"] if r.fields.get("status") == "reserved"]
    mine = [r for r in open_rows if r.fields.get("feature") == feature]
    if len(mine) != 1:
        raise RegistryError(f"expected exactly one `reserved` wire_version row for feature `{feature}`, found {len(mine)}")
    ahead = [r for r in open_rows if r.get("number", int) < mine[0].get("number", int)]
    if not ahead:
        raise RegistryError(f"`{feature}` already holds the lowest open number ({mine[0].fields['number']}): nothing to take over")
    block = ahead + mine
    numbers = [r.get("number", int) for r in block]
    if numbers != list(range(numbers[0], numbers[0] + len(numbers))):
        raise RegistryError(f"open reservations {numbers} are not contiguous; repair the registry first")
    moved = {mine[0].get("number", int): numbers[0]}
    moved.update({r.get("number", int): r.get("number", int) + 1 for r in ahead})
    reordered = mine + ahead
    for slot, row in zip(block, reordered):
        fields = [("number", moved[row.get("number", int)])] + [(k, v) for k, v in row.fields.items() if k != "number"]
        lines[slot.line - 1] = render(fields)
    for row in tables["enum_tag"]:
        if row.fields.get("status") == "reserved" and row.fields.get("since") in moved:
            fields = [(k, moved[v] if k == "since" else v) for k, v in row.fields.items()]
            lines[row.line - 1] = render(fields)
    displaced = [
        f"wire v{r.fields['number']} -> v{moved[r.get('number', int)]}: `{r.fields.get('feature')}` (owner `{r.fields.get('owner')}`)"
        for r in ahead
    ]
    return "\n".join(lines) + "\n", displaced, moved


NEXT_STEPS = """\
Commit this row with the code that uses it, with its status set to "landed"
({registry}; "shipped" in crates/trust-ir/wire_versions.tsv). If main takes
the same number first, the merge conflicts on adjacent rows: renumber
(`wire_alloc.py next`)."""


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("check", help="the toolchain-free half of the registry gate")
    nxt = commands.add_parser("next", help="print the next free number")
    nxt.add_argument("namespace", choices=("version", "tag", "domain"))
    nxt.add_argument("name", nargs="?", help="the enum (tag) or the domain (domain)")
    res = commands.add_parser("reserve", help="write a reserved row for the next free number")
    kinds = res.add_subparsers(dest="namespace", required=True)
    ver = kinds.add_parser("version")
    ver.add_argument("--feature", required=True)
    ver.add_argument("--constant", help="the *_FORMAT_VERSION constant the feature will add")
    tag = kinds.add_parser("tag")
    tag.add_argument("--enum", required=True)
    tag.add_argument("--variant", required=True)
    tag.add_argument("--since", required=True, type=int, help="the wire version that will carry it")
    dom = kinds.add_parser("domain")
    dom.add_argument("--domain", required=True, help="without the .vN suffix")
    dom.add_argument("--binds", required=True, help="what the digest/schema tag binds")
    for sub in (ver, tag, dom):
        sub.add_argument("--owner", required=True, help="the branch or lane that owns the number")
        sub.add_argument("--date", default=datetime.date.today().isoformat())
    take = commands.add_parser(
        "takeover",
        help="move your reserved wire version to the LOWEST open number (versions land in number order)",
    )
    take.add_argument("--feature", required=True, help="the `feature` of YOUR reserved wire_version row")
    commands.add_parser("required-census-tests", help="print the census tests gate 10 requires to have run")
    commands.add_parser(
        "sync",
        help=f"copy an open wire-version reservation that only one of {REGISTRY} / {VERSION_LEDGER} has into the other",
    )
    own = commands.add_parser(
        "owners",
        help="asks the remote where the owner of every open claim is: exit 1 on a lane deleted from it, 2 when nothing can be judged",
    )
    own.add_argument("--remote", default="origin", help="the remote whose branches a lane label is looked up in")
    pin_cmd = commands.add_parser(
        "pin",
        help="pin every open claim of a bare lane to the commit that landed it, in both wire-version ledgers",
    )
    pin_cmd.add_argument("lane", help="the bare lane label, as the claims' `owner` spells it")
    args = parser.parse_args(argv)

    if args.command == "required-census-tests":
        print("\n".join(REQUIRED_CENSUS_TESTS))
        return 0
    root: Path = args.root
    path = root / REGISTRY
    ledger_path = root / VERSION_LEDGER
    displaced: List[str] = []
    synced: List[str] = []
    try:
        text = path.read_text(encoding="utf-8")
        if not ledger_path.is_file():
            raise RegistryError(
                f"{VERSION_LEDGER} is missing. It is the OTHER wire-version ledger and this registry is "
                "bound to it; if it was retired, retire the binding (VERSION_LEDGER here, "
                "check_the_version_ledgers_agree in wire_census.rs) with it."
            )
        tsv = ledger_path.read_text(encoding="utf-8")
        tables = parse(text)
        if args.command == "next":
            if args.namespace != "version" and not args.name:
                parser.error(f"`next {args.namespace}` needs a name")
            print(next_free(tables, args.namespace, args.name))
            return 0
        if args.command == "reserve":
            text, row = reserve(text, args)
            tables = parse(text)
            if args.namespace == "version":
                # One counter, two ledgers: a reservation goes into BOTH.
                made = tables["wire_version"][-1].fields
                tsv = ledger_with(tsv, ledger_row(int(made["number"]), args.feature, args.constant, args.owner))
        if args.command == "takeover":
            text, displaced, moved = takeover(text, args.feature)
            tsv = ledger_renumbered(tsv, moved)
            tables = parse(text)
        if args.command == "sync":
            text, tsv, synced = sync(text, tsv, datetime.date.today().isoformat())
            tables = parse(text)
        if args.command == "pin":
            text, tsv, synced = pin_lane(text, tsv, root, args.lane)
            tables = parse(text)
        binary_src = (root / "crates/trust-ir/src/binary.rs").read_text(encoding="utf-8")
        errors = check(tables, binary_src, scan_literals(root), tsv)
        # Only a well-formed owner reaches the resolver; a malformed one is
        # already an error above and would resolve as nothing at all.
        problems, pinned = unresolved_pins(tables, root)
        errors.extend(problems[line] for line in sorted(problems))
    except RegistryError as error:
        print(f"FAIL: {path.name}: {error}", file=sys.stderr)
        return 1
    if errors:
        print(f"FAIL: {path.name} disagrees with the code:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1
    if args.command == "owners":
        status, report = audit_owners(tables, root, args.remote)
        print("\n".join(report), file=sys.stderr if status else sys.stdout)
        return status
    if args.command == "pin":
        path.write_text(text, encoding="utf-8")
        ledger_path.write_text(tsv, encoding="utf-8")
        print(f"PINNED in {path.name} and {VERSION_LEDGER}:\n  " + "\n  ".join(synced))
        return 0
    if args.command == "sync":
        path.write_text(text, encoding="utf-8")
        ledger_path.write_text(tsv, encoding="utf-8")
        print("SYNCED: " + ("; ".join(synced) if synced else "nothing to copy — the two ledgers already agree"))
        return 0
    if args.command == "reserve":
        path.write_text(text, encoding="utf-8")
        ledger_path.write_text(tsv, encoding="utf-8")
        also = f" and {VERSION_LEDGER}" if args.namespace == "version" else ""
        print(f"RESERVED in {path.name}{also}:\n{row}\n")
        print(NEXT_STEPS.format(registry=REGISTRY))
        return 0
    if args.command == "takeover":
        path.write_text(text, encoding="utf-8")
        ledger_path.write_text(tsv, encoding="utf-8")
        print(f"TAKEN OVER in {path.name} and {VERSION_LEDGER}: `{args.feature}` now holds the lowest open wire version. Displaced:")
        for line in displaced:
            print(f"  {line}")
        print(
            "Renumber YOUR constant to match and commit this registry change with your code.\n"
            "Each displaced line learns of it from the census the first time it merges main."
        )
        return 0
    counts = ", ".join(f"{len(tables[name])} {name}" for name in COUNTED)
    spaces = len({row.fields.get("enum") for row in tables["enum_tag"]})
    print(
        f"PASS: {path.name} — {counts} ({spaces} tag spaces, {len(tables['scan_exempt'])} scan exemptions); "
        "version constants, versioned identity strings and the tag spaces binary.rs spells agree with the "
        f"sources; the compiled census is hooked in; {VERSION_LEDGER} agrees number by number; {pinned}. "
        "This is a SOURCE SCAN, not a proof "
        "(tag bytes and reader status: `test -p trust-ir --lib wire_census`)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
