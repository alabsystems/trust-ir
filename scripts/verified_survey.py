#!/usr/bin/env python3
"""The verified SURVEY (gate 15 of scripts/ci_gates.sh, `verified-survey`).

OPT-IN: ci_gates.sh runs it only when TRUST_IR_VERIFIED_SURVEY=1 and otherwise
prints SKIP (and still runs `--check-ledger`). A full survey took 35 to 144
minutes in this change's four measured runs (2026-09-29/30, 14 cores, load
17-78 from other sessions; r7 measured 83), plus a 4-6 GiB build tree the
survey clears at its start and 0.35-1.2 GB of reports, so it cannot run on
every ci_gates.sh call.

WHAT IT RUNS, per workspace member (`targo metadata`'s `workspace_members`,
never a hand list), one after another:

    targo trust check --allow-l0-gaps -p <crate> [--features <resolved>] \\
        --report-dir <out>/<crate>

in the DEBUG profile — gate 13 (scripts/verified_contracts.py) stays the
`--release` contract lane — with CARGO_TARGET_DIR=<root>/target/verified-survey
and nothing in RUSTFLAGS (the root `[trust]` table is the budget). `<resolved>`
is the feature set the workspace's own build resolves for the crate (the
`targo metadata` resolve graph): the code the workspace compiles. targo's exit
status is IGNORED: the advisory lane exits 1 on any refutation and 0 on
thousands of unknowns, so it says nothing a gate can use. Every verdict is read
PER ROW from `report.ndjson`, streamed (crate trust-ir's report is ~1.2 GB) and
checked against its own footer (record count and digest), so a truncated
report is never read as a small one.

JUDGED (per crate) is gate 13's rule, from gate 13's code (verified_contracts,
THE RULE — one reader, not two): a crate is judged only if
  (a) its report's resource accounting passes `memory_not_judged`: a current
      schema-4 budget profile matches the primary units' compiler controls,
      typed vector and stop accounting, with no resource/unexplained stop;
      an older seal's report instead needs its explicit memory ceiling and
      every RSS reading below it. The older seal's RSS trip was invisible to
      its checkpoint and made strict/certify PROVE counter-program p4, and
  (b) NO row of its primary unit is budget- or resource-attributable
      (`row_budget_attribution`, whose field list is the report schema's own:
      a `timeout` row; the seal's synthetic whole-function stop rows —
      `TrustPreprocessingBudget`, `MemoryAdmission` (a trustd that refused its
      socket left every function of a crate behind one, measured in this
      survey), `TrustDumpOnly`; the memory-ceiling gap row; a reason naming a
      word of the ResourceLimit arm of Trust's own classifier, which covers the
      type-lowering budget, the deadline at solver dispatch and the
      native-bundle budget; a native verifier `TimedOut`; and a kernel
      certification the seal skipped or declined — `certify_all` stops at the
      function deadline and records no cause, so a proof without its
      Clean-kernel re-check is one) and NO line of the run reports a budget
      stop (`budget_stop_not_judged`).
Added here because the survey reads a whole crate: the report stream must be
whole, every omitted-request list must parse, and a request publication kept
out of the rows is admitted only as a favorable claim "withheld at
publication" — any other omission (it carries no stop cause; one measured
omission hid a refutation behind a solver timeout) makes the crate NOT JUDGED.
Gate 13's rule (c) — every row proved or an expected refutation — is gate 13's
alone: a survey is ABOUT unknown rows.

Anything else is NOT JUDGED in BOTH directions: its refutations are listed and
never gated, its proved rows are not evidence. No count is gated — not proved
totals, not inventory size, not `coverage_complete`, not the refuted set as an
equality — because each moves with load and with the seal's budget trips (the
r8 budget challenge: at `function_budget_ms = 1` five refutations became
zero with coverage still "complete").

A REFUTATION is ONE thing in both verified gates (`refutation_route`): a row
whose status is `failed` (the L0 route), or a row whose verdict text names the
native runner's `refuted obligation` — gate 13's own refutation evidence
(`verified_contracts.REFUTED_LINE`). The installed seal publishes every native
CHC/PDR refutation as `unknown` ("refutation demoted to unknown: the submitted
ChcVc has no positive producer fidelity attestation") because its encoding may
over-approximate: UNPROVED, not disproved, so it is a refutation to classify
exactly like a `failed` one — measured 2026-09-30, a reachable `Option::unwrap`
and a reachable `unreachable!()` in a JUDGED crate were published ONLY this
way, and an earlier version of this gate, which read `failed` alone, passed
both. NOT a refutation: "refutation demoted to unknown (constructs: …)" — the
CHC lowering turned an unsupported construct into an unconditional error
rule, so the solver's path to it says nothing about the obligation (it never
names `refuted obligation`); it is reported with the unknown rows.

WHAT IT GATES, for a JUDGED crate only:
  * every refutation is in the committed ledger
    scripts/gates/verified-survey-refutations.tsv, keyed by its SITE — crate,
    file, enclosing function and the source text its span covers — and its
    obligation KIND (`Site`). Not the line: an unrelated edit above a refuted
    line must not un-ledger it. Not the obligation id: ids are not stable
    across identical runs (r7: one function emitted `custom:0` in one run and
    `assertion:panic-freedom:0` in the next). The ledger is a MULTISET: a
    row counts the refuted rows its identity carries, because several checks
    share one span and kind (measured: the null, validity, alignment and
    bounds checks of one deref). More refuted rows at an identity than the
    ledger counts — or any at an identity it lacks — FAIL, printed as a ledger
    line to classify; a refuted row with no complete location cannot be
    keyed, so it FAILS too. ONE class is admitted without a ledger line, and
    only on another gate's verdict: a DEMOTED `postcondition` refutation of a
    law of gate 13's laws file (`gate13_law`). Gate 13 PROVES every such law
    at --release, where the inliner puts the table's body into the wrapper;
    in this DEBUG survey nothing is inlined and the seal refutes the
    wrapper's encoding (measured: 312 of 313 laws, in each of R1, R2, R3).
    Those rows are counted and printed as gate 13's, never as this survey's
    evidence, and are not re-measured here: the admission rests on gate 13
    passing on the same tree (ci_gates.sh runs both; a `failed` row, another
    kind, file or function is never admitted);
  * a ledger row is `verifier-false` (a false refutation of the installed Trust,
    naming its shape — SHAPES — and the repro that shows it) or `policy` (a
    hardened-profile row trust-ir keeps by a recorded decision: its cause
    must begin with a decision of the CLOSED table POLICY_DECISIONS, and its
    kind must be one that decision covers). A `true` class is FORBIDDEN: a
    true refutation is a defect to fix at its root. The ledger is parsed
    before anything runs, and a bad ledger fails the gate;
  * a ledger row whose refutation is ABSENT from a judged run (or present
    fewer times than it counts) is reported as "expected refutation missing —
    NOT JUDGED for that row": never a pass,
    never auto-deleted. Removing a row is an explicit commit citing the Trust
    fix that removed the false refutation (or the source change that removed
    the code: `--check-ledger` fails a row whose text no longer occurs in its
    file, toolchain-free, so gate 15's SKIP path and gate 0's script tests
    catch it without a survey).
Unknown, timeout and design-requirement rows are reported per crate, never
gated: a survey PASS says nothing about a check whose row came back unknown.

VERDICT: FAIL (exit 1) on a new or unkeyable refutation in a judged crate or a
ledger that does not parse; otherwise PASS (exit 0) with every NOT JUDGED crate
listed. Exit 2: the survey could not run (no targo, RUSTFLAGS set, metadata
failed). Expected today: most crates NOT JUDGED — the installed seal trips its
wall-clock per-function budget under this host's load, and its 3 GiB RSS
ceiling on the large crates — so this gate is the instrument that turns green
as Trust's deterministic budget lands, not a claim that any crate is verified.

Usage:
  verified_survey.py [--root DIR] [--out DIR] [--crates a,b] [--keep-json]
  verified_survey.py --rejudge [--out DIR] [--crates a,b]   # re-read kept runs
  verified_survey.py --check-ledger                          # the ledger alone
A survey writes <out>/summary.json; a re-judge writes <out>/summary.rejudge.json
and never touches the run's own record.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import time
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, FrozenSet, Iterable, Iterator, List, Optional, Sequence, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verified_contracts as vc  # noqa: E402  -- THE one report reader and THE RULE

NOT_JUDGED = vc.NOT_JUDGED
OPT_IN = "TRUST_IR_VERIFIED_SURVEY"
LEDGER = Path("scripts") / "gates" / "verified-survey-refutations.tsv"
TARGET = Path("target") / "verified-survey"
LEDGER_HEADER = ("crate", "file", "function", "kind", "text", "count", "class", "cause")
CLASSES = ("verifier-false", "policy")
FORBIDDEN_CLASSES = ("true",)
# The recorded decisions a `policy` row may cite — the id its cause begins
# with, then " POLICY rows: " — and the obligation kinds each one covers.
# CLOSED: a new decision is a reviewed edit of this table, never a ledger
# line. Without it a `policy` cause was free text, and a TRUE refutation
# ledgered as `policy` passed (measured in review: a planted `x + 1` overflow
# ledgered as `policy` passed --check-ledger and the re-judge). The id is a
# dev-history commit; the public snapshot rewrites history, so it is a
# citation, not something this script resolves. What the kind cannot check
# (that each capacity really is the length of a resident collection) is the
# cause's own reading of the code.
POLICY_DECISIONS: Dict[str, Tuple[str, ...]] = {
    # Stage 0 (2026-09-29): a hardened `unbounded_allocation` on a Vec sized
    # by the length of a collection already resident in memory is
    # O(input already paid for); rewriting it as `collect()` would hide the
    # same allocation from the lint.
    "d5db1e5d": ("unbounded_allocation",),
}
POLICY_CAUSE = re.compile(r"^(?P<decision>[0-9a-f]{8}) POLICY rows: \S")
# The installed seal's false-refutation shapes (r7 measurement, blocker B2).
# REPRO is a standalone crate with a function per shape:
#   targo trust check --allow-l0-gaps --manifest-path <REPRO>/Cargo.toml
# Shape (c)'s MIR `null reference constructed` check of a deref through a Box
# refutes in isolation (`Nest::width`, the reduction of trust-ir's
# `Ty::bit_width`); its `Box::new` allocation check PROVES in isolation
# (`boxed`) and refutes only in larger bodies, so those rows are their own
# evidence.
REPRO = Path("scripts") / "tests" / "fixtures" / "verified_survey" / "false_refutation_repro"
SHAPES = {
    "a": "the hardened_panic_boundary route drops the type-range facts its L0 twin keeps "
    "(counterexample slice_len = 2^64, usize = -1) and refutes an op the L0 route PROVES",
    "b": "a guard or invariant the code establishes is lost — to slice-length symbol proliferation "
    "(Trust open item 36984d56d6: a bound on one read of a slice's length does not reach the next), on "
    "the bound of a `0..n` range, or over data the function builds itself (every decimal digit < 10) "
    "— so an op the guard makes safe is refuted",
    "c": "a separation-logic `[unsafe:sep:*]` check (a Box::new allocation null check, a deref's "
    "null/validity/alignment), or the MIR `null reference constructed` check of a deref through a Box, "
    "charged to SAFE source: the crate's `src/` has no `unsafe` block, fn or impl",
    "d": "a widening `From` of a narrower integer (`i128::from(u64)`, `u64::from(u32)`) treated as "
    "unconstrained in the wider type",
    "e": "a fact a call establishes is lost at the call boundary — the range a successful "
    "`u32::try_from(x).expect(..)` puts on `x`, the length `Vec::push` leaves — so arithmetic it "
    "makes safe is refuted",
}
# What the ledger check can hold toolchain-free about a shape's rows (the rest
# of each claim is the cause's own reading of the code, and the repro):
#   c — the row's crate has no `unsafe` block, fn or impl in its `src/`;
#   d — the refuted text is arithmetic (`+`, `-`, `*`) applied directly to a
#       widening `<int>::from(..)` (WIDENING_ARITH): a shift of the widened
#       value, like conformance's varint reader `u64::from(b) << (7 * width)`,
#       is NOT this shape (its shift amount really can overflow).
WIDENING_ARITH = re.compile(r"\b[iu](?:8|16|32|64|128|size)::from\((?:[^()]|\([^()]*\))*\)\s*[-+*]\s")
UNSAFE_SITE = re.compile(r"\bunsafe\s*(\{|fn\b|impl\b|extern\b|trait\b)")
SPAN = re.compile(r"^(\d+):(\d+)-(\d+):(\d+)$")
# The identity's text: the source a refuted row's span covers, whitespace
# collapsed, at most TEXT_MAX characters with `…` marking a cut.
TEXT_MAX = 100
VERIFIER_FALSE_CAUSE = re.compile(r"^shape (?P<shape>[a-z])\b")
NDJSON_SCHEMA = "trust.report.ndjson.v2"
# seal crates/trust-report/src/json_output.rs `write_ndjson`: the footer's
# `function_records_sha256` is SHA-256 over this domain, the record count
# (u64 big-endian), then each record's length (u64 big-endian) and bytes.
NDJSON_RECORDS_DOMAIN = b"trust.report.ndjson.function-records.v2"
REPORT = "report.ndjson"
REFUTED = "failed"
DEMOTED = "demoted"
EXAMPLES = 3


# ---------------------------------------------------------------------------
# identity and the ledger
# ---------------------------------------------------------------------------


@dataclass(frozen=True, order=True)
class Site:
    """The identity of a refuted row: crate, file, enclosing function, the
    obligation kind, and the source text the row's span covers. NOT the line
    and column (an unrelated edit above a refuted line would un-ledger it —
    stage 0 keyed its row deltas the same way for the same reason), and NOT
    the obligation id (unstable across identical runs, measured)."""

    crate: str
    file: str
    function: str
    kind: str
    text: str

    def ledger_prefix(self) -> str:
        return "\t".join((self.crate, self.file, self.function, self.kind, self.text))

    def __str__(self) -> str:
        return f"{self.crate} {self.file} `{self.function}` {self.kind} `{self.text}`"


def row_span(ob: dict) -> Optional[Tuple[str, str]]:
    """(file, "L:C-L:C") of row `ob`, or None when its location is incomplete."""
    loc = ob.get("location")
    if not isinstance(loc, dict):
        return None
    try:
        file = loc["file"]
        ends = [int(loc[k]) for k in ("line_start", "col_start", "line_end", "col_end")]
    except (KeyError, TypeError, ValueError):
        return None
    if not isinstance(file, str) or not file:
        return None
    return file, "{}:{}-{}:{}".format(*ends)


def site_of(crate: str, function: str, ob: dict, root: Optional[Path]) -> Optional[Site]:
    """The identity of row `ob` of `function` in `crate`, or None when the row
    carries no complete location or kind. The text is read from `root` — the
    tree the survey verified; a span outside it (an absolute path, a span
    that does not fit the file) is identified by `@L:C-L:C` instead."""
    where = row_span(ob)
    kind = ob.get("kind")
    if where is None or not isinstance(kind, str) or not kind or not function:
        return None
    file, span = where
    return Site(crate, file, function, kind, span_text(root, file, span) or f"@{span}")


def normalize(text: str) -> str:
    """Whitespace runs collapsed; cut at TEXT_MAX with `…`."""
    text = " ".join(text.split())
    return text if len(text) <= TEXT_MAX else text[: TEXT_MAX - 1] + "…"


def tree_file(root: Optional[Path], file: str) -> Optional[Path]:
    """`root/file` when the report's path names a file INSIDE the tree (it may
    climb, as `crates/trust-ir-conformance/src/../tests/generate.rs` does for a
    `#[path]` module), else None — std's `core/src/panic.rs`, an absolute
    path, or anything that leaves the root."""
    if root is None or Path(file).is_absolute():
        return None
    norm = os.path.normpath(file)
    if norm == ".." or norm.startswith(".." + os.sep) or os.path.isabs(norm):
        return None
    path = root / norm
    return path if path.is_file() else None


def span_text(root: Optional[Path], file: str, span: str) -> Optional[str]:
    """The normalized source text `span` covers in `root/file` (columns are
    0-based and end-exclusive, as the report writes them), or None when the
    file is not in the tree or the span does not fit it."""
    m = SPAN.match(span)
    path = tree_file(root, file)
    if m is None or path is None:
        return None
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    l0, c0, l1, c1 = (int(g) for g in m.groups())
    if not (1 <= l0 <= l1 <= len(lines)):
        return None
    if l0 == l1:
        if c1 < c0 or c1 > len(lines[l0 - 1]):
            return None
        raw = lines[l0 - 1][c0:c1]
    else:
        raw = "\n".join([lines[l0 - 1][c0:], *lines[l0:l1 - 1], lines[l1 - 1][:c1]])
    return normalize(raw) or None


@dataclass(frozen=True)
class LedgerRow:
    site: Site
    count: int  # refuted rows the identity carries (several checks can share one span and kind)
    klass: str
    cause: str
    line: int


def parse_ledger(text: str) -> Tuple[Dict[Site, LedgerRow], List[str]]:
    """(rows by identity, errors). Tab-separated, one header row, `#` comment
    lines. An error anywhere fails the gate: the ledger is the gate's input."""
    rows: Dict[Site, LedgerRow] = {}
    errors: List[str] = []
    header = False
    for n, raw in enumerate(text.splitlines(), 1):
        if not raw.strip() or raw.startswith("#"):
            continue
        cols = raw.split("\t")
        if not header:
            header = True
            if tuple(cols) != LEDGER_HEADER:
                errors.append(f"line {n}: the header must be {chr(9).join(LEDGER_HEADER)!r}, got {raw!r}")
            continue
        if len(cols) != len(LEDGER_HEADER):
            errors.append(f"line {n}: {len(cols)} tab-separated columns, need {len(LEDGER_HEADER)}: {raw!r}")
            continue
        if any(c != c.strip() or not c for c in cols):
            errors.append(f"line {n}: every column is non-empty with no surrounding blanks: {raw!r}")
            continue
        crate, file, function, kind, text, count, klass, cause = cols
        site = Site(crate, file, function, kind, text)
        if not count.isdigit() or int(count) < 1:
            errors.append(f"line {n}: count must be a positive integer, got {count!r}")
            continue
        if text != normalize(text):
            errors.append(f"line {n}: the text column must be normalized (whitespace collapsed, <= {TEXT_MAX} "
                          f"characters): {text!r}")
            continue
        if klass in FORBIDDEN_CLASSES:
            errors.append(
                f"line {n}: class `{klass}` is FORBIDDEN ({site}): a true refutation is a defect to fix "
                "at its root, never a ledger row"
            )
            continue
        if klass not in CLASSES:
            errors.append(f"line {n}: class must be one of {', '.join(CLASSES)}, got {klass!r}")
            continue
        if klass == "verifier-false":
            m = VERIFIER_FALSE_CAUSE.match(cause)
            if m is None or m["shape"] not in SHAPES:
                errors.append(
                    f"line {n}: a verifier-false row names its Trust shape first "
                    f"(`shape <{'|'.join(SHAPES)}> ...`), got {cause!r}"
                )
                continue
        if klass == "policy":
            m = POLICY_CAUSE.match(cause)
            decision = m["decision"] if m else None
            if decision not in POLICY_DECISIONS:
                errors.append(
                    f"line {n}: a policy row's cause begins with a recorded decision of POLICY_DECISIONS "
                    f"(`<{'|'.join(POLICY_DECISIONS)}> POLICY rows: ...`), got {cause!r}"
                )
                continue
            if kind not in POLICY_DECISIONS[decision]:
                errors.append(
                    f"line {n}: decision {decision} covers only {', '.join(POLICY_DECISIONS[decision])}, not a "
                    f"`{kind}` row ({site}): a refutation of any other kind is verifier-false (naming its shape) "
                    "or a defect to fix"
                )
                continue
        if site in rows:
            errors.append(f"line {n}: duplicate identity {site} (first at line {rows[site].line})")
            continue
        rows[site] = LedgerRow(site, int(count), klass, cause, n)
    if not header:
        errors.append(f"no header row {chr(9).join(LEDGER_HEADER)!r}")
    return rows, errors


def crate_dir(root: Path, file: str) -> Optional[Path]:
    """The directory of the nearest Cargo.toml above `file` in the tree."""
    path = tree_file(root, file)
    if path is None:
        return None
    here = path.parent
    while True:
        if (here / "Cargo.toml").is_file():
            return here
        if here == root or here.parent == here:
            return None
        here = here.parent


def unsafe_sites(directory: Path, also: Optional[Path] = None) -> List[str]:
    """`file:line` of every `unsafe` block/fn/impl/extern/trait in the code a
    `targo trust check` of the crate verifies: its `src/` tree, plus `also`
    (the refuted file, which a `#[path]` module can place outside `src/`).
    `tests/` is not compiled by `check`, so an `unsafe` there says nothing.
    Text after `//` is skipped."""
    found = []
    paths = set((directory / "src").rglob("*.rs")) | ({also} if also is not None else set())
    for path in sorted(paths):
        for n, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            code = line.split("//", 1)[0]
            if UNSAFE_SITE.search(code):
                found.append(f"{os.path.relpath(path, directory)}:{n}")
    return found


def ledger_text_errors(root: Path, rows: Dict[Site, LedgerRow]) -> List[str]:
    """Every row whose source text no longer occurs in its file: the refuted
    code is gone or rewritten, so the row names nothing (delete it in the
    change that removed the code, or re-key it). Toolchain-free, so gate 0's
    script tests and gate 15's SKIP path catch it without a survey. A row of
    a file outside the tree (`@L:C-L:C` text) cannot be checked and is named.
    Also the checkable part of each shape claim (see UNSAFE_SITE above)."""
    errors: List[str] = []
    cache: Dict[str, Optional[str]] = {}
    unsafe_cache: Dict[Tuple[Path, Optional[Path]], List[str]] = {}
    for site, row in sorted(rows.items()):
        shape = VERIFIER_FALSE_CAUSE.match(row.cause) if row.klass == "verifier-false" else None
        if shape and shape["shape"] == "d" and not WIDENING_ARITH.search(site.text):
            errors.append(
                f"line {row.line}: {site}: a shape-d row's text must be `+`, `-` or `*` on a widening `<int>::from(..)`"
            )
        if shape and shape["shape"] == "c":
            directory = crate_dir(root, site.file)
            if directory is None:
                errors.append(f"line {row.line}: {site}: no crate manifest above the file for a shape-c row")
            else:
                key = (directory, tree_file(root, site.file))
                if key not in unsafe_cache:
                    unsafe_cache[key] = unsafe_sites(*key)
                if unsafe_cache[key]:
                    errors.append(
                        f"line {row.line}: {site}: a shape-c row claims safe source, but the crate has `unsafe` at "
                        + ", ".join(unsafe_cache[key][:3])
                    )
        if site.text.startswith("@"):
            if SPAN.match(site.text[1:]) is None:
                errors.append(f"line {row.line}: {site}: an `@` text must be `@L:C-L:C`")
            continue
        if site.file not in cache:
            path = tree_file(root, site.file)
            cache[site.file] = " ".join(path.read_text(encoding="utf-8", errors="replace").split()) if path else None
        body = cache[site.file]
        if body is None:
            errors.append(f"line {row.line}: {site}: the file is not in the tree")
        elif site.text.rstrip("…") not in body:
            errors.append(f"line {row.line}: {site}: the text no longer occurs in the file")
    return errors


def load_ledger(root: Path) -> Tuple[Dict[Site, LedgerRow], List[str]]:
    path = root / LEDGER
    if not path.is_file():
        return {}, [f"{LEDGER}: missing"]
    rows, errors = parse_ledger(path.read_text(encoding="utf-8"))
    errors += ledger_text_errors(root, rows)
    return rows, [f"{LEDGER}: {e}" for e in errors]


# ---------------------------------------------------------------------------
# the report stream
# ---------------------------------------------------------------------------


def records_digest(records: Iterable[bytes], count: int) -> str:
    """The footer's `function_records_sha256` over `count` record lines."""
    h = hashlib.sha256(NDJSON_RECORDS_DOMAIN + struct.pack(">Q", count))
    for line in records:
        h.update(struct.pack(">Q", len(line)))
        h.update(line)
    return "sha256:" + h.hexdigest()


def iter_stream(lines: Iterable[bytes]) -> Iterator[Tuple[str, object]]:
    """Walk a report.ndjson one record at a time: yields ("header", dict),
    ("function", dict), and ("problem", str) for every reason the stream is
    not the whole report its own footer describes. The records digest is
    seeded with the header's `expected_functions` (the seal hashes the count
    FIRST), so a count that differs is refused by count and by digest."""
    header: Optional[dict] = None
    footer: Optional[dict] = None
    digest = None
    count = 0
    n = 0
    for n, raw in enumerate(lines, 1):
        line = raw.rstrip(b"\n")
        try:
            rec = json.loads(line)
        except (json.JSONDecodeError, UnicodeDecodeError) as e:
            yield "problem", f"line {n}: not a JSON record ({e})"
            continue
        kind = rec.get("record_type") if isinstance(rec, dict) else None
        if footer is not None:
            yield "problem", f"line {n}: a record after the footer"
        if kind == "header":
            if n != 1:
                yield "problem", f"line {n}: a header that is not the first record"
                continue
            header = rec
            if rec.get("schema") != NDJSON_SCHEMA:
                yield "problem", f"header schema {rec.get('schema')!r}, expected {NDJSON_SCHEMA!r}"
            expected = rec.get("expected_functions")
            if isinstance(expected, int) and expected >= 0:
                digest = hashlib.sha256(NDJSON_RECORDS_DOMAIN + struct.pack(">Q", expected))
            else:
                yield "problem", f"header expected_functions {expected!r} is not a count"
            yield "header", rec
        elif kind == "function":
            if header is None:
                yield "problem", f"line {n}: a function record before the header"
            count += 1
            if digest is not None:
                digest.update(struct.pack(">Q", len(line)))
                digest.update(line)
            yield "function", rec
        elif kind == "footer":
            footer = rec
        else:
            yield "problem", f"line {n}: unknown record_type {kind!r}"
    if n == 0 or header is None:
        yield "problem", "no header record"
    if footer is None:
        yield "problem", "no footer record: the report is truncated"
        return
    if footer.get("functions_emitted") != count:
        yield "problem", f"the footer counts {footer.get('functions_emitted')} function records, the stream holds {count}"
    if header is not None and header.get("expected_functions") != count:
        yield "problem", f"the header expects {header.get('expected_functions')} function records, the stream holds {count}"
    if digest is None or footer.get("function_records_sha256") != "sha256:" + digest.hexdigest():
        yield "problem", "the function records do not match the footer's function_records_sha256"


# ---------------------------------------------------------------------------
# judging one crate
# ---------------------------------------------------------------------------


def refutation_route(ob: dict) -> Optional[str]:
    """How row `ob` refutes its obligation, or None (the module docstring's
    A REFUTATION): REFUTED for a `failed` row, DEMOTED for a row whose
    verdict text names the native runner's `refuted obligation` — gate 13's
    evidence text, `vc.REFUTED_LINE`, whatever status the seal published."""
    outcome = ob.get("outcome") or {}
    if outcome.get("status") == REFUTED:
        return REFUTED
    if vc.REFUTED_LINE.search(str(outcome.get("reason") or "")):
        return DEMOTED
    return None


def gate13_law(crate: str, function: str, ob: dict, route: str, laws: FrozenSet[str]) -> Optional[str]:
    """The law of gate 13 whose debug-profile encoding row `ob` refutes, or
    None. ALL must hold: `crate` is gate 13's (vc.CRATE), the route is
    DEMOTED (a `failed` row is never admitted), the kind is `postcondition`,
    the location is gate 13's laws file (vc.LAWS_FILE), and `function` is
    `<crate>::laws::<law>` for a law gate 13 enumerates (`laws`, from
    vc.law_functions: every `pub fn` there, each of which gate 13 holds
    proved + Certified + KernelRechecked at --release). The module docstring
    says why such a row is gate 13's to decide and what the admission rests
    on."""
    if crate != vc.CRATE or route != DEMOTED or ob.get("kind") != "postcondition":
        return None
    where = row_span(ob)
    if where is None or os.path.normpath(where[0]) != vc.LAWS_FILE.as_posix():
        return None
    prefix = f"{vc.CRATE_IDENT}::laws::"
    law = function[len(prefix):] if function.startswith(prefix) else None
    return law if law in laws else None


def gate13_laws(crate: str, root: Optional[Path]) -> FrozenSet[str]:
    """Gate 13's laws when `crate` is gate 13's and the tree carries a laws
    file gate 13 can read; else none, so nothing is admitted (fail-closed:
    every such refutation then needs a ledger line)."""
    if crate != vc.CRATE or root is None:
        return frozenset()
    try:
        return frozenset(vc.law_functions(root))
    except (OSError, SystemExit):
        return frozenset()


@dataclass
class Refutation:
    site: Optional[Site]
    function: str
    obligation: str
    description: str
    where: str = ""  # file:L:C-L:C as this run measured it (display only)
    route: str = REFUTED  # REFUTED or DEMOTED (refutation_route)


@dataclass
class CrateResult:
    crate: str
    features: List[str] = field(default_factory=list)
    exit: Optional[int] = None
    rss_bound: Optional[int] = None
    wall_s: Optional[float] = None
    reasons: List[str] = field(default_factory=list)  # every one begins NOT_JUDGED
    statuses: Counter = field(default_factory=Counter)  # published primary rows by status
    budget: Counter = field(default_factory=Counter)  # budget-attributable rows by category
    budget_examples: List[str] = field(default_factory=list)
    refutations: List[Refutation] = field(default_factory=list)
    gate13_laws: List[str] = field(default_factory=list)  # demoted law postconditions admitted as gate 13's
    omitted: Counter = field(default_factory=Counter)  # omitted requests by outcome
    functions: int = 0
    memory: str = ""

    @property
    def judged(self) -> bool:
        return not self.reasons


def budget_category(attribution: str) -> str:
    """A short label for a `row_budget_attribution` finding (display only:
    the decision is whether there is one at all)."""
    m = re.match(r"its text names `([^`]+)`", attribution)
    if m:
        if "type lowering exceeded" in attribution:
            return f"type-lowering budget (names `{m.group(1)}`)"
        return f"reason names `{m.group(1)}`"
    return re.split(r": | \(", attribution, maxsplit=1)[0]


class CrateJudge:
    """Consumes one crate's run record by record and keeps summaries only."""

    def __init__(self, crate: str, root: Optional[Path] = None):
        self.result = CrateResult(crate)
        self.root = root
        self.laws = gate13_laws(crate, root)
        self.header: Optional[dict] = None
        self.problems: List[str] = []
        self.rows = 0

    def add_header(self, header: dict) -> None:
        self.header = header

    def add_problem(self, problem: str) -> None:
        self.problems.append(problem)

    def add_function(self, rec: dict) -> None:
        name = vc.primary_function(str(rec.get("function", "")), self.result.crate)
        if name is None:
            return
        self.result.functions += 1
        for ob in rec.get("obligations") or []:
            self.rows += 1
            outcome = ob.get("outcome") or {}
            status = str(outcome.get("status"))
            self.result.statuses[status] += 1
            stop = vc.row_budget_attribution(ob)
            if stop is not None:
                self.result.budget[budget_category(stop)] += 1
                if len(self.result.budget_examples) < EXAMPLES:
                    self.result.budget_examples.append(f"`{name}` {ob.get('obligation_id', '?')}: {stop[:200]}")
            route = refutation_route(ob)
            if route is None:
                continue
            law = gate13_law(self.result.crate, name, ob, route, self.laws)
            if law is not None:
                self.result.gate13_laws.append(law)
                continue
            where = row_span(ob)
            self.result.refutations.append(
                Refutation(
                    site_of(self.result.crate, name, ob, self.root),
                    name,
                    str(ob.get("obligation_id", "?")),
                    str(ob.get("description", ""))[:160],
                    ":".join(where) if where else "(no location)",
                    route,
                )
            )

    def finish(self, output: str, rss_bound: Optional[int]) -> CrateResult:
        r = self.result
        r.reasons += [f"{NOT_JUDGED} report stream: {p}" for p in self.problems]
        if self.header is None:
            r.reasons.append(f"{NOT_JUDGED} no report header: the run produced no readable report")
            return r
        r.memory = vc.memory_evidence(self.header, vc.LaneRun(r.exit or 0, output, rss_bound))
        r.reasons += vc.memory_not_judged(self.header, output, rss_bound)
        r.reasons += vc.budget_stop_not_judged(output)
        r.reasons += omitted_not_judged(output, r)
        if r.budget:
            parts = ", ".join(f"{n} {c}" for c, n in r.budget.most_common())
            r.reasons.append(
                f"{NOT_JUDGED} {sum(r.budget.values())} budget- or resource-attributable row(s): {parts}; e.g. "
                + " | ".join(r.budget_examples)
            )
        if self.rows == 0:
            r.reasons.append(f"{NOT_JUDGED} the report carries no row of the primary unit")
        r.reasons = collapse(r.reasons)
        return r


def collapse(reasons: Sequence[str]) -> List[str]:
    """Identical reasons once each, with their count, in first-seen order (a
    crate over the memory ceiling repeats one line per skipped body —
    measured: 10,659 for crate trust-ir)."""
    counts = Counter(reasons)
    out: List[str] = []
    for reason in reasons:
        n = counts.pop(reason, 0)
        if n:
            out.append(reason if n == 1 else f"{reason} (x{n})")
    return out


def omitted_not_judged(output: str, result: CrateResult) -> List[str]:
    """The omitted-request lists of the terminal (verified_contracts parses
    them): they must parse whole, the publication boundary must attribute
    every withheld row, and an omitted request of this crate's primary unit is
    admitted only as a favorable claim withheld at publication."""
    reasons: List[str] = []
    for line in output.splitlines():
        if vc.UNATTRIBUTED_WITHHELD.search(line):
            reasons.append(f"{NOT_JUDGED} the publication boundary cannot attribute every withheld row: {line.strip()[:240]}")
    for found in vc.omitted_lists(output):
        if found.count is None:
            reasons.append(f"{NOT_JUDGED} unparsed omitted-request list header: {found.header.strip()[:240]}")
        elif found.count != len(found.entries):
            reasons.append(
                f"{NOT_JUDGED} the omitted-request list prints {found.count} request(s) but carries "
                f"{len(found.entries)} entry line(s)"
            )
        for line in found.entries:
            entry = vc.OMITTED_ENTRY.match(line)
            if entry is None:
                reasons.append(f"{NOT_JUDGED} unparsed omitted-request entry: {line.strip()[:240]}")
                continue
            name = vc.primary_function(entry["function"], result.crate)
            if name is None:
                continue
            result.omitted[entry["outcome"] + (" (withheld)" if entry["withheld"] else "")] += 1
            if entry["withheld"]:
                continue
            reasons.append(
                f"{NOT_JUDGED} `{name}` {entry['obligation']} ({entry['kind']}) was omitted from the published "
                f"rows as {entry['outcome']}, not as a favorable claim withheld at publication: it carries no "
                "stop cause and no site, so it can be neither ruled out as a stop nor keyed as a refutation"
            )
    return reasons


def judge_crate(
    crate: str, lines: Iterable[bytes], output: str, rss_bound: Optional[int], root: Optional[Path] = None
) -> CrateResult:
    """One crate's verdict from its report stream and terminal output; `root`
    is the tree the run verified (it spells each refutation's source text)."""
    judge = CrateJudge(crate, root)
    for kind, value in iter_stream(lines):
        if kind == "header":
            judge.add_header(value)  # type: ignore[arg-type]
        elif kind == "function":
            judge.add_function(value)  # type: ignore[arg-type]
        else:
            judge.add_problem(str(value))
    return judge.finish(output, rss_bound)


# ---------------------------------------------------------------------------
# the gate
# ---------------------------------------------------------------------------


@dataclass
class Verdict:
    failures: List[str] = field(default_factory=list)
    missing: List[str] = field(default_factory=list)  # expected refutations absent (NOT JUDGED per row)
    not_judged: List[CrateResult] = field(default_factory=list)
    judged: List[CrateResult] = field(default_factory=list)

    @property
    def passed(self) -> bool:
        return not self.failures


def gate(
    results: Sequence[CrateResult],
    ledger: Dict[Site, LedgerRow],
    ledger_errors: Sequence[str],
) -> Verdict:
    """FAIL on a bad ledger or a new/unkeyable refutation of a JUDGED crate.
    The ledger is a MULTISET: an identity refuted more times than its row
    counts carries new refutations (FAIL); fewer, or none, is "expected
    refutation missing — NOT JUDGED for that row". A NOT JUDGED crate gates
    nothing, in either direction."""
    v = Verdict()
    v.failures += [f"ledger: {e}" for e in ledger_errors]
    for r in results:
        if not r.judged:
            v.not_judged.append(r)
            continue
        v.judged.append(r)
        seen: Dict[Site, List[Refutation]] = {}
        for f in r.refutations:
            if f.site is None:
                v.failures.append(
                    f"{r.crate}: refutation `{f.function}` {f.obligation} ({f.where}) carries no complete site, "
                    f"so no ledger row can admit it: {f.description}"
                )
            else:
                seen.setdefault(f.site, []).append(f)
        for site, found in sorted(seen.items()):
            row = ledger.get(site)
            allowed = row.count if row is not None else 0
            if len(found) > allowed:
                first = found[0]
                routes = ", ".join(f"{n} {k}" for k, n in sorted(Counter(f.route for f in found).items()))
                v.failures.append(
                    f"{r.crate}: NEW refutation {site}: {len(found)} refuted row(s) ({routes}), the ledger admits "
                    f"{allowed} ({first.obligation}: {first.description}; at "
                    f"{', '.join(sorted({f.where for f in found}))}); "
                    "fix it, or if Trust is wrong add or raise the ledger line "
                    f"`{site.ledger_prefix()}\t{len(found)}\t<class>\t<cause>`"
                )
        for site, row in sorted(ledger.items()):
            if site.crate != r.crate:
                continue
            short = row.count - len(seen.get(site, []))
            if short > 0:
                v.missing.append(
                    f"expected refutation missing — NOT JUDGED for that row: {site} ({short} of {row.count} "
                    f"refuted row(s) absent; {row.klass}, ledger line {row.line}); never a pass, never "
                    "auto-deleted (removing it is a commit citing the Trust fix)"
                )
    return v


# ---------------------------------------------------------------------------
# running
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Member:
    name: str
    features: Tuple[str, ...]
    no_default_features: bool

    def cargo_args(self) -> List[str]:
        args = ["-p", self.name]
        if self.no_default_features:
            args.append("--no-default-features")
        if self.features:
            args += ["--features", ",".join(self.features)]
        return args


def workspace_members(meta: dict) -> List[Member]:
    """Every workspace member with the features the workspace build resolves
    for it (`resolve.nodes[].features`), sorted by name."""
    packages = {p["id"]: p for p in meta.get("packages", [])}
    resolved = {n["id"]: n.get("features", []) for n in (meta.get("resolve") or {}).get("nodes", [])}
    out: List[Member] = []
    for pid in meta.get("workspace_members", []):
        pkg = packages.get(pid)
        if pkg is None or pid not in resolved:
            raise SystemExit(f"targo metadata: workspace member {pid} has no package or resolve node")
        feats = resolved[pid]
        has_default = "default" in (pkg.get("features") or {})
        out.append(
            Member(
                pkg["name"],
                tuple(sorted(f for f in feats if f != "default")),
                has_default and "default" not in feats,
            )
        )
    return sorted(out, key=lambda m: m.name)


def metadata(targo: str, root: Path) -> dict:
    proc = subprocess.run(
        [targo, "metadata", "--format-version", "1", "--offline"], cwd=root, capture_output=True, text=True, check=False
    )
    if proc.returncode != 0:
        proc = subprocess.run(
            [targo, "metadata", "--format-version", "1"], cwd=root, capture_output=True, text=True, check=False
        )
    if proc.returncode != 0:
        raise SystemExit(f"targo metadata failed (exit {proc.returncode}): {proc.stderr.strip()[:400]}")
    return json.loads(proc.stdout)


def lane_record(out: Path, crate: str) -> dict:
    path = out / f"{crate}.lane.json"
    return json.loads(path.read_text(encoding="utf-8")) if path.is_file() else {}


def judge_kept(out: Path, crate: str, root: Optional[Path] = None) -> CrateResult:
    """Re-judge a kept run exactly as the survey judged it (against the tree
    it verified: a refutation's identity reads its source text there)."""
    lane = lane_record(out, crate)
    log = out / f"{crate}.log"
    output = log.read_text(encoding="utf-8", errors="replace") if log.is_file() else ""
    declared = lane.get("report_dir")
    if "report_dir" in lane and (not isinstance(declared, str) or not Path(declared).is_absolute()):
        result = judge_crate(crate, [], output, lane.get("rss_bound_bytes"), root)
        result.reasons.insert(0, f"{NOT_JUDGED} invalid retained report directory")
        result.exit = lane.get("exit")
        return result
    report = (Path(declared) if declared is not None else out / crate) / REPORT
    if report.is_file():
        with report.open("rb") as handle:
            result = judge_crate(crate, handle, output, lane.get("rss_bound_bytes"), root)
    else:
        result = judge_crate(crate, [], output, lane.get("rss_bound_bytes"), root)
        result.reasons.insert(0, f"{NOT_JUDGED} no {REPORT} was written (exit {lane.get('exit')})")
    result.exit = lane.get("exit")
    result.rss_bound = lane.get("rss_bound_bytes")
    result.wall_s = lane.get("wall_s")
    result.features = list(lane.get("features") or [])
    return result


def run_member(targo: str, root: Path, out: Path, member: Member, keep_json: bool) -> CrateResult:
    report_dir = out / member.name
    extra = ["--allow-l0-gaps", *member.cargo_args()]
    started = time.monotonic()
    run = vc.run_lane(targo, root, report_dir, root / TARGET, extra, release=False)
    report_dir = vc.retained_report_dir(run, report_dir)
    wall = time.monotonic() - started
    vc.record_run(out / member.name, run)
    lane = {"exit": run.code, "rss_bound_bytes": run.rss_bound, "wall_s": round(wall, 1),
            "features": list(member.features), "args": extra}
    if run.report_dir is not None:
        lane["report_dir"] = run.report_dir
    (out / f"{member.name}.lane.json").write_text(json.dumps(lane) + "\n", encoding="utf-8")
    if not keep_json:  # report.ndjson carries the same records, streamable
        for name in ("report.json", "report.html"):
            (report_dir / name).unlink(missing_ok=True)
    return judge_kept(out, member.name, root)


def clear_build_tree(target: Path) -> Optional[int]:
    """Remove `target/debug`, the survey's build tree, and return its size (None
    if absent). Every `targo trust check` run rebuilds its dependency graph
    under fresh fingerprints — measured: 71 copies of libc after three surveys,
    the directory growing 6.2 -> 9.8 -> 13.4 GiB — so a kept build tree is
    never reused and only grows. Reports (`--out`) and targo's observational
    `trust-cache/verification.json` snapshot are left alone."""
    tree = target / "debug"
    if not tree.is_dir():
        return None
    size = disk_usage(tree)
    shutil.rmtree(tree)
    return size


def gib(n: Optional[int]) -> str:
    return "?" if n is None else f"{n / (1 << 30):.2f} GiB"


def print_crate(r: CrateResult, ledger: Dict[Site, LedgerRow]) -> None:
    feats = ",".join(r.features) or "-"
    wall = "?" if r.wall_s is None else f"{r.wall_s:.0f} s"
    print(f"\n== {r.crate}  [features: {feats}]  targo exit {r.exit} (ignored), {wall}")
    if r.memory:
        print(f"   {r.memory}")
    order = ("proved", "failed", "unknown", "timeout", "runtime_checked", "design_requirement")
    counts = ", ".join(f"{r.statuses.get(s, 0)} {s}" for s in order)
    extra = ", ".join(f"{n} {s}" for s, n in sorted(r.statuses.items()) if s not in order)
    total = sum(r.statuses.values())
    omitted = ", ".join(f"{n} {k}" for k, n in sorted(r.omitted.items())) or "none"
    print(f"   rows (reported, never gated): {counts}{', ' + extra if extra else ''} — {total} published "
          f"over {r.functions} functions; omitted requests: {omitted}")
    if r.judged:
        print("   JUDGED")
    else:
        print(f"   NOT JUDGED ({len(r.reasons)} reason(s)) — no row of this crate is evidence either way:")
        for reason in r.reasons[:8]:
            print(f"     - {reason[len(NOT_JUDGED):].strip()[:400]}")
        if len(r.reasons) > 8:
            print(f"     - … {len(r.reasons) - 8} more")
    sites = Counter(f.site for f in r.refutations)
    if r.gate13_laws:
        print(f"   {len(r.gate13_laws)} demoted law postcondition(s) of {vc.LAWS_FILE.as_posix()}: gate 13's rows "
              "(it proves each law at --release; in this debug profile the table's body is not inlined into the "
              "wrapper), admitted on gate 13's verdict and never this survey's evidence")
    if r.refutations:
        known = sum(n for s, n in sites.items() if s is not None and s in ledger)
        routes = ", ".join(f"{n} {k}" for k, n in sorted(Counter(f.route for f in r.refutations).items()))
        print(f"   refutations: {len(r.refutations)} ({routes}) at {len(sites)} identities ({known} in the ledger)"
              + ("" if r.judged else " — NOT gated, the crate is NOT JUDGED"))
        wheres: Dict[Optional[Site], List[str]] = {}
        kinds: Dict[Optional[Site], Counter] = {}
        for f in r.refutations:
            wheres.setdefault(f.site, []).append(f.where)
            kinds.setdefault(f.site, Counter())[f.route] += 1
        for site, n in sorted(sites.items(), key=lambda kv: str(kv[0])):
            tag = "ledger:" + ledger[site].klass if site is not None and site in ledger else "NOT IN LEDGER"
            at = ", ".join(sorted(set(wheres[site])))[:160]
            how = "+".join(sorted(kinds[site]))
            print(f"     {n}x {site if site is not None else '(no site)'} at {at} ({how})  [{tag}]")


def summary_json(results: Sequence[CrateResult]) -> dict:
    """What a run found, for comparing runs: the JUDGED set, the refuted
    identities with multiplicity, the per-status totals, cost."""
    out = {}
    for r in results:
        sites: Dict[str, dict] = {}
        for f in r.refutations:
            key = f.site.ledger_prefix() if f.site else f"(no site)\t{f.function}\t{f.obligation}"
            entry = sites.setdefault(key, {"count": 0, "where": [], "routes": {}})
            entry["count"] += 1
            entry["where"] = sorted(set(entry["where"]) | {f.where})
            entry["routes"][f.route] = entry["routes"].get(f.route, 0) + 1
        out[r.crate] = {
            "judged": r.judged,
            "reasons": [x[len(NOT_JUDGED):].strip()[:300] for x in r.reasons],
            "statuses": dict(r.statuses),
            "budget": dict(r.budget),
            "omitted": dict(r.omitted),
            "refuted": dict(sorted(sites.items())),
            "gate13_laws": len(r.gate13_laws),
            "exit": r.exit,
            "rss_bound_bytes": r.rss_bound,
            "wall_s": r.wall_s,
            "features": r.features,
        }
    return out


def disk_usage(path: Path) -> Optional[int]:
    proc = subprocess.run(["du", "-sk", str(path)], capture_output=True, text=True, check=False)
    try:
        return int(proc.stdout.split()[0]) * 1024
    except (IndexError, ValueError):
        return None


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=str(Path(__file__).resolve().parents[1]))
    ap.add_argument("--out", default=None, help=f"report directory (default <root>/{TARGET.as_posix()}/survey)")
    ap.add_argument("--crates", default=None, help="comma-separated subset of the workspace members")
    ap.add_argument("--keep-json", action="store_true", help="keep report.json/report.html beside report.ndjson")
    ap.add_argument("--rejudge", action="store_true", help="re-judge the kept runs in --out; run nothing")
    ap.add_argument("--check-ledger", action="store_true", help="parse the ledger and exit")
    args = ap.parse_args(argv)
    root = Path(args.root).resolve()
    out = Path(args.out).resolve() if args.out else root / TARGET / "survey"

    ledger, ledger_errors = load_ledger(root)
    shapes = Counter(VERIFIER_FALSE_CAUSE.match(r.cause)["shape"] for r in ledger.values() if r.klass == "verifier-false")
    print(f"ledger: {LEDGER} — {len(ledger)} row(s): "
          + ", ".join(f"{n} {k}" for k, n in sorted(Counter(r.klass for r in ledger.values()).items()))
          + (f" (verifier-false shapes: {', '.join(f'{k}={n}' for k, n in sorted(shapes.items()))})" if shapes else ""))
    if ledger_errors:
        for e in ledger_errors:
            print(f"FAIL: ledger: {e}", file=sys.stderr)
        print(f"verified-survey: FAIL — the ledger does not parse ({len(ledger_errors)} error(s)); nothing was run",
              file=sys.stderr)
        return 1
    if args.check_ledger:
        print("verified-survey: ledger OK")
        return 0

    wanted = [c for c in args.crates.split(",") if c] if args.crates else None
    results: List[CrateResult] = []
    started = time.monotonic()
    if args.rejudge:
        crates = wanted or sorted(p.name[: -len(".lane.json")] for p in out.glob("*.lane.json"))
        if not crates:
            print(f"verified-survey: no kept run under {out}", file=sys.stderr)
            return 2
        for crate in crates:
            results.append(judge_kept(out, crate, root))
            print_crate(results[-1], ledger)
    else:
        for key in ("RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS"):
            if key in os.environ:
                print(f"verified-survey: {key} is set; the survey takes its policy from the manifest only",
                      file=sys.stderr)
                return 2
        try:
            targo = vc.resolve_targo()
            members = workspace_members(metadata(targo, root))
        except SystemExit as e:
            print(f"verified-survey: could not run: {e}", file=sys.stderr)
            return 2
        if wanted:
            unknown = sorted(set(wanted) - {m.name for m in members})
            if unknown:
                print(f"verified-survey: not workspace members: {', '.join(unknown)}", file=sys.stderr)
                return 2
            members = [m for m in members if m.name in wanted]
        print(f"verified survey: {targo}")
        print(f"toolchain: {vc.toolchain_identity(targo)}")
        print(f"members ({len(members)}): {', '.join(m.name for m in members)}")
        cleared = clear_build_tree(root / TARGET)
        if cleared is not None:
            print(f"cleared the previous survey's build tree ({gib(cleared)}): nothing in it is reused")
        out.mkdir(parents=True, exist_ok=True)
        for member in members:
            results.append(run_member(targo, root, out, member, args.keep_json))
            print_crate(results[-1], ledger)
            sys.stdout.flush()
        ran = {m.name for m in members}
        if wanted is None:
            stale = sorted({s.crate for s in ledger} - ran)
            if stale:
                print(f"FAIL: ledger rows name crates that are not workspace members: {', '.join(stale)}",
                      file=sys.stderr)
                ledger_errors = [f"rows for non-members {', '.join(stale)}"]
    elapsed = time.monotonic() - started
    # A re-judge (possibly of a --crates subset) never overwrites the run's own record.
    summary = out / ("summary.rejudge.json" if args.rejudge else "summary.json")
    summary.write_text(json.dumps(summary_json(results), indent=1, sort_keys=True) + "\n", encoding="utf-8")

    v = gate(results, ledger, ledger_errors)
    print()
    judged = [r.crate for r in v.judged]
    unjudged = [r.crate for r in v.not_judged]
    print(f"JUDGED ({len(judged)} of {len(results)}): {', '.join(judged) or 'none'}")
    print(f"NOT JUDGED ({len(unjudged)} of {len(results)}): {', '.join(unjudged) or 'none'} — no verdict of these "
          "crates is evidence in either direction (scripts/verified_survey.py, JUDGED)")
    for line in v.missing:
        print(f"NOT JUDGED (row): {line}")
    unknown_total = sum(r.statuses.get("unknown", 0) + r.statuses.get("timeout", 0) for r in results)
    laws = sum(len(r.gate13_laws) for r in results)
    demoted = sum(f.route == DEMOTED for r in results for f in r.refutations) + laws
    print(f"unknown/timeout rows (reported, never gated): {unknown_total}; {demoted} of them are native "
          f"refutations the seal published as `unknown`, handled above as refutations ({laws} gate 13's law rows)")
    admitted = sum(len(r.gate13_laws) for r in v.judged)
    if not args.rejudge:
        size = disk_usage(root / TARGET)
        print(f"cost: {elapsed:.0f} s wall; {gib(size)} under {TARGET.as_posix()}")
    sys.stdout.flush()
    for f in v.failures:
        print(f"FAIL: {f}", file=sys.stderr)
    if not v.passed:
        print(f"verified-survey: FAIL — {len(v.failures)} finding(s) in JUDGED crate(s) or the ledger; "
              f"{len(unjudged)} crate(s) NOT JUDGED", file=sys.stderr)
        return 1
    print(f"verified-survey: PASS — {len(judged)} crate(s) JUDGED with every refutation (a `failed` row or a "
          "native refutation the seal demotes to `unknown`) in the ledger"
          + (f", but {admitted} demoted law postcondition(s) admitted on gate 13's verdict" if admitted else "")
          + f"; {len(unjudged)} crate(s) NOT JUDGED: {', '.join(unjudged) or 'none'}; "
          f"{len(v.missing)} ledger row(s) NOT JUDGED (expected refutation missing). Unknown rows are not "
          "gated: no crate is claimed verified")
    return 0


if __name__ == "__main__":
    sys.exit(main())
