#!/usr/bin/env python3
"""Declarative leg table for the Clean / AY dependency pins, plus a rewriter.

A pin move is an ATOMIC transaction across every leg listed below.  Moving
fewer than all of them leaves `main` red, and `cargo check` does not execute
the compiled guard (`crates/trust-ir/tests/dependency_pin_coherence.rs`). That
is exactly how a partial move shipped three times. The `static-guard` command
mirrors every runtime assertion in that Rust test but one without requiring a
compiler, while the Rust test remains an independent parity check. The one
assertion with no mirror here: `frontend_lock_resolves_under_locked` asks
Cargo's resolver (`metadata --locked`, offline first, non-compiling but not
toolchain-free) whether `frontend/Cargo.lock` still describes the manifests,
which no text census of the pin rows can decide. That claim is held per test
FUNCTION, not stated: `GUARD_TEST_MIRRORS` names every `#[test]` of the Rust
guard with what mirrors it (or why nothing does), and `static-guard` fails
when the guard gains a test the table does not name or loses one it does.
An assertion added INSIDE an already-mirrored test is not detected that way.

This module is the machine-readable statement of "which files hold the pin".
It never mutates the repository: `apply` and `apply-clean-ay` write candidates
into a staging directory and `scripts/bump-dep-pin.sh` owns the
install/rollback transaction. The coordinated form matters because the Clean
and AY leg sets overlap in the Rust guard and target Clean revisions can
co-own a new AY pin.

Every leg carries an ANCHORED regex plus an exact expected match count, so a
reformatted manifest fails CLOSED (count mismatch) rather than silently
rewriting nothing.  Per-constant anchoring is also what keeps `CLEAN_REVISION`
and `AY_REVISION` independent inside the one file that holds both -- a global
string replace is only accidentally correct while the two SHAs differ.

NOTE FOR MAINTAINERS: the expected counts here duplicate the inventory the
guard test asserts (`assert_exact_manifest_pins(.., 1)` / `(.., 4)`). Adding a
`clean-*` dependency to trust-ir-build means updating BOTH, including dev deps.
"""

from __future__ import annotations

import argparse
import ast
import fnmatch
import hashlib
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, List, Optional, Sequence, Tuple

Reader = Callable[[str], str]


SHA_RE = re.compile(r"^[0-9a-f]{40}$")
SEMVER_RE = re.compile(
    r"^(?:0|[1-9][0-9]*)\."
    r"(?:0|[1-9][0-9]*)\."
    r"(?:0|[1-9][0-9]*)"
    r"(?:-[0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*)?"
    r"(?:\+[0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*)?$"
)

CLEAN_URL = r"https://github\.com/alabsystems/clean\.git"
AY_URL = r"https://github\.com/alabsystems/ay\.git"
SHA = r"(?P<sha>[0-9a-f]{40})"

CLEAN_REMOTE = "https://github.com/alabsystems/clean.git"
AY_REMOTE = "https://github.com/alabsystems/ay.git"


@dataclass(frozen=True)
class Leg:
    """One file that holds a dependency revision."""

    relpath: str
    pattern: str
    note: str
    rewritable: bool = True
    # Exact number of matches required (rewritable legs).  ``None`` means "any
    # count at or above ``minimum``" -- used for lockfiles, whose row count is
    # a resolution detail rather than a hand-maintained inventory.
    expected: Optional[int] = None
    minimum: int = 0
    # When set, only lines containing this substring are scanned.  Lockfile
    # source rows spell the revision twice (``?rev=SHA#SHA``); scanning the
    # whole line catches a split between the two halves.
    line_contains: Optional[str] = None


@dataclass(frozen=True)
class VersionLeg:
    """One reviewed package-version selector that moves with a revision."""

    relpath: str
    pattern: str
    note: str
    expected: int


GUARD_TEST = "crates/trust-ir/tests/dependency_pin_coherence.rs"

CLEAN_LEGS: Tuple[Leg, ...] = (
    Leg(
        relpath="crates/trust-ir/Cargo.toml",
        pattern=rf'git = "{CLEAN_URL}", rev = "{SHA}"',
        note="clean-kernel (optional, behind the clean-expr feature)",
        expected=1,
    ),
    Leg(
        relpath="crates/trust-ir-build/Cargo.toml",
        pattern=rf'git = "{CLEAN_URL}", rev = "{SHA}"',
        note="clean-kernel + clean-mathverse + optional and dev clean-olean + optional and dev clean-verify",
        expected=6,
    ),
    Leg(
        relpath=GUARD_TEST,
        pattern=rf'(?m)^const CLEAN_REVISION: &str = "{SHA}";$',
        note="the guard test's own frozen constant",
        expected=1,
    ),
    Leg(
        relpath="frontend/Cargo.lock",
        pattern=rf"(?P<sha>[0-9a-f]{{40}})",
        note=(
            "SEPARATE WORKSPACE -- frontend/ is `exclude`d from the root, so it "
            "is invisible to --workspace. THE LEG THAT KEEPS GETTING MISSED."
        ),
        rewritable=False,
        minimum=1,
        line_contains="github.com/alabsystems/clean.git",
    ),
    Leg(
        relpath="Cargo.lock",
        pattern=rf"(?P<sha>[0-9a-f]{{40}})",
        note=(
            "root lock -- since the root [patch] was deleted (2026-08-19) this "
            "records the revision on every clean.git package, so `--locked` is "
            "now a real second check. ZERO rows here means the patch is back."
        ),
        rewritable=False,
        minimum=1,
        line_contains="github.com/alabsystems/clean.git",
    ),
)

AY_LEGS: Tuple[Leg, ...] = (
    Leg(
        relpath="crates/trust-ir-ay/Cargo.toml",
        pattern=rf'git = "{AY_URL}", rev = "{SHA}"',
        note=(
            "TWO declarations: `ay` (the solver facade) and `ay-proof` (the "
            "trust-free bv-blast exporter, which the `ay` facade does not "
            "re-export). Both must move together or the adapter links two ay "
            "revisions."
        ),
        expected=2,
    ),
    Leg(
        relpath="crates/trust-ir-ay/src/vc.rs",
        pattern=rf'(?m)^pub const AY_REV: &str = "{SHA}";$',
        note=(
            "stamps solver provenance into every emitted bundle (vc.rs:1044); "
            "a stale value silently misreports which solver replayed a proof"
        ),
        expected=1,
    ),
    Leg(
        relpath="crates/trust-ir-ay/src/bvblast.rs",
        pattern=rf'(?m)^pub const BVBLAST_PROVER: &str = "trust-ir-ay/bvblast@{SHA}";$',
        note=(
            "stamps the exact AY revision into stored bit-blast proof authority; "
            "a stale value accepts the right payload under a false solver identity"
        ),
        expected=1,
    ),
    Leg(
        relpath=GUARD_TEST,
        pattern=rf'(?m)^const AY_REVISION: &str = "{SHA}";$',
        note="the guard test's own frozen constant",
        expected=1,
    ),
    Leg(
        relpath="Cargo.lock",
        pattern=rf"(?P<sha>[0-9a-f]{{40}})",
        note="root lock -- the ay graph resolved through trust-ir-ay and Clean",
        rewritable=False,
        minimum=1,
        line_contains="github.com/alabsystems/ay.git",
    ),
)

LEGS: Dict[str, Tuple[Leg, ...]] = {"clean": CLEAN_LEGS, "ay": AY_LEGS}

# Package versions are independent transaction legs. Cargo interprets an exact
# dependency string such as ``0.1.0`` as the compatible requirement ``^0.1.0``;
# consequently a target commit that publishes ``0.2.0`` cannot be selected by
# changing only ``rev``. Keep these patterns separate from the revision table
# so both named captures remain exact-count anchored.
VERSION_LEGS: Dict[str, Tuple[VersionLeg, ...]] = {
    "clean": (
        VersionLeg(
            relpath="crates/trust-ir/Cargo.toml",
            pattern=(
                rf'(?m)^(?=[^#\n]*git = "{CLEAN_URL}")[^#\n]*?'
                r'version = "(?P<version>[^"]+)"'
            ),
            note="clean-kernel dependency requirement",
            expected=1,
        ),
        VersionLeg(
            relpath="crates/trust-ir-build/Cargo.toml",
            pattern=(
                rf'(?m)^(?=[^#\n]*git = "{CLEAN_URL}")[^#\n]*?'
                r'version = "(?P<version>[^"]+)"'
            ),
            note="clean-kernel + clean-mathverse + optional and dev clean-olean + optional and dev clean-verify requirements",
            expected=6,
        ),
        VersionLeg(
            relpath=GUARD_TEST,
            pattern=r'(?m)^const CLEAN_VERSION: &str = "(?P<version>[^"]+)";$',
            note="the guard test's frozen Clean package version",
            expected=1,
        ),
    ),
    "ay": (
        VersionLeg(
            relpath="crates/trust-ir-ay/Cargo.toml",
            pattern=(
                rf'(?m)^(?=[^#\n]*git = "{AY_URL}")[^#\n]*?'
                r'version = "(?P<version>[^"]+)"'
            ),
            note="ay + ay-proof dependency requirements",
            expected=2,
        ),
        VersionLeg(
            relpath=GUARD_TEST,
            pattern=r'(?m)^const AY_VERSION: &str = "(?P<version>[^"]+)";$',
            note="the guard test's frozen AY package version",
            expected=1,
        ),
    ),
}

REMOTES: Dict[str, str] = {"clean": CLEAN_REMOTE, "ay": AY_REMOTE}

# Cross-repository legs cannot be rewritten or audited by `census`.
# bump-dep-pin.sh checks their immutable target-commit content as a
# precondition; ambient sibling checkout state is never authoritative.
EXTERNAL_LEGS: Dict[str, str] = {
    "clean": (
        "RETIRED 2026-08-19: there is no ../clean working-tree leg any more. "
        "The root [patch] was deleted, so cargo compiles clean.git AT THE "
        "PINNED REV. Do NOT check ../clean out at the pin and do NOT follow "
        "its HEAD -- Clean pins trust-ir back through clean-reflect, so "
        "chasing HEAD reopens the pin cycle that deletion cut. Cross-repo "
        "publication uses the ratified predecessor-epoch cut: backedges may "
        "intentionally retain predecessor identities while successors "
        "advance. Verify that exact cohort with its final epoch receipt, not "
        "with a raw five-workspace SHA-equality requirement."
    ),
    "ay": (
        "The selected Clean COMMIT's Cargo.toml CO-OWNS the AY pin (7 "
        "declarations). If it disagrees the root lock carries two ay graphs "
        "and the guard fails; an AY-only move checks the frozen Clean commit, "
        "while a Clean + AY move checks the target Clean commit."
    ),
}


class PinError(Exception):
    """A leg could not be read or rewritten as declared."""


class NotAGitCheckout(Exception):
    """The undeclared-pin-site audit needs a tracked-file set and has none."""


# --------------------------------------------------------------------------
# Pure helpers (no I/O) -- the unit-testable core.
# --------------------------------------------------------------------------


# Rust str::trim uses Unicode White_Space, excluding Python's additional
# U+001C..U+001F controls. Keep this local to the existing pin-checking core.
_RUST_WHITESPACE = (
    "\t\n\v\f\r \u0085\u00a0\u1680"
    "\u2000\u2001\u2002\u2003\u2004\u2005\u2006\u2007\u2008\u2009\u200a"
    "\u2028\u2029\u202f\u205f\u3000"
)


def _rust_trim(text: str) -> str:
    return text.strip(_RUST_WHITESPACE)


def _rust_lines(text: str) -> List[str]:
    # Rust lines() splits LF/CRLF, excludes a final empty line, and retains
    # a bare CR at unterminated EOF. Other Unicode separators stay in a line.
    rows = text.split("\n")
    terminated = len(rows) - 1
    return [
        row[:-1] if index < terminated and row.endswith("\r") else row
        for index, row in enumerate(rows)
        if index < terminated or row != ""
    ]


def _scan_text(text: str, leg: Leg) -> str:
    if leg.line_contains is None:
        return text
    return "\n".join(
        line for line in text.splitlines() if leg.line_contains in line
    )


def find_shas(text: str, leg: Leg) -> List[str]:
    """Every revision this leg declares, in file order (duplicates kept)."""

    scanned = _scan_text(text, leg)
    return [match.group("sha") for match in re.finditer(leg.pattern, scanned)]


def substitute(text: str, leg: Leg, new_sha: str) -> Tuple[str, int]:
    """Rewrite every revision this leg declares; return (text, match count)."""

    if leg.line_contains is not None:
        raise PinError(
            f"{leg.relpath}: line-filtered legs are lockfiles and are refreshed "
            "by cargo, never rewritten"
        )
    pieces: List[str] = []
    cursor = 0
    count = 0
    for match in re.finditer(leg.pattern, text):
        start, end = match.span("sha")
        pieces.append(text[cursor:start])
        pieces.append(new_sha)
        cursor = end
        count += 1
    pieces.append(text[cursor:])
    return "".join(pieces), count


def find_versions(text: str, leg: VersionLeg) -> List[str]:
    """Every package-version selector this leg declares, in file order."""

    return [match.group("version") for match in re.finditer(leg.pattern, text)]


def substitute_version(
    text: str, leg: VersionLeg, new_version: str
) -> Tuple[str, int]:
    """Rewrite this leg's version captures; return (text, match count)."""

    pieces: List[str] = []
    cursor = 0
    count = 0
    for match in re.finditer(leg.pattern, text):
        start, end = match.span("version")
        pieces.append(text[cursor:start])
        pieces.append(new_version)
        cursor = end
        count += 1
    pieces.append(text[cursor:])
    return "".join(pieces), count


def check_count(leg: Leg, count: int) -> Optional[str]:
    """Return a violation message if this leg's match count is wrong."""

    if leg.expected is not None and count != leg.expected:
        return (
            f"expected exactly {leg.expected} pinned revision(s), found {count} "
            "-- the declaration shape drifted; update scripts/pin_rewrite.py "
            "and the guard test together"
        )
    if count < leg.minimum:
        return (
            f"expected at least {leg.minimum} pinned revision(s), found {count} "
            "-- the pin vanished from this leg"
        )
    return None


def check_version_count(leg: VersionLeg, count: int) -> Optional[str]:
    """Return a violation when a reviewed version leg changed shape."""

    if count != leg.expected:
        return (
            f"expected exactly {leg.expected} package version selector(s), "
            f"found {count} -- the declaration shape drifted; update "
            "scripts/pin_rewrite.py and the guard test together"
        )
    return None


@dataclass(frozen=True)
class LegReport:
    relpath: str
    count: int
    shas: Tuple[str, ...]
    violation: Optional[str]


@dataclass(frozen=True)
class Census:
    dep: str
    legs: Tuple[LegReport, ...]

    @property
    def distinct(self) -> Tuple[str, ...]:
        seen: List[str] = []
        for leg in self.legs:
            for sha in leg.shas:
                if sha not in seen:
                    seen.append(sha)
        return tuple(seen)

    @property
    def coherent(self) -> bool:
        if any(leg.violation for leg in self.legs):
            return False
        return len(self.distinct) == 1

    def current(self) -> str:
        if not self.coherent:
            raise PinError(f"{self.dep} pin is not a singleton: {self.distinct}")
        return self.distinct[0]

    def render(self) -> str:
        width = max(len(leg.relpath) for leg in self.legs)
        rows = [f"{self.dep} pin legs:"]
        for leg in self.legs:
            shas = ", ".join(sorted(set(leg.shas))) or "<none>"
            rows.append(f"  {leg.relpath.ljust(width)}  n={leg.count:<3} {shas}")
            if leg.violation is not None:
                rows.append(f"  {' ' * width}  !! {leg.violation}")
        external = EXTERNAL_LEGS.get(self.dep)
        if external:
            rows.append(f"  (not auditable from this repo) {external}")
        return "\n".join(rows)


@dataclass(frozen=True)
class VersionCensus:
    dep: str
    legs: Tuple[LegReport, ...]

    @property
    def distinct(self) -> Tuple[str, ...]:
        seen: List[str] = []
        for leg in self.legs:
            for version in leg.shas:
                if version not in seen:
                    seen.append(version)
        return tuple(seen)

    @property
    def coherent(self) -> bool:
        if any(leg.violation for leg in self.legs):
            return False
        return len(self.distinct) == 1 and bool(self.distinct)

    def current(self) -> str:
        if not self.coherent:
            raise PinError(
                f"{self.dep} package version is not a singleton: {self.distinct}"
            )
        return self.distinct[0]

    def render(self) -> str:
        width = max(len(leg.relpath) for leg in self.legs)
        rows = [f"{self.dep} package-version legs:"]
        for leg in self.legs:
            versions = ", ".join(sorted(set(leg.shas))) or "<none>"
            rows.append(
                f"  {leg.relpath.ljust(width)}  n={leg.count:<3} {versions}"
            )
            if leg.violation is not None:
                rows.append(f"  {' ' * width}  !! {leg.violation}")
        return "\n".join(rows)


#: Every `#[test]` of the compiled guard (`GUARD_TEST`), with what mirrors it
#: in `static_guard`. `None` marks the deliberate exemption, with its reason
#: in the module docstring. `static_guard` refuses a guard test this table
#: does not name, and a row whose test is gone: a new assertion the mirror
#: does not know is how the mirror's "exact" claim went false once already
#: (`x86_icmp_certificate_rule_names_the_pinned_ay`, 2026-09-30, until this
#: table existed). Parity is per test FUNCTION; an assertion added inside an
#: already-mirrored test is not detected here.
GUARD_TEST_MIRRORS: Dict[str, Optional[str]] = {
    "clean_consumability_baseline_is_exact_and_atomic": (
        "the two Clean manifest inventories and frontend/Cargo.lock's one "
        "Clean package, version and source"
    ),
    "clean_pin_is_not_path_patched": (
        "no root clean.git [patch]; every root Cargo.lock clean.git source "
        "exact, and at least one"
    ),
    "frontend_lock_resolves_under_locked": None,
    "ay_manifest_and_root_lock_are_exact_and_atomic": (
        "the trust-ir-ay manifest, AY_REV, BVBLAST_PROVER and the root "
        "Cargo.lock's AY selectors, sources and versions"
    ),
    "x86_icmp_certificate_rule_names_the_pinned_ay": (
        "CHC_X86_ICMP_CERTIFICATE_RULE.ay (rev, version) equal to "
        "(AY_REVISION, AY_VERSION)"
    ),
}

GUARD_TEST_ATTRIBUTE = re.compile(r"(?m)^#\[test\]$")
GUARD_TEST_FUNCTION = re.compile(
    r"(?m)^#\[test\]\n(?:#\[[^\n]*\]\n)*fn (?P<name>[A-Za-z_][A-Za-z0-9_]*)\(\)"
)


def guard_test_parity(guard: str) -> List[str]:
    """Violations of ``GUARD_TEST_MIRRORS`` against the guard's ``#[test]`` set."""

    names = [match["name"] for match in GUARD_TEST_FUNCTION.finditer(guard)]
    attributes = len(GUARD_TEST_ATTRIBUTE.findall(guard))
    if len(names) != attributes:
        return [
            f"{GUARD_TEST}: {attributes} top-level #[test] attribute(s) but "
            f"{len(names)} readable `fn name()` test(s); the mirror table "
            "cannot be checked against a guard it cannot read"
        ]
    violations: List[str] = []
    known = set(GUARD_TEST_MIRRORS)
    for name in sorted(set(names) - known):
        violations.append(
            f"{GUARD_TEST} test {name} has no row in "
            "scripts/pin_rewrite.py GUARD_TEST_MIRRORS: mirror its assertions "
            "in static_guard (or record why nothing can) before claiming the "
            "static guard is exact"
        )
    for name in sorted(known - set(names)):
        violations.append(
            f"scripts/pin_rewrite.py GUARD_TEST_MIRRORS names {name}, which "
            f"{GUARD_TEST} no longer defines"
        )
    if len(names) != len(set(names)):
        violations.append(f"{GUARD_TEST} defines a #[test] name twice")
    return violations


#: The x86-64 vector-compare certificate rule names the AY that produced
#: every certificate. It is NOT a pin leg: the bumper cannot move it, because
#: moving it asserts a re-certification (`docs/dialects.md`, the per-cell
#: rule). It is read exactly as `publish/transforms.sh` T1 reads it: inside
#: the ONE `CHC_X86_ICMP_CERTIFICATE_RULE` declaration, anchored on its
#: `ay: ChcX86IcmpCertifyingBuild` literal, never on prose.
CERTIFICATE_RULE_PATH = "crates/trust-ir/src/request/evidence.rs"
CERTIFICATE_RULE_DECLARATION = (
    "pub const CHC_X86_ICMP_CERTIFICATE_RULE: ChcX86IcmpCertificateRule = "
    "ChcX86IcmpCertificateRule {\n"
)
CERTIFICATE_RULE_AY = re.compile(
    r'^    ay: ChcX86IcmpCertifyingBuild \{\n'
    r'        package: "ay",\n'
    r'        rev: "(?P<rev>[^"\n]*)",\n'
    r'        version: "(?P<version>[^"\n]*)",\n',
    re.MULTILINE,
)


def certificate_rule_ay(text: str) -> Tuple[str, str]:
    """The rule's AY ``(rev, version)``, or ``PinError`` naming why not."""

    if text.count(CERTIFICATE_RULE_DECLARATION) != 1:
        raise PinError(
            f"{CERTIFICATE_RULE_PATH} must declare CHC_X86_ICMP_CERTIFICATE_RULE "
            "exactly once, in the form the mirror anchors on"
        )
    start = text.index(CERTIFICATE_RULE_DECLARATION)
    end = text.find("\n};\n", start)
    if end < 0:
        raise PinError(
            f"{CERTIFICATE_RULE_PATH}: the CHC_X86_ICMP_CERTIFICATE_RULE "
            "declaration never closes"
        )
    matches = list(CERTIFICATE_RULE_AY.finditer(text, start, end))
    if len(matches) != 1:
        raise PinError(
            f"{CERTIFICATE_RULE_PATH}: CHC_X86_ICMP_CERTIFICATE_RULE must carry "
            "exactly one `ay: ChcX86IcmpCertifyingBuild { package, rev, version, .. }` "
            f"literal, found {len(matches)}"
        )
    return matches[0]["rev"], matches[0]["version"]


def census(read: Reader, dep: str) -> Census:
    reports: List[LegReport] = []
    for leg in LEGS[dep]:
        text = read(leg.relpath)
        shas = find_shas(text, leg)
        reports.append(
            LegReport(
                relpath=leg.relpath,
                count=len(shas),
                shas=tuple(shas),
                violation=check_count(leg, len(shas)),
            )
        )
    return Census(dep=dep, legs=tuple(reports))


def version_census(read: Reader, dep: str) -> VersionCensus:
    reports: List[LegReport] = []
    for leg in VERSION_LEGS[dep]:
        versions = find_versions(read(leg.relpath), leg)
        reports.append(
            LegReport(
                relpath=leg.relpath,
                count=len(versions),
                shas=tuple(versions),
                violation=check_version_count(leg, len(versions)),
            )
        )
    return VersionCensus(dep=dep, legs=tuple(reports))


@dataclass(frozen=True)
class StaticGuardReport:
    """Toolchain-free mirror of ``dependency_pin_coherence.rs``."""

    violations: Tuple[str, ...]

    @property
    def coherent(self) -> bool:
        return not self.violations

    def render(self) -> str:
        if self.coherent:
            return (
                "STATIC GUARD: PASS -- exact Clean/AY manifest, provenance, "
                "root-patch, lockfile and certificate-rule AY coherence checks "
                "passed, and every guard test has a mirror row"
            )
        rows = [
            "STATIC GUARD: FAIL -- dependency_pin_coherence mirror found "
            f"{len(self.violations)} violation(s):"
        ]
        rows.extend(f"  - {violation}" for violation in self.violations)
        return "\n".join(rows)


def static_guard(read: Reader) -> StaticGuardReport:
    """Mirror every runtime assertion in ``dependency_pin_coherence.rs`` but one.

    This is deliberately independent of Rust compilation so a missing Trust
    stage2 cannot turn the bumper's best-effort compiled guard into a silent
    authority gap. The Rust test remains the canonical compiled check and runs
    whenever Targo is available; this mirror is mandatory on every bump.

    Not mirrored: ``frontend_lock_resolves_under_locked``, which runs
    Cargo's resolver over ``frontend/Cargo.lock`` (see the module docstring).
    Which guard test each check below mirrors is ``GUARD_TEST_MIRRORS``, and
    the first check is that the table and the guard's tests agree.
    """

    violations: List[str] = list(guard_test_parity(read(GUARD_TEST)))

    # The leg and package-version censuses are part of the fallback contract,
    # even though the bumper also prints them separately. Keeping them here
    # makes the standalone `static-guard` command complete and fail-closed.
    for dep in sorted(LEGS):
        revision_report = census(read, dep)
        if not revision_report.coherent:
            violations.append(
                f"{dep} revision legs are not one exact authority: "
                f"{revision_report.distinct or ('<none>',)}"
            )
        version_report = version_census(read, dep)
        if not version_report.coherent:
            violations.append(
                f"{dep} package-version legs are not one exact version: "
                f"{version_report.distinct or ('<none>',)}"
            )

    guard = read(GUARD_TEST)
    constants: Dict[str, str] = {}
    for name in (
        "CLEAN_REPOSITORY",
        "CLEAN_REVISION",
        "CLEAN_VERSION",
        "AY_REPOSITORY",
        "AY_REVISION",
        "AY_VERSION",
    ):
        values = re.findall(
            rf'(?m)^const {re.escape(name)}: &str = "([^"]+)";$', guard
        )
        if len(values) != 1:
            violations.append(
                f"{GUARD_TEST} must define exactly one canonical {name}; "
                f"found {len(values)}"
            )
        else:
            constants[name] = values[0]

    # Without all six constants no dependent comparison has a trustworthy
    # authority. Report the shape failures above and stop rather than deriving
    # follow-on diagnostics from guessed defaults.
    if len(constants) != 6:
        return StaticGuardReport(tuple(violations))

    clean_repository = constants["CLEAN_REPOSITORY"]
    clean_revision = constants["CLEAN_REVISION"]
    clean_version = constants["CLEAN_VERSION"]
    ay_repository = constants["AY_REPOSITORY"]
    ay_revision = constants["AY_REVISION"]
    ay_version = constants["AY_VERSION"]

    if clean_repository != CLEAN_REMOTE:
        violations.append(
            f"CLEAN_REPOSITORY is not the canonical authority {CLEAN_REMOTE}: "
            f"{clean_repository!r}"
        )
    if ay_repository != AY_REMOTE:
        violations.append(
            f"AY_REPOSITORY is not the canonical authority {AY_REMOTE}: "
            f"{ay_repository!r}"
        )
    if not SHA_RE.fullmatch(clean_revision):
        violations.append(f"CLEAN_REVISION is not a full 40-hex SHA: {clean_revision!r}")
    if not SHA_RE.fullmatch(ay_revision):
        violations.append(f"AY_REVISION is not a full 40-hex SHA: {ay_revision!r}")
    if not SEMVER_RE.fullmatch(clean_version):
        violations.append(
            f"CLEAN_VERSION is not an exact canonical semantic version: {clean_version!r}"
        )
    if not SEMVER_RE.fullmatch(ay_version):
        violations.append(
            f"AY_VERSION is not an exact canonical semantic version: {ay_version!r}"
        )

    exact_clean_git = f'git = "{clean_repository}"'
    exact_clean_rev = f'rev = "{clean_revision}"'
    exact_clean_version = f'version = "{clean_version}"'
    for manifest_name, expected_count in (
        ("crates/trust-ir/Cargo.toml", 1),
        ("crates/trust-ir-build/Cargo.toml", 6),
    ):
        dependency_lines = [
            line.strip()
            for line in read(manifest_name).splitlines()
            if not line.strip().startswith("#")
            and line.strip().startswith("clean-")
            and " = {" in line.strip()
        ]
        if len(dependency_lines) != expected_count:
            violations.append(
                f"{manifest_name} Clean dependency inventory: expected "
                f"{expected_count}, found {len(dependency_lines)}"
            )
        for line in dependency_lines:
            if exact_clean_version not in line:
                violations.append(
                    f"{manifest_name} Clean dependency has the wrong version: {line}"
                )
            if exact_clean_git not in line:
                violations.append(
                    f"{manifest_name} Clean dependency has the wrong repository: {line}"
                )
            if exact_clean_rev not in line:
                violations.append(
                    f"{manifest_name} Clean dependency has the wrong revision: {line}"
                )
            if "branch =" in line or "tag =" in line:
                violations.append(
                    f"{manifest_name} Clean dependency has a floating selector: {line}"
                )

    exact_clean_source = (
        f'source = "git+{clean_repository}?rev={clean_revision}#{clean_revision}"'
    )
    clean_git_source = f"git+{clean_repository}"
    frontend_lock = read("frontend/Cargo.lock")
    frontend_clean_packages = [
        package
        for package in frontend_lock.split("[[package]]")
        if any(
            _rust_trim(line).startswith('name = "clean-')
            for line in _rust_lines(package)
        )
    ]
    if len(frontend_clean_packages) != 1:
        violations.append(
            "frontend/Cargo.lock Clean package inventory: expected 1, "
            f"found {len(frontend_clean_packages)}"
        )
    else:
        package_lines = {_rust_trim(line) for line in _rust_lines(frontend_clean_packages[0])}
        if f'version = "{clean_version}"' not in package_lines:
            violations.append(
                "frontend/Cargo.lock Clean package does not use the exact "
                f"version {clean_version}"
            )
        if exact_clean_source not in package_lines:
            violations.append(
                "frontend/Cargo.lock Clean package does not use the exact "
                f"source {exact_clean_source}"
            )
    frontend_clean_source_rows = [
        _rust_trim(line)
        for line in _rust_lines(frontend_lock)
        if clean_git_source in _rust_trim(line)
    ]
    if frontend_clean_source_rows != [exact_clean_source]:
        violations.append(
            "frontend/Cargo.lock contains a floating, duplicated, or split "
            f"Clean source: {frontend_clean_source_rows!r}"
        )

    root_manifest = read("Cargo.toml")
    root_clean_patches = [
        line.strip()
        for line in root_manifest.splitlines()
        if not line.strip().startswith("#")
        and line.strip().startswith("[patch")
        and "clean.git" in line.strip()
    ]
    if root_clean_patches:
        violations.append(
            "Cargo.toml re-introduces a Clean path patch: "
            f"{root_clean_patches!r}"
        )

    root_lock = read("Cargo.lock")
    root_clean_source_rows = [
        _rust_trim(line)
        for line in _rust_lines(root_lock)
        if clean_git_source in _rust_trim(line)
    ]
    if not root_clean_source_rows:
        violations.append("Cargo.lock records no clean.git source")
    elif any(line != exact_clean_source for line in root_clean_source_rows):
        violations.append(
            "Cargo.lock contains a stale or split Clean source: "
            f"{root_clean_source_rows!r}"
        )

    ay_manifest_lines = [
        line.strip()
        for line in read("crates/trust-ir-ay/Cargo.toml").splitlines()
        if not line.strip().startswith("#")
        and (
            line.strip().startswith("ay = {")
            or line.strip().startswith("ay-proof = {")
        )
    ]
    if len(ay_manifest_lines) != 2:
        violations.append(
            "crates/trust-ir-ay/Cargo.toml AY dependency inventory: "
            f"expected 2, found {len(ay_manifest_lines)}"
        )
    exact_ay_git = f'git = "{ay_repository}"'
    exact_ay_rev = f'rev = "{ay_revision}"'
    exact_ay_version = f'version = "{ay_version}"'
    for line in ay_manifest_lines:
        if not (
            exact_ay_git in line
            and exact_ay_rev in line
            and exact_ay_version in line
            and "branch =" not in line
            and "tag =" not in line
        ):
            violations.append(
                "crates/trust-ir-ay/Cargo.toml has a non-exact AY authority: "
                f"{line}"
            )

    exact_ay_provenance = f'pub const AY_REV: &str = "{ay_revision}";'
    if not any(
        line.strip() == exact_ay_provenance
        for line in read("crates/trust-ir-ay/src/vc.rs").splitlines()
    ):
        violations.append("crates/trust-ir-ay/src/vc.rs AY_REV is stale or missing")
    exact_bvblast_prover = (
        'pub const BVBLAST_PROVER: &str = '
        f'"trust-ir-ay/bvblast@{ay_revision}";'
    )
    if not any(
        line.strip() == exact_bvblast_prover
        for line in read("crates/trust-ir-ay/src/bvblast.rs").splitlines()
    ):
        violations.append(
            "crates/trust-ir-ay/src/bvblast.rs BVBLAST_PROVER is stale or missing"
        )

    ay_selector = f"git+{ay_repository}?rev={ay_revision}"
    ay_git_selector = f"git+{ay_repository}?rev="
    root_ay_selector_rows = [
        _rust_trim(line)
        for line in _rust_lines(root_lock)
        if ay_git_selector in _rust_trim(line)
    ]
    if not root_ay_selector_rows:
        violations.append("Cargo.lock records no ay.git source")
    elif any(ay_selector not in line for line in root_ay_selector_rows):
        violations.append(
            "Cargo.lock contains a stale or split AY selector: "
            f"{root_ay_selector_rows!r}"
        )

    exact_ay_source = f'source = "{ay_selector}#{ay_revision}"'
    root_ay_source_rows = [
        line for line in root_ay_selector_rows if line.startswith("source = ")
    ]
    if not root_ay_source_rows or any(
        line != exact_ay_source for line in root_ay_source_rows
    ):
        violations.append(
            "Cargo.lock does not resolve every AY package to the exact source: "
            f"{root_ay_source_rows!r}"
        )

    root_ay_packages = [
        package
        for package in root_lock.split("[[package]]")
        if any(
            _rust_trim(line) == exact_ay_source for line in _rust_lines(package)
        )
    ]
    if len(root_ay_packages) != len(root_ay_source_rows):
        violations.append(
            "Cargo.lock AY package/source cardinality mismatch: "
            f"{len(root_ay_packages)} package(s), "
            f"{len(root_ay_source_rows)} source row(s)"
        )
    exact_ay_package_version = f'version = "{ay_version}"'
    if any(
        not any(
            _rust_trim(line) == exact_ay_package_version
            for line in _rust_lines(package)
        )
        for package in root_ay_packages
    ):
        violations.append(
            "Cargo.lock resolves an AY package outside the exact version "
            f"{ay_version}"
        )

    # x86_icmp_certificate_rule_names_the_pinned_ay: the certificate rule's AY
    # is the AY pin, revision AND version, as publish/transforms.sh T1 holds it.
    try:
        rule_ay = certificate_rule_ay(read(CERTIFICATE_RULE_PATH))
    except PinError as error:
        violations.append(str(error))
    else:
        if rule_ay != (ay_revision, ay_version):
            violations.append(
                "CHC_X86_ICMP_CERTIFICATE_RULE.ay names "
                f"{rule_ay[0]} {rule_ay[1]}, not the AY pin {ay_revision} "
                f"{ay_version}: re-certify the x86-64 vector-compare certificate "
                "cells under the new AY (trust-cg scripts/check_x86_icmp_certificates.py) "
                f"and move the rule's ay.rev, ay.version and certifying_sha256 in "
                f"{CERTIFICATE_RULE_PATH} with the pin; the bumper cannot move them"
            )

    return StaticGuardReport(tuple(violations))


#: Build inputs a pin can actually take effect from. Deliberately narrow —
#: docs, ledgers and design notes quote revisions in prose and must not trip
#: the complement check, but anything cargo reads must.
PIN_BEARING_SUFFIXES = (".toml", ".lock", ".rs")

# Exact captured inputs in the sealed historical SourceOp packet, not Cargo
# workspaces. Their original names and bytes are part of the nested/outer
# artifact manifests, so rewriting or renaming them would damage that evidence.
# This is deliberately not a reports/ exemption: every new/neighboring build
# input still participates in the complement census. A changed or redirected
# captured input refuses even when it no longer contains the dependency URL.
ARCHIVED_PIN_INPUT_SHA256 = {
    "reports/2026-11-08-source-value-operational/evidence/afa-corrected-compact/source/Cargo.lock":
        "cd930175713a5dbafbe1231aa4f19aa36f6737cc92e62211dc59004ff0b3abf5",
    "reports/2026-11-08-source-value-operational/evidence/afa-corrected-compact/source/crates/trust-ir-build/Cargo.toml":
        "479b6d4bcb8c8ced8dd4d7cf16eb87491d73e98bb44db5e4c2dc30a7d64800dc",
}
ARCHIVED_SOURCE_ROOT = "reports/2026-11-08-source-value-operational/evidence/afa-corrected-compact/source"
ARCHIVED_SOURCE_MANIFEST = "reports/2026-11-08-source-value-operational/evidence/afa-corrected-compact/artifact-manifest.json"
ARCHIVED_SOURCE_MANIFEST_SHA256 = "e2083a87711b4fc2a63d63ce1eefaa62946b3c8ba7df82ac05c45feef2cfdb10"


def physically_within(path: Path, directory: Path) -> bool:
    """Include filesystem aliases whose spelling resolve() does not change."""
    for ancestor in (path, *path.parents):
        try:
            if ancestor.samefile(directory):
                return True
        except FileNotFoundError:
            continue
        except OSError as error:
            raise PinError(f"cannot establish filesystem containment: {error}") from error
    return False


def inspect_cargo_pattern(base: Path, value: str, root: Path, boundary: Path) -> None:
    pattern = base / value
    if "**" in pattern.parts or len(pattern.parts) > 64:
        raise PinError("recursive or over-depth Cargo glob cannot prove archive inertness")
    candidates = [Path(pattern.anchor)]
    visited = 0
    for part in pattern.parts[1:]:
        following = []
        for candidate in candidates:
            if any(char in part for char in "*?["):
                if not physically_within(candidate, root):
                    raise PinError("outside-repository Cargo glob cannot prove archive inertness")
                if not candidate.is_dir():
                    continue
                try:
                    with os.scandir(candidate) as entries:
                        for entry in entries:
                            visited += 1
                            if visited > 4096:
                                raise PinError("Cargo glob archive inspection budget exhausted")
                            if fnmatch.fnmatchcase(entry.name.casefold(), part.casefold()):
                                following.append(Path(entry.path).resolve())
                except OSError as error:
                    raise PinError(f"cannot inspect Cargo glob: {error}") from error
            else:
                following.append((candidate / part).resolve())
        if len(following) > 256:
            raise PinError("Cargo glob archive match budget exhausted")
        for candidate in following:
            if physically_within(candidate, boundary):
                raise PinError("Cargo glob adopts the archived pin boundary")
        candidates = following


def validate_archived_pin_boundary(root: Path, tracked: Sequence[str]) -> None:
    boundary = root / ARCHIVED_SOURCE_ROOT
    if not boundary.exists() and not any(
        p.startswith(ARCHIVED_SOURCE_ROOT + "/") for p in tracked
    ):
        return
    manifest = root / ARCHIVED_SOURCE_MANIFEST
    for relative in (ARCHIVED_SOURCE_ROOT, ARCHIVED_SOURCE_MANIFEST):
        cursor = root
        for part in Path(relative).parts:
            cursor /= part
            if cursor.is_symlink():
                raise PinError("archived pin boundary contains a symlink")
    if manifest.is_symlink() or not manifest.is_file():
        raise PinError("archived pin boundary has no regular sealed manifest")
    payload = manifest.read_bytes()
    if hashlib.sha256(payload).hexdigest() != ARCHIVED_SOURCE_MANIFEST_SHA256:
        raise PinError("archived pin boundary manifest changed")
    rows = json.loads(payload)["files"]
    expected = {r["path"][7:]: r["sha256"] for r in rows if r["path"].startswith("source/")}
    actual = set()
    for path in boundary.rglob("*"):
        if path.is_symlink():
            raise PinError("archived pin boundary contains a symlink")
        if path.is_file():
            relative = path.relative_to(boundary).as_posix()
            if relative not in expected:
                raise PinError(f"archived pin boundary gained an input: {relative}")
            if hashlib.sha256(path.read_bytes()).hexdigest() != expected[relative]:
                raise PinError(f"archived pin input content changed: {relative}")
            actual.add(relative)
    if actual != set(expected):
        raise PinError("archived pin boundary lost a captured input")
    # Cargo can activate an unchanged captured manifest through a workspace
    # member or path dependency without repeating its Clean/AY URL. Inspect
    # path/membership values, including glob membership; Cargo's own resolver
    # still judges syntax and the actual dependency graph. Quoted strings and
    # comments are tokenized before tracking assignments, so '=' inside an
    # earlier member/description cannot hide a later member.
    parent = boundary.parent
    while parent != root:
        if (parent / "Cargo.toml").exists() or (parent / "Cargo.toml").is_symlink():
            raise PinError("archived pin boundary gained an enclosing Cargo manifest")
        parent = parent.parent
    destinations = [boundary.resolve(), *(p.parent.resolve() for p in boundary.rglob("Cargo.toml"))]
    literals = re.compile(
        r'#[^\n]*|"""(?:\\.|(?!""")[\s\S])*"""'
        + r"|'''[\s\S]*?'''"
        + r'''|"(?:\\.|[^"\\])*"|'[^']*' '''.strip()
    )
    manifests = {p for p in tracked if p.endswith("Cargo.toml") and not p.startswith(ARCHIVED_SOURCE_ROOT + "/")}
    if (root / "Cargo.toml").exists():
        manifests.add("Cargo.toml")
    for relative in sorted(manifests):
        path = root / relative
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            raise PinError(f"cannot inspect Cargo adoption of archive: {relative}") from error
        cursor = 0
        assignment = None
        quoted_key = None
        for match in literals.finditer(text):
            gap = text[cursor:match.start()]
            assignments = re.findall(r"([A-Za-z_][A-Za-z0-9_-]*)\s*=", gap)
            if assignments:
                assignment = assignments[-1]
            elif quoted_key is not None and gap.lstrip().startswith("="):
                assignment = quoted_key
            cursor = match.end()
            token = match.group()
            if token.startswith("#"):
                continue
            line_prefix = text[text.rfind("\n", 0, match.start()) + 1:match.start()]
            if line_prefix.lstrip().startswith("["):
                # Quoted table keys (notably profile.package."*") are names,
                # not workspace/path values.
                quoted_key = None
                continue
            triple = token.startswith(('"""', "'''"))
            try:
                if token.startswith("'"):
                    value = token[3:-3] if triple else token[1:-1]
                else:
                    # TOML multiline basic strings trim continuation whitespace.
                    value = ast.literal_eval(re.sub(r"\\\r?\n[ \t\r\n]*", "", token))
                if triple and value.startswith("\n"):
                    value = value[1:]
            except (ValueError, SyntaxError):
                raise PinError(f"unsupported Cargo string while checking archive adoption: {relative}")
            following = text[match.end():].lstrip()
            quoted_key = value if following.startswith(("=", ".")) else None
            if quoted_key is not None or assignment not in {"path", "members", "default-members", "build", "workspace"}:
                continue
            candidate = (path.parent / value).resolve()
            if any(char in value for char in "*?["):
                inspect_cargo_pattern(path.parent.resolve(), value, root.resolve(), boundary.resolve())
            # Case folding is a conservative overapproximation on case-sensitive
            # filesystems and also catches ordinary macOS case aliases.
            normalized = str(candidate).casefold()
            if str(boundary.resolve()).casefold() == normalized or any(
                str(boundary.resolve()).casefold() == str(p).casefold() for p in candidate.parents
            ) or any(
                fnmatch.fnmatchcase(str(target).casefold(), normalized) for target in destinations
            ):
                raise PinError(f"Cargo manifest adopts the archived pin boundary: {relative}")


def validated_stage(root: Path, proposed: Path, edits: Dict[str, str]) -> Path:
    stage = proposed.resolve()
    source = root.resolve()
    if physically_within(stage, source):
        raise PinError("staging directory must be outside the source tree")
    for relative in edits:
        destination = (stage / relative).resolve()
        if stage not in destination.parents:
            raise PinError(f"staged destination escapes its directory: {relative}")
        if physically_within(destination, source):
            raise PinError(f"staged destination enters the source tree: {relative}")
        if destination.exists() or destination.is_symlink():
            raise PinError(f"staged output must be fresh: {relative}")
    return stage


def write_staged_output(destination: Path, text: str) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    try:
        with destination.open("x", encoding="utf-8") as output:
            output.write(text)
    except OSError as error:
        raise PinError(f"cannot exclusively create staged output {destination}: {error}") from error


def is_archived_pin_input(root: Path, relpath: str) -> bool:
    expected = ARCHIVED_PIN_INPUT_SHA256.get(relpath)
    if expected is None:
        return False
    path = root / relpath
    cursor = root
    for part in Path(relpath).parts:
        cursor /= part
        if cursor.is_symlink():
            raise PinError(f"archived pin input is redirected by a symlink: {relpath}")
    try:
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError as error:
        raise PinError(f"cannot read archived pin input {relpath}: {error}") from error
    if actual != expected:
        raise PinError(f"archived pin input content changed: {relpath}")
    return True


def undeclared_pin_sites(root: Path, dep: str) -> List[Tuple[str, int, str]]:
    """Tracked build inputs that pin ``dep`` but are NOT declared legs.

    The leg table is a WHITELIST, and a whitelist alone cannot notice a pin
    added somewhere it does not list. Every channel inherits that blind spot:
    the census iterates ``LEGS``, the Rust guard ``include_str!``s a fixed file
    set, and the bump script verifies with this same census. (``--locked`` was
    blind here too until the root ``[patch]`` was deleted on 2026-08-19 —
    while it stood, it collapsed every clean.git revision to one path dep and
    the lock recorded no revision at all.) A stray ``rev = "..."`` in some
    other manifest is therefore a real, silently-stale extra leg — and the
    bump script would still print "across every leg" over it.

    This is the complement: assert that the only places a pin appears are the
    places we declared. Returns ``(relpath, lineno, line)`` for each offender.
    """

    declared = {leg.relpath for leg in LEGS[dep]}
    url_plain = (CLEAN_URL if dep == "clean" else AY_URL).replace("\\", "")
    sha_anywhere = re.compile(r"[0-9a-f]{40}")

    listing = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z"],
        capture_output=True,
    )
    if listing.returncode != 0:
        # Not a git checkout (synthetic fixture trees, exported snapshots).
        # There is no tracked-file set to take a complement against, so this
        # audit is INAPPLICABLE rather than passing. Signalled distinctly so
        # the caller reports "not audited" instead of "clean" — the whole point
        # of this check is that a silent pass is indistinguishable from a real
        # one.
        raise NotAGitCheckout(str(root))

    offenders: List[Tuple[str, int, str]] = []
    tracked = [raw.decode("utf-8", "surrogateescape") for raw in listing.stdout.split(b"\0") if raw]
    validate_archived_pin_boundary(root, tracked)
    for raw in listing.stdout.split(b"\0"):
        if not raw:
            continue
        relpath = raw.decode("utf-8", "surrogateescape")
        if relpath in declared or not relpath.endswith(PIN_BEARING_SUFFIXES):
            continue
        if is_archived_pin_input(root, relpath):
            continue
        try:
            text = (root / relpath).read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        if url_plain not in text:
            continue
        for lineno, line in enumerate(text.splitlines(), start=1):
            if url_plain in line and sha_anywhere.search(line):
                offenders.append((relpath, lineno, line.strip()))
    return offenders



def clean_authority_versions(manifest: str, ay_revision: str) -> Tuple[str, str]:
    """Return (Clean, AY) versions certified by an immutable Clean manifest.

    Clean's root manifest is the coordinated transaction authority: its
    ``workspace.package.version`` is the version every Clean member publishes,
    and exactly seven ``workspace.dependencies`` entries co-own both AY's
    revision and package version. Narrow TOML-section parsing avoids accepting
    commented or similarly-spelled rows, while cardinality remains fail-closed.
    """

    if not SHA_RE.fullmatch(ay_revision):
        raise PinError(f"not a 40-hex AY commit sha: {ay_revision!r}")
    # TrustIR's supported bootstrap Python is 3.9, before stdlib ``tomllib``.
    # Parse only the two deliberately narrow TOML surfaces we authorize. A
    # multiline/aliased/reformatted declaration fails closed and requires a
    # review of this parser, just like a changed pin-leg regex.
    section = ""
    workspace_versions: List[str] = []
    ay_entries: List[Tuple[str, str, str]] = []

    def without_comment(line: str) -> str:
        quoted = False
        escaped = False
        for index, character in enumerate(line):
            if escaped:
                escaped = False
            elif character == "\\" and quoted:
                escaped = True
            elif character == '"':
                quoted = not quoted
            elif character == "#" and not quoted:
                return line[:index]
        return line

    def field(name: str, line: str) -> Optional[re.Match[str]]:
        return re.search(rf'(?:^|[,{{])\s*{name}\s*=\s*"([^"]+)"', line)
    for raw_line in manifest.splitlines():
        line = without_comment(raw_line).strip()
        if not line:
            continue
        section_match = re.fullmatch(r"\[([^]]+)\]", line)
        if section_match:
            section = section_match.group(1).strip()
            continue
        if section == "workspace.package":
            version_match = re.fullmatch(r'version\s*=\s*"([^"]+)"', line)
            if version_match:
                workspace_versions.append(version_match.group(1))
        elif section == "workspace.dependencies":
            git_match = field("git", line)
            if git_match is None or git_match.group(1) != AY_REMOTE:
                continue
            rev_match = field("rev", line)
            version_match = field("version", line)
            if rev_match is None or version_match is None:
                raise PinError(
                    "target Clean AY dependency declaration must carry one-line "
                    f"git/version/rev authority: {raw_line.strip()}"
                )
            ay_entries.append(
                (
                    line.split("=", 1)[0].strip(),
                    rev_match.group(1),
                    version_match.group(1),
                )
            )

    if len(workspace_versions) != 1:
        raise PinError(
            "target Clean Cargo.toml must contain exactly one direct "
            "workspace.package.version declaration; found "
            f"{len(workspace_versions)}"
        )
    clean_version = workspace_versions[0]
    if not SEMVER_RE.fullmatch(clean_version):
        raise PinError(
            "target Clean workspace.package.version is not a canonical semantic "
            f"version: {clean_version!r}"
        )
    if len(ay_entries) != 7:
        raise PinError(
            f"found {len(ay_entries)} ay.git declarations in target Clean "
            "Cargo.toml; expected exactly 7"
        )

    revisions = {revision for _, revision, _ in ay_entries}
    if revisions != {ay_revision}:
        rendered = ", ".join(sorted(repr(value) for value in revisions))
        raise PinError(
            "target Clean Cargo.toml does not co-own the exact coordinated AY "
            f"revision {ay_revision}; found {rendered}"
        )

    ay_versions = {version for _, _, version in ay_entries}
    if len(ay_versions) != 1:
        rendered = ", ".join(sorted(repr(value) for value in ay_versions))
        raise PinError(
            "target Clean Cargo.toml has split AY package versions across its "
            f"seven declarations: {rendered}"
        )
    ay_version = next(iter(ay_versions))
    if not SEMVER_RE.fullmatch(ay_version):
        raise PinError(
            "target Clean AY package version is not a canonical semantic "
            f"version: {ay_version!r}"
        )
    return clean_version, ay_version


def plan_version_edits(
    read: Reader, dep: str, new_version: str
) -> Dict[str, str]:
    """Return exact-count-anchored package-version rewrites for ``dep``."""

    if not SEMVER_RE.fullmatch(new_version):
        raise PinError(f"not a canonical semantic version: {new_version!r}")
    edits: Dict[str, str] = {}
    for leg in VERSION_LEGS[dep]:
        text = read(leg.relpath)
        rewritten, count = substitute_version(text, leg, new_version)
        violation = check_version_count(leg, count)
        if violation is not None:
            raise PinError(f"{leg.relpath}: {violation}")
        edits[leg.relpath] = rewritten
    return edits


def plan_edits(
    read: Reader,
    dep: str,
    new_sha: str,
    new_version: Optional[str] = None,
) -> Dict[str, str]:
    """Return {relpath: rewritten text} for every rewritable leg.

    Raises PinError if any leg's match count disagrees with its declaration.
    """

    if not SHA_RE.match(new_sha):
        raise PinError(f"not a 40-hex commit sha: {new_sha!r}")
    edits: Dict[str, str] = {}
    for leg in LEGS[dep]:
        if not leg.rewritable:
            continue
        text = read(leg.relpath)
        rewritten, count = substitute(text, leg, new_sha)
        violation = check_count(leg, count)
        if violation is not None:
            raise PinError(f"{leg.relpath}: {violation}")
        edits[leg.relpath] = rewritten
    if new_version is not None:
        def overlay_read(relpath: str) -> str:
            return edits.get(relpath, read(relpath))

        edits.update(plan_version_edits(overlay_read, dep, new_version))
    return edits


def plan_clean_ay_edits(
    read: Reader,
    clean_sha: str,
    ay_sha: str,
    clean_version: Optional[str] = None,
    ay_version: Optional[str] = None,
) -> Dict[str, str]:
    """Return one coherent staged tree for a coordinated Clean + AY move.

    The two leg sets overlap in ``dependency_pin_coherence.rs``.  Planning
    them independently and copying both stage directories would make the last
    copy silently restore the first dependency's old constant.  Apply the AY
    rewrite through an overlay containing the already-planned Clean edits so
    the shared file carries both new revisions.
    """

    edits = plan_edits(read, "clean", clean_sha, clean_version)

    def overlay_read(relpath: str) -> str:
        return edits.get(relpath, read(relpath))

    edits.update(plan_edits(overlay_read, "ay", ay_sha, ay_version))
    return edits


# --------------------------------------------------------------------------
# I/O
# --------------------------------------------------------------------------

def repo_reader(root: Path) -> Reader:
    def read(relpath: str) -> str:
        path = root / relpath
        try:
            # Lock checks must see original CR/LF bytes like Rust include_str!,
            # rather than universal-newline normalization hiding a bare CR.
            if path.name == "Cargo.lock":
                with path.open(encoding="utf-8", newline="") as stream:
                    return stream.read()
            return path.read_text(encoding="utf-8")
        except OSError as error:
            raise PinError(f"{relpath}: cannot read pin leg: {error}") from error

    return read


def _add_common(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="repository root (defaults to this script's parent repository)",
    )
    parser.add_argument(
        "--dep",
        required=True,
        choices=sorted(LEGS),
        help="which dependency pin to operate on",
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)

    census_parser = sub.add_parser(
        "census", help="report every leg's revision; exit 1 unless all agree"
    )
    _add_common(census_parser)

    current_parser = sub.add_parser(
        "current", help="print the single current revision; exit 1 if split"
    )
    _add_common(current_parser)

    version_current_parser = sub.add_parser(
        "version-current",
        help="print the single current package version; exit 1 if split",
    )
    _add_common(version_current_parser)

    static_guard_parser = sub.add_parser(
        "static-guard",
        help=(
            "run the toolchain-free mirror of dependency_pin_coherence.rs "
            "(every assertion but the frontend-lock resolve)"
        ),
    )
    static_guard_parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="repository root (defaults to this script's parent repository)",
    )
    integrity_parser = sub.add_parser("integrity", help="refuse fatal input/complement errors before staging")
    integrity_parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)

    legs_parser = sub.add_parser(
        "legs", help="print this dependency's leg paths, one per line"
    )
    _add_common(legs_parser)
    legs_parser.add_argument(
        "--rewritable-only",
        action="store_true",
        help="omit the lockfiles, which cargo refreshes rather than this script",
    )

    version_legs_parser = sub.add_parser(
        "version-legs", help="print package-version leg paths, one per line"
    )
    _add_common(version_legs_parser)

    authority_parser = sub.add_parser(
        "clean-authority",
        help="validate an immutable Clean Cargo.toml and print Clean/AY versions",
    )
    authority_parser.add_argument("--manifest", required=True, type=Path)
    authority_parser.add_argument("--ay-revision", required=True)

    apply_parser = sub.add_parser(
        "apply", help="stage rewritten legs into --stage-dir (never touches --root)"
    )
    _add_common(apply_parser)
    apply_parser.add_argument("--to", required=True, help="target 40-hex revision")
    apply_parser.add_argument(
        "--version-to",
        default=None,
        help="reviewed target package version (exact canonical semver)",
    )
    apply_parser.add_argument(
        "--from",
        dest="from_rev",
        default=None,
        help="expected current revision; refuse if the tree disagrees",
    )
    apply_parser.add_argument(
        "--stage-dir", required=True, type=Path, help="directory to write into"
    )

    pair_parser = sub.add_parser(
        "apply-clean-ay",
        help=(
            "stage a coordinated Clean + AY rewrite into --stage-dir; needed "
            "because the two leg sets share the coherence guard"
        ),
    )
    pair_parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    pair_parser.add_argument("--clean-to", required=True, help="target Clean revision")
    pair_parser.add_argument("--ay-to", required=True, help="target AY revision")
    pair_parser.add_argument(
        "--clean-version-to",
        default=None,
        help="reviewed target Clean package version",
    )
    pair_parser.add_argument(
        "--ay-version-to",
        default=None,
        help="reviewed target AY package version",
    )
    pair_parser.add_argument(
        "--stage-dir", required=True, type=Path, help="directory to write into"
    )

    args = parser.parse_args(argv)
    root = args.root.resolve() if hasattr(args, "root") else None
    read = repo_reader(root) if root is not None else None

    try:
        if args.command == "integrity":
            for dependency in LEGS:
                try:
                    rogue = undeclared_pin_sites(Path(args.root), dependency)
                except NotAGitCheckout:
                    print("(not audited) pin integrity complement needs a Git checkout")
                    return 0
                if rogue:
                    raise PinError(f"undeclared {dependency} pin site: {rogue[0][0]}")
            print("PIN INPUT INTEGRITY: PASS")
            return 0
        if args.command == "census":
            assert read is not None
            report = census(read, args.dep)
            print(report.render())
            if not report.coherent:
                print(
                    f"\nINCOHERENT: {args.dep} pin is split across "
                    f"{len(report.distinct)} revision(s) or a leg lost its pin.\n"
                    "Fix with: scripts/bump-dep-pin.sh "
                    f"{args.dep} <40-hex-sha>",
                    file=sys.stderr,
                )
                return 1
            try:
                rogue = undeclared_pin_sites(Path(args.root), args.dep)
            except NotAGitCheckout as exc:
                print(
                    f"  (not audited) undeclared-pin-site check needs a git "
                    f"checkout; {exc} is not one",
                    file=sys.stderr,
                )
                rogue = []
            if rogue:
                print(
                    f"\nUNDECLARED PIN SITE(S): {len(rogue)} tracked build input(s) "
                    f"pin {args.dep} but are not declared legs, so nothing moves "
                    "them and nothing checks them:",
                    file=sys.stderr,
                )
                for relpath, lineno, line in rogue:
                    print(f"    {relpath}:{lineno}: {line}", file=sys.stderr)
                print(
                    "\nEither remove the pin, or add the file to the leg table in "
                    "scripts/pin_rewrite.py AND to the inventory assertions in\n"
                    "crates/trust-ir/tests/dependency_pin_coherence.rs — together.",
                    file=sys.stderr,
                )
                return 1
            versions = version_census(read, args.dep)
            print()
            print(versions.render())
            if not versions.coherent:
                print(
                    f"\nSPLIT PACKAGE VERSION: {args.dep} is declared at "
                    f"{len(versions.distinct)} different versions "
                    f"({', '.join(sorted(versions.distinct)) or '<none>'}).",
                    file=sys.stderr,
                )
                print(
                    "\nThe revision and package version are separate atomic legs. "
                    "Repair them with bump-dep-pin.sh and its explicit "
                    "--clean-version/--ay-version confirmation.",
                    file=sys.stderr,
                )
                return 1
            print(
                f"\nCOHERENT: every {args.dep} leg pins {report.current()} "
                f"at package version {versions.current()}"
            )
            return 0

        if args.command == "legs":
            for leg in LEGS[args.dep]:
                if args.rewritable_only and not leg.rewritable:
                    continue
                print(leg.relpath)
            return 0

        if args.command == "version-legs":
            for leg in VERSION_LEGS[args.dep]:
                print(leg.relpath)
            return 0

        if args.command == "clean-authority":
            try:
                manifest = args.manifest.read_text(encoding="utf-8")
            except OSError as error:
                raise PinError(
                    f"cannot read target Clean manifest {args.manifest}: {error}"
                ) from error
            clean_version, ay_version = clean_authority_versions(
                manifest, args.ay_revision
            )
            print(f"clean={clean_version}")
            print(f"ay={ay_version}")
            return 0

        if args.command == "current":
            assert read is not None
            report = census(read, args.dep)
            if not report.coherent:
                print(report.render(), file=sys.stderr)
                return 1
            print(report.current())
            return 0

        if args.command == "version-current":
            assert read is not None
            report = version_census(read, args.dep)
            if not report.coherent:
                print(report.render(), file=sys.stderr)
                return 1
            print(report.current())
            return 0

        if args.command == "static-guard":
            assert read is not None
            report = static_guard(read)
            print(report.render(), file=sys.stderr if not report.coherent else sys.stdout)
            return 0 if report.coherent else 1

        if args.command == "apply":
            assert read is not None
            if not SHA_RE.match(args.to):
                print(
                    f"--to must be a full 40-hex commit sha, got {args.to!r}",
                    file=sys.stderr,
                )
                return 2
            if args.from_rev is not None:
                report = census(read, args.dep)
                if not report.coherent or report.current() != args.from_rev:
                    print(report.render(), file=sys.stderr)
                    print(
                        f"--from {args.from_rev} does not match the tree",
                        file=sys.stderr,
                    )
                    return 1
            if args.version_to is not None and not SEMVER_RE.fullmatch(args.version_to):
                print(
                    "--version-to must be an exact canonical semantic version, "
                    f"got {args.version_to!r}",
                    file=sys.stderr,
                )
                return 2
            edits = plan_edits(read, args.dep, args.to, args.version_to)
            stage = validated_stage(Path(args.root), args.stage_dir, edits)
            for relpath, text in sorted(edits.items()):
                destination = stage / relpath
                write_staged_output(destination, text)
                print(relpath)
            return 0

        if args.command == "apply-clean-ay":
            assert read is not None
            for label, revision in (("--clean-to", args.clean_to), ("--ay-to", args.ay_to)):
                if not SHA_RE.match(revision):
                    print(
                        f"{label} must be a full 40-hex commit sha, got {revision!r}",
                        file=sys.stderr,
                    )
                    return 2
            for label, version in (
                ("--clean-version-to", args.clean_version_to),
                ("--ay-version-to", args.ay_version_to),
            ):
                if version is not None and not SEMVER_RE.fullmatch(version):
                    print(
                        f"{label} must be an exact canonical semantic version, "
                        f"got {version!r}",
                        file=sys.stderr,
                    )
                    return 2
            edits = plan_clean_ay_edits(
                read,
                args.clean_to,
                args.ay_to,
                args.clean_version_to,
                args.ay_version_to,
            )
            stage = validated_stage(Path(args.root), args.stage_dir, edits)
            for relpath, staged_text in sorted(edits.items()):
                destination = stage / relpath
                write_staged_output(destination, staged_text)
                print(relpath)
            return 0
    except PinError as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1

    parser.error(f"unhandled command {args.command!r}")
    return 2  # pragma: no cover - argparse exits


if __name__ == "__main__":
    raise SystemExit(main())
