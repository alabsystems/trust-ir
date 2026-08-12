#!/usr/bin/env python3
"""Declarative leg table for the Clean / AY dependency pins, plus a rewriter.

A pin move is an ATOMIC transaction across every leg listed below.  Moving
fewer than all of them leaves `main` red, and the failure is invisible to
`cargo check` because the only enforcement is a TEST
(`crates/trust-ir/tests/dependency_pin_coherence.rs`).  That is exactly how a
partial move shipped three times.

This module is the machine-readable statement of "which files hold the pin".
It never mutates the repository: `apply` writes candidates into a staging
directory and `scripts/bump-dep-pin.sh` owns the install/rollback transaction.

Every leg carries an ANCHORED regex plus an exact expected match count, so a
reformatted manifest fails CLOSED (count mismatch) rather than silently
rewriting nothing.  Per-constant anchoring is also what keeps `CLEAN_REVISION`
and `AY_REVISION` independent inside the one file that holds both -- a global
string replace is only accidentally correct while the two SHAs differ.

NOTE FOR MAINTAINERS: the expected counts here duplicate the inventory the
guard test asserts (`assert_exact_manifest_pins(.., 1)` / `(.., 3)`).  Adding a
fourth `clean-*` dependency to trust-ir-build means updating BOTH.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, List, Optional, Sequence, Tuple

Reader = Callable[[str], str]


SHA_RE = re.compile(r"^[0-9a-f]{40}$")

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
        note="clean-kernel + clean-mathverse + clean-olean",
        expected=3,
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
            "root lock -- normally ZERO clean rows, because the root [patch] "
            "rewrites clean.git to ../clean path deps and path deps emit no "
            "`source =` line. Any row that DOES appear must match."
        ),
        rewritable=False,
        minimum=0,
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

REMOTES: Dict[str, str] = {"clean": CLEAN_REMOTE, "ay": AY_REMOTE}

# Legs that live outside this repository and therefore cannot be rewritten or
# audited by `census`.  bump-dep-pin.sh checks them as preconditions.
EXTERNAL_LEGS: Dict[str, str] = {
    "clean": (
        "../clean working tree MUST be checked out AT the rev -- the root "
        "[patch] is a PATH dep, so cargo compiles the sibling's working tree, "
        "not the pinned revision."
    ),
    "ay": (
        "../clean/Cargo.toml CO-OWNS the AY pin (7 declarations). If it "
        "disagrees the root lock carries two ay graphs and the guard fails; "
        "move ../clean first. trust-ir cannot bump ay alone."
    ),
}


class PinError(Exception):
    """A leg could not be read or rewritten as declared."""


class NotAGitCheckout(Exception):
    """The undeclared-pin-site audit needs a tracked-file set and has none."""


# --------------------------------------------------------------------------
# Pure helpers (no I/O) -- the unit-testable core.
# --------------------------------------------------------------------------


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


#: Build inputs a pin can actually take effect from. Deliberately narrow —
#: docs, ledgers and design notes quote revisions in prose and must not trip
#: the complement check, but anything cargo reads must.
PIN_BEARING_SUFFIXES = (".toml", ".lock", ".rs")


def undeclared_pin_sites(root: Path, dep: str) -> List[Tuple[str, int, str]]:
    """Tracked build inputs that pin ``dep`` but are NOT declared legs.

    The leg table is a WHITELIST, and a whitelist alone cannot notice a pin
    added somewhere it does not list. Every channel inherits that blind spot:
    the census iterates ``LEGS``, the Rust guard ``include_str!``s a fixed file
    set, the bump script verifies with this same census, and ``--locked``
    cannot see it either because the root ``[patch]`` collapses every clean.git
    revision to one path dep. A stray ``rev = "..."`` in some other manifest is
    therefore a real, silently-stale seventh leg — and the bump script would
    still print "across every leg" over it.

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
    for raw in listing.stdout.split(b"\0"):
        if not raw:
            continue
        relpath = raw.decode("utf-8", "surrogateescape")
        if relpath in declared or not relpath.endswith(PIN_BEARING_SUFFIXES):
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



def declared_versions(root: Path, dep: str) -> List[Tuple[str, int, str]]:
    """Every `version = "X"` paired with this dependency's git URL, by file.

    The rev and the package VERSION are separate legs that move together: a
    rev bump can carry a semver bump (clean 1.2.0 -> 1.3.0 across
    76a7508e -> 88f9c2c3), and the lockfile then resolves a version the
    manifests do not declare. `bump-dep-pin.sh` rewrites revs only -- correctly,
    since a version change is shape drift that must be reviewed -- so without
    this check the census reports COHERENT while the guard test fails on the
    version. Returns (relpath, lineno, version).
    """

    url_plain = (CLEAN_URL if dep == "clean" else AY_URL).replace("\\", "")
    version_re = re.compile(r'version = "([^"]+)"')
    found: List[Tuple[str, int, str]] = []
    for leg in LEGS[dep]:
        if not leg.rewritable or leg.relpath.endswith(".rs"):
            continue
        try:
            text = (root / leg.relpath).read_text(encoding="utf-8")
        except OSError:
            continue
        for lineno, line in enumerate(text.splitlines(), start=1):
            if url_plain not in line or line.lstrip().startswith("#"):
                continue
            m = version_re.search(line)
            if m:
                found.append((leg.relpath, lineno, m.group(1)))
    return found


def plan_edits(read: Reader, dep: str, new_sha: str) -> Dict[str, str]:
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
    return edits


# --------------------------------------------------------------------------
# I/O
# --------------------------------------------------------------------------

def repo_reader(root: Path) -> Reader:
    def read(relpath: str) -> str:
        path = root / relpath
        try:
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

    legs_parser = sub.add_parser(
        "legs", help="print this dependency's leg paths, one per line"
    )
    _add_common(legs_parser)
    legs_parser.add_argument(
        "--rewritable-only",
        action="store_true",
        help="omit the lockfiles, which cargo refreshes rather than this script",
    )

    apply_parser = sub.add_parser(
        "apply", help="stage rewritten legs into --stage-dir (never touches --root)"
    )
    _add_common(apply_parser)
    apply_parser.add_argument("--to", required=True, help="target 40-hex revision")
    apply_parser.add_argument(
        "--from",
        dest="from_rev",
        default=None,
        help="expected current revision; refuse if the tree disagrees",
    )
    apply_parser.add_argument(
        "--stage-dir", required=True, type=Path, help="directory to write into"
    )

    args = parser.parse_args(argv)
    root = args.root.resolve()
    read = repo_reader(root)

    try:
        if args.command == "census":
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
            versions = declared_versions(Path(args.root), args.dep)
            distinct_versions = {v for _, _, v in versions}
            if len(distinct_versions) > 1:
                print(
                    f"\nSPLIT PACKAGE VERSION: {args.dep} is declared at "
                    f"{len(distinct_versions)} different versions "
                    f"({', '.join(sorted(distinct_versions))}):",
                    file=sys.stderr,
                )
                for relpath, lineno, v in versions:
                    print(f"    {relpath}:{lineno}: version = \"{v}\"", file=sys.stderr)
                print(
                    "\nThe revision and the package version are separate legs. A rev bump "
                    "can carry a semver bump;\nbump-dep-pin.sh moves revs only, so the "
                    "version must be moved deliberately (and the guard test's\n"
                    "CLEAN_VERSION / AY_VERSION with it).",
                    file=sys.stderr,
                )
                return 1
            print(f"\nCOHERENT: every {args.dep} leg pins {report.current()}")
            return 0

        if args.command == "legs":
            for leg in LEGS[args.dep]:
                if args.rewritable_only and not leg.rewritable:
                    continue
                print(leg.relpath)
            return 0

        if args.command == "current":
            report = census(read, args.dep)
            if not report.coherent:
                print(report.render(), file=sys.stderr)
                return 1
            print(report.current())
            return 0

        if args.command == "apply":
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
            edits = plan_edits(read, args.dep, args.to)
            stage = args.stage_dir.resolve()
            for relpath, text in sorted(edits.items()):
                destination = stage / relpath
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_text(text, encoding="utf-8")
                print(relpath)
            return 0
    except PinError as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1

    parser.error(f"unhandled command {args.command!r}")
    return 2  # pragma: no cover - argparse exits


if __name__ == "__main__":
    raise SystemExit(main())
