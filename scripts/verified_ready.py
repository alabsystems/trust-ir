#!/usr/bin/env python3
"""The verified READY lane (gate 16 of scripts/ci_gates.sh, `verified-ready`).

Gate 15 (scripts/verified_survey.py) surveys every workspace member and is
opt-in; gate 13 (scripts/verified_contracts.py) is the --release contract lane
over the laws alone. This gate holds the members (and targets) whose advisory
run is ALREADY clean — zero refuted rows — to staying clean, and holds each to
a floor of PROVED rows so a regression that turns proofs into unknowns is seen.
The rows are the committed table scripts/gates/verified-ready.tsv:

    crate <TAB> target (lib|bins) <TAB> floor <TAB> why

WHAT IT RUNS, per row, one after another, in the DEBUG profile (gate 15's
profile), with CARGO_TARGET_DIR=<root>/target/verified-ready-build, nothing in
RUSTFLAGS (the root `[trust]` table is the budget) and `-j N`, N sized to the
host when the gate starts by scripts/host_scale.py (cores, available memory,
the share and heavy child the rows took here; TRUST_IR_TARGO_JOBS and a
positive CARGO_BUILD_JOBS cap it; a host without room waits, then refuses):

    targo trust check --allow-l0-gaps --locked -p <crate> --<target> \\
        --report-dir <out>/<crate>.<target>/<crate>

The build tree is cleared first, as gate 15 does (a `targo trust check` run
never reuses a kept dependency build; it only grows).

WHAT IT GATES, per row — every condition, none of them advisory:
  * targo exits 0 (gate 15 ignores the exit; a READY row's clean run exits 0);
  * the run is JUDGED by gate 15's reader (verified_survey.judge_kept, which is
    gate 13's THE RULE: peak RSS below the recorded ceiling, no budget- or
    resource-attributable row, no budget stop, a whole report stream, no
    unexplained omitted request). A NOT JUDGED run FAILS here: its proved rows
    are not evidence, so the floor cannot be met by it;
  * the report's own `verification_gate`: decision is not `fail` and
    `counts.failed` is 0;
  * no REFUTATION in the crate's primary unit (gate 15's `refutation_route`:
    a `failed` row, or a native refutation the seal publishes as `unknown`).
    There is no ledger here: a READY row has none. The one class gate 15
    admits on gate 13's verdict — a demoted law postcondition of
    crates/trust-ir-laws/src/laws.rs — is admitted the same way and counted
    apart, never as proved;
  * PROVED rows of the primary unit >= the row's floor. Only `proved` counts:
    unknown, timeout, runtime-checked, assumed and mandated rows never do.

The floors are measured, not aspirational: about 80% of a measured run's
proved rows, rounded down (scripts/gates/verified-ready.tsv says when). Proved
totals move with load (gate 15's docstring: the seal's budget trips), so a
floor below the measured count is slack against that motion, not a claim.
Raise a floor when a measured run sustains more; lower one only with a commit
that names the Trust change that moved it.

A PASS says: these targets carry no refuted row and at least this many proved
rows on this tree and toolchain. It does NOT say they are verified: their
unknown rows are reported and stay unproved.

Exit 0 PASS, 1 FAIL, 2 could not run (no targo, RUSTFLAGS set, bad table).

Usage:
  verified_ready.py [--root DIR] [--out DIR] [--rows crate.target,...]
  verified_ready.py --check-rows        # the table alone, toolchain-free
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Sequence, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
import host_scale as hs  # noqa: E402
import verified_contracts as vc  # noqa: E402  -- THE one report reader and THE RULE
import verified_survey as vs  # noqa: E402  -- gate 15's per-crate judge

ROWS = Path("scripts") / "gates" / "verified-ready.tsv"
TARGET = Path("target") / "verified-ready-build"
REPORTS = Path("target") / "verified-ready" / "reports"
HEADER = ("crate", "target", "floor", "why")
TARGETS = ("lib", "bins")
CRATE_NAME = re.compile(r"^[a-z][a-z0-9_-]*$")


@dataclass(frozen=True)
class Row:
    crate: str
    target: str
    floor: int
    why: str
    line: int

    @property
    def key(self) -> str:
        return f"{self.crate}.{self.target}"


def parse_rows(text: str) -> Tuple[List[Row], List[str]]:
    """The table: `#` comments and blank lines skipped, then the header, then
    one row per (crate, target). A floor must be a positive integer — a floor
    of 0 holds nothing, so it is refused, not read as "no floor"."""
    rows: List[Row] = []
    errors: List[str] = []
    header_seen = False
    seen = set()
    for n, raw in enumerate(text.splitlines(), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        cells = raw.split("\t")
        if not header_seen:
            if tuple(cells) != HEADER:
                errors.append(f"line {n}: the first non-comment line must be the header {'<TAB>'.join(HEADER)}")
                return rows, errors
            header_seen = True
            continue
        if len(cells) != len(HEADER):
            errors.append(f"line {n}: {len(cells)} column(s), want {len(HEADER)}")
            continue
        crate, target, floor, why = (c.strip() for c in cells)
        if not CRATE_NAME.match(crate):
            errors.append(f"line {n}: `{crate}` is not a crate name")
            continue
        if target not in TARGETS:
            errors.append(f"line {n}: target `{target}` is not one of {', '.join(TARGETS)}")
            continue
        if not floor.isdigit() or int(floor) < 1:
            errors.append(f"line {n}: floor `{floor}` is not a positive integer (a 0 floor holds nothing)")
            continue
        if not why:
            errors.append(f"line {n}: the `why` column is empty (say when and how the floor was measured)")
            continue
        if (crate, target) in seen:
            errors.append(f"line {n}: duplicate row {crate}.{target}")
            continue
        seen.add((crate, target))
        rows.append(Row(crate, target, int(floor), why, n))
    if not header_seen:
        errors.append("no header line")
    elif not rows:
        errors.append("no rows: an empty READY lane gates nothing")
    return rows, errors


def rows_against_tree(root: Path, rows: Sequence[Row]) -> List[str]:
    """Toolchain-free: each row names a crate of `crates/` by its package name."""
    errors: List[str] = []
    for row in rows:
        manifest = root / "crates" / row.crate / "Cargo.toml"
        if not manifest.is_file():
            errors.append(f"line {row.line}: no crates/{row.crate}/Cargo.toml")
            continue
        text = manifest.read_text(encoding="utf-8")
        if not re.search(rf'(?m)^name\s*=\s*"{re.escape(row.crate)}"\s*$', text):
            errors.append(f"line {row.line}: crates/{row.crate}/Cargo.toml does not name package `{row.crate}`")
    return errors


def load_rows(root: Path) -> Tuple[List[Row], List[str]]:
    path = root / ROWS
    if not path.is_file():
        return [], [f"{ROWS} is missing"]
    rows, errors = parse_rows(path.read_text(encoding="utf-8"))
    return rows, errors + rows_against_tree(root, rows)


@dataclass
class RowVerdict:
    row: Row
    failures: List[str]
    proved: int
    unknown: int
    gate_counts: dict
    laws_admitted: int

    @property
    def passed(self) -> bool:
        return not self.failures


def judge_row(row: Row, result: "vs.CrateResult", gate: Optional[dict]) -> RowVerdict:
    """Every condition of the module docstring, over one run: `result` is gate
    15's judgment of the run, `gate` its report.json `verification_gate`
    (None when report.json is missing)."""
    failures: List[str] = []
    proved = result.statuses.get("proved", 0)
    unknown = result.statuses.get("unknown", 0) + result.statuses.get("timeout", 0)
    if not result.judged:
        failures.append(
            f"{row.key}: NOT JUDGED, so none of its proved rows is evidence and the floor cannot be met: "
            + " | ".join(r[len(vc.NOT_JUDGED):].strip()[:240] for r in result.reasons[:4])
        )
    if result.exit != 0:
        # A READY row's clean run exits 0 (measured: every clean run did; the
        # advisory lane exits 1 exactly when its gate decides `fail`). Gate 15
        # ignores the exit; here a non-zero or missing exit is a failure on its
        # own, so a run that died after writing a report cannot pass on it.
        failures.append(f"{row.key}: targo exited {result.exit}, not 0")
    counts = {}
    if gate is None:
        failures.append(f"{row.key}: no report.json verification_gate")
    else:
        counts = dict(gate.get("counts") or {})
        if gate.get("decision") == "fail":
            failures.append(f"{row.key}: verification_gate decision is `fail`")
        if counts.get("failed", 0) != 0:
            failures.append(f"{row.key}: verification_gate counts.failed = {counts.get('failed')}")
    if result.statuses.get("failed", 0):
        failures.append(f"{row.key}: {result.statuses['failed']} failed row(s) in the primary unit")
    for f in result.refutations:
        failures.append(
            f"{row.key}: refutation ({f.route}) `{f.function}` {f.obligation} at {f.where}: {f.description}"
        )
    if proved < row.floor:
        failures.append(
            f"{row.key}: {proved} proved row(s), below the floor {row.floor} (unknown rows never count)"
        )
    return RowVerdict(row, failures, proved, unknown, counts, len(result.gate13_laws))


def run_row(targo: str, root: Path, out: Path, row: Row, jobs: Optional[str]) -> RowVerdict:
    row_out = out / row.key
    row_out.mkdir(parents=True, exist_ok=True)
    report_dir = row_out / row.crate
    extra = ["--allow-l0-gaps", "--locked", *(["-j", jobs] if jobs else []), "-p", row.crate, f"--{row.target}"]
    started = time.monotonic()
    run = vc.run_lane(targo, root, report_dir, root / TARGET, extra, release=False)
    report_dir = vc.retained_report_dir(run, report_dir)
    wall = time.monotonic() - started
    if run.code == 0 and run.rss_bound:
        heavy = run.rss_bound >> 20
        share = hs.share_of(run.tree_mb or 0, run.procs_at_peak or 0, run.largest_mb or 0, heavy)
        hs.record("verified-ready", share, heavy, run.tree_mb or 0, run.procs_at_peak or 0)
    vc.record_run(row_out / row.crate, run)
    lane = {"exit": run.code, "rss_bound_bytes": run.rss_bound, "wall_s": round(wall, 1), "features": [],
            "args": extra}
    if run.report_dir is not None:
        lane["report_dir"] = run.report_dir
    (row_out / f"{row.crate}.lane.json").write_text(json.dumps(lane) + "\n", encoding="utf-8")
    result = vs.judge_kept(row_out, row.crate, root)
    gate = None
    report = report_dir / "report.json"
    if report.is_file():
        try:
            gate = json.loads(report.read_text(encoding="utf-8")).get("verification_gate")
        except (OSError, ValueError):
            gate = None
    return judge_row(row, result, gate)


def print_verdict(v: RowVerdict) -> None:
    c = v.gate_counts
    gate = ", ".join(f"{c.get(k, 0)} {k}" for k in ("proved", "failed", "unknown", "runtime_checked", "assumed",
                                                      "mandated", "total"))
    print(f"\n== {v.row.key}: {'PASS' if v.passed else 'FAIL'}; primary unit {v.proved} proved (floor "
          f"{v.row.floor}), {v.unknown} unknown/timeout (reported, never counted); report gate: {gate}")
    if v.laws_admitted:
        print(f"   {v.laws_admitted} demoted law postcondition(s) admitted on gate 13's verdict (not proved here)")
    for f in v.failures:
        print(f"   FAIL: {f}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=str(Path(__file__).resolve().parents[1]))
    ap.add_argument("--out", default=None, help=f"report directory (default <root>/{REPORTS.as_posix()})")
    ap.add_argument("--rows", default=None, help="comma-separated subset, as crate.target")
    ap.add_argument("--check-rows", action="store_true", help="parse the table and exit")
    args = ap.parse_args(argv)
    root = Path(args.root).resolve()
    out = Path(args.out).resolve() if args.out else root / REPORTS

    rows, errors = load_rows(root)
    if errors:
        for e in errors:
            print(f"FAIL: {ROWS}: {e}", file=sys.stderr)
        print(f"verified-ready: FAIL — the table does not parse ({len(errors)} error(s)); nothing was run",
              file=sys.stderr)
        return 2
    print(f"rows: {ROWS} — {', '.join(f'{r.key} (floor {r.floor})' for r in rows)}")
    if args.check_rows:
        print("verified-ready: table OK")
        return 0
    if args.rows is not None:
        wanted = [k for k in args.rows.split(",") if k]
        if not wanted:
            print("verified-ready: --rows names no row; an empty selection gates nothing", file=sys.stderr)
            return 2
        unknown = sorted(set(wanted) - {r.key for r in rows})
        if unknown:
            print(f"verified-ready: not rows of {ROWS}: {', '.join(unknown)}", file=sys.stderr)
            return 2
        rows = [r for r in rows if r.key in wanted]
    for key in ("RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS"):
        if key in os.environ:
            print(f"verified-ready: {key} is set; the lane takes its policy from the manifest only", file=sys.stderr)
            return 2
    try:
        cap_jobs = hs.caller_cap()
    except ValueError as e:
        print(f"verified-ready: {e}", file=sys.stderr)
        return 2
    # `-j` sized to the host now (scripts/host_scale.py): the cap is the
    # largest process-tree peak a row reached here; TRUST_IR_TARGO_JOBS (and a
    # positive CARGO_BUILD_JOBS) caps it. A host with no room waits for it, as
    # every other Targo leg does, then is refused.
    cap = hs.cap_for("verified-ready")
    plan, reading = hs.admit("verified-ready", cap, cap_jobs, hs.admission_wait_s())
    if plan is None:
        print("verified-ready: COULD NOT RUN: not even one child fits the memory available", file=sys.stderr)
        return 2
    print(hs.describe("verified-ready", reading, plan, cap.why, cap.reserve_mb))
    jobs = str(plan.jobs)
    try:
        targo = vc.resolve_targo()
    except SystemExit as e:
        print(f"verified-ready: could not run: {e}", file=sys.stderr)
        return 2
    print(f"verified ready lane: {targo}")
    print(f"toolchain: {vc.toolchain_identity(targo)}")
    cleared = vs.clear_build_tree(root / TARGET)
    if cleared is not None:
        print(f"cleared the previous run's build tree ({vs.gib(cleared)}): nothing in it is reused")
    started = time.monotonic()
    verdicts = []
    for row in rows:
        verdicts.append(run_row(targo, root, out, row, jobs))
        print_verdict(verdicts[-1])
        sys.stdout.flush()
    elapsed = time.monotonic() - started
    failed = [v for v in verdicts if not v.passed]
    print(f"\ncost: {elapsed:.0f} s wall; reports under {out}")
    if failed:
        print(f"verified-ready: FAIL — {len(failed)} of {len(verdicts)} row(s): "
              f"{', '.join(v.row.key for v in failed)}", file=sys.stderr)
        return 1
    print(f"verified-ready: PASS — {len(verdicts)} row(s) JUDGED with no refuted row and every proved floor met; "
          "their unknown rows stay unproved: no target is claimed verified")
    return 0


if __name__ == "__main__":
    sys.exit(main())
