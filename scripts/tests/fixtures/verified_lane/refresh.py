#!/usr/bin/env python3
"""Regenerate the gate-13 run fixtures from a REAL kept run of the lane.

    python3 scripts/verified_contracts.py --keep            # the real runs
    python3 scripts/tests/fixtures/verified_lane/refresh.py target/verified-lane <mutant-name>
    python3 scripts/tests/fixtures/verified_lane/refresh.py --build-executions target/verified-lane <mutant-name>
    python3 scripts/tests/fixtures/verified_lane/refresh.py --retained-report <report.json>

writes `laws_base_run.json` (the base run), `laws_mutant_run.json` (the named
mutant run) and `build_executions.json` (both runs' build-script executions)
next to this file; `--build-executions` writes only the last. Each is a
PROJECTION of what the gate
read — never an invented run: the report's primary-unit rows with every field
`verified_contracts.not_judged` / `check_rows` reads, the primary unit's
rustflags that carry the budget and memory ceiling, the terminal lines the
gate parses (`gate_lines`), the exit status and the process-tree RSS bound
from the run's `.lane.json`. Paths, session ids and certificate bytes are dropped (the
fixtures are exported with `scripts/`, and a local path is not content).

`build_executions.json` holds what `verified_contracts.check_build_scripts`
reads of each run — its `build-execution-scope` rows and its inventory's
`run-custom-build` units — and the root's workspace version. The tests overlay
it on the run fixture it names. It is its own file because the run fixtures
above predate that projection: it was first written (`--build-executions`) from
a later run than theirs, and its `provenance` says which. A full refresh
writes all three from one run.

The provenance's `tree` and `workspace_version` are read from THIS checkout,
so a projection is refused (`provenance_refusals`) unless the kept run is
one this checkout made (the run directory inside it) and the checkout has no
change outside this directory: then they name the tree the run built,
provided the run was made at the current commit (run the gate and this
script back to back). The first `build_executions.json` was projected from
another worktree's run and so recorded a tree it never ran.

`budget_rows.json` is not regenerated here: it holds rows measured once on
the installed lane with the r7 false-refutation repro crate, and records how
in its own `provenance`.

`--retained-report` prints a report-only projection, with the SHA-256 of the
original bytes and the compiler identities that report records. It claims no
checkout revision, terminal transcript, RSS reading or lane qualification.
`schema4_c6_report.json` is such a projection of the retained failing C6 run;
it keeps all 1,116 rows, including their stable transport keys and grades.
"""

from __future__ import annotations

import json
import hashlib
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "scripts"))

import verified_contracts as vc  # noqa: E402

PATH = re.compile(r"(?:/Users|/home|/private|/tmp|/var)/[^\s\"'`)]+")
# A path package's id keeps its `#<version>` fragment; only the path goes.
PACKAGE_PATH = re.compile(r"path\+file://[^#\"]*")
KEPT_FLAGS = ("trust-verify-level", "trust-verify-timeout-ms", "trust-verify-function-budget-ms",
              "trust-verify-effort", "trust-verify-worker-threads", vc.MEMORY_CEILING_OPTION, "trust-policy")


def scrub(text: str) -> str:
    return PATH.sub("<path>", PACKAGE_PATH.sub("path+file://<path>", text))


def slim_row(ob: dict) -> dict:
    outcome = ob.get("outcome") or {}
    strength = outcome.get("strength") or {}
    slim_outcome = {"status": outcome.get("status")}
    for key in ("reason", "timeout_ms", "detail", "note"):
        if key in outcome:
            slim_outcome[key] = scrub(str(outcome[key])) if isinstance(outcome[key], str) else outcome[key]
    if strength:
        slim_outcome["strength"] = {
            "assurance": strength.get("assurance"),
            "grade": {"validation": (strength.get("grade") or {}).get("validation")},
        }
    row = {k: ob[k] for k in ("obligation_id", "kind", "solver") if k in ob}
    row["description"] = scrub(str(ob.get("description", "")))
    row["outcome"] = slim_outcome
    transport = ob.get("transport_evidence") or {}
    evidence = {k: transport[k] for k in ("typed_kind", "identity") if k in transport}
    if evidence:
        row["transport_evidence"] = json.loads(scrub(json.dumps(evidence)))
    return row


def slim_flags(flags: list) -> list:
    out = []
    for i, flag in enumerate(flags):
        if flag == "-Z" and i + 1 < len(flags) and flags[i + 1].split("=", 1)[0] in KEPT_FLAGS:
            out += ["-Z", flags[i + 1]]
    return out


def slim_report(data: dict) -> dict:
    functions = []
    for entry in data.get("functions", []):
        full = entry.get("function", "")
        if ")::" not in full:
            continue
        prefix, name = full.split(")::", 1)
        if f'package="{vc.CRATE}"' not in prefix or 'proof_unit_role="primary"' not in prefix:
            continue
        functions.append({
            "function": f'cargo-target(package="{vc.CRATE}",proof_unit_role="primary")::{name}',
            "summary": {"verdict": (entry.get("summary") or {}).get("verdict")},
            "obligations": [slim_row(ob) for ob in entry.get("obligations", [])],
        })
    roots = ((data.get("cargo_proof_inventory") or {}).get("completed") or {}).get("primary_roots") or []
    return {
        "verification_gate": data.get("verification_gate"),
        "cargo_proof_inventory": {"completed": {"primary_roots": [
            {"semantics": {"unit_rustflags": slim_flags((r.get("semantics") or {}).get("unit_rustflags") or [])}}
            for r in roots
        ]}},
        "functions": functions,
    }


def slim_build_executions(data: dict) -> dict:
    """What `check_build_scripts` reads of one report: its
    `build-execution-scope` rows and its inventory's `run-custom-build` units
    (placed in `excluded_active_units`, where every measured run lists them)."""
    return {
        "assumptions": [
            {key: scrub(str(row[key])) for key in ("scope", "subject", "tag", "source") if key in row}
            for row in data.get("assumptions") or [] if row.get("tag") == vc.BUILD_EXECUTION_TAG
        ],
        "excluded_active_units": [
            {key: scrub(u[key]) if isinstance(u[key], str) else u[key]
             for key in ("package_id", "package_name", "target_name", "proof_unit_index", "proof_unit_mode",
                         "exclusion_reason") if key in u}
            for u in vc.inventory_units(data) if u.get("proof_unit_mode") == vc.BUILD_EXECUTION_MODE
        ],
    }


def retained_report(raw: bytes) -> dict:
    """An attributed projection; never borrow THIS checkout's provenance."""
    data = json.loads(raw)
    roots = ((data.get("cargo_proof_inventory") or {}).get("completed") or {}).get("primary_roots") or []
    return {
        "provenance": {
            "scope": "report compatibility controls only; not proof or lane qualification",
            "report_sha256": hashlib.sha256(raw).hexdigest(),
            "compiler_commits": sorted({
                r["semantics"]["compiler"]["rustc_commit_hash"] for r in roots
            }),
            "projection": "scripts/tests/fixtures/verified_lane/refresh.py --retained-report",
        },
        "report": slim_report(data),
    }


def gate_lines(output: str) -> list:
    """The lines the gate parses, in order: verdict, `refuted obligation`,
    trustc memory notes, budget-stop diagnostics, the publication boundary,
    and each omitted-request list (its header and every entry line)."""
    omitted = {line for found in vc.omitted_lists(output) for line in (found.header, *found.entries)}
    keep = []
    for line in output.splitlines():
        if (vc.VERDICT_LINE.match(line) or vc.REFUTED_LINE.search(line) or vc.MEMORY_MENTION.search(line)
                or vc.BUDGET_STOP_MENTION.search(line) or line.startswith("Publication boundary:")
                or line in omitted):
            keep.append(scrub(line))
    return keep


def fixture(report: Path, log: Path, lane: Path, provenance: dict) -> dict:
    run = json.loads(lane.read_text(encoding="utf-8"))
    return {
        "provenance": provenance,
        "exit": run["exit"],
        "rss_bound_bytes": run["rss_bound_bytes"],
        "output_lines": gate_lines(log.read_text(encoding="utf-8")),
        "report": slim_report(json.loads(report.read_text(encoding="utf-8"))),
    }


def provenance_refusals(out: Path, root: Path, status: str) -> list:
    """Every reason a projection of the kept run under `out` would record a
    provenance it did not have: the `tree` and `workspace_version` are read
    from the checkout at `root`, so the run must be that checkout's (`out`
    inside `root`) and the checkout clean outside this fixture directory
    (`status` is its `git status --porcelain` output)."""
    refusals = []
    out, root = out.resolve(), root.resolve()
    if root != out and root not in out.parents:
        refusals.append(
            f"{out} is not inside this checkout ({root}): the provenance would name this checkout's "
            "tree, not the one that ran; project a run of this checkout (its target/verified-lane)"
        )
    here = HERE.resolve().relative_to(root).as_posix() + "/" if root in HERE.resolve().parents else None
    dirty = [line for line in status.splitlines() if line.strip() and not (here and line[3:].startswith(here))]
    if dirty:
        refusals.append(
            "the checkout has uncommitted changes outside the fixture directory, so its HEAD is not the "
            "tree the run built: " + "; ".join(dirty[:5]) + (f" (+{len(dirty) - 5} more)" if len(dirty) > 5 else "")
        )
    return refusals


def main(argv: list) -> int:
    if len(argv) == 3 and argv[1] == "--retained-report":
        print(json.dumps(retained_report(Path(argv[2]).read_bytes()), indent=1, sort_keys=True))
        return 0
    only_executions = len(argv) > 1 and argv[1] == "--build-executions"
    if only_executions:
        argv = argv[:1] + argv[2:]
    if len(argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    out, mutant = Path(argv[1]), argv[2]
    names = {m.name: m for m in vc.MUTANTS}
    if mutant not in names:
        raise SystemExit(f"unknown mutant {mutant!r}")
    import datetime
    import subprocess

    status = subprocess.run(["git", "-C", str(ROOT), "status", "--porcelain"], capture_output=True, text=True,
                            check=True).stdout
    refusals = provenance_refusals(out, ROOT, status)
    if refusals:
        raise SystemExit("\n".join(f"refresh.py: refused: {r}" for r in refusals))
    commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True, text=True,
                            check=True).stdout.strip()
    common = {
        "gate": "scripts/verified_contracts.py (gate 13), a real kept run (--keep)",
        "regenerate": "scripts/tests/fixtures/verified_lane/refresh.py",
        "toolchain": vc.toolchain_identity(vc.resolve_targo()),
        "tree": commit,
        "date": datetime.date.today().isoformat(),
    }
    reports = {
        "laws_base_run.json": ("base", out / "base" / "report.json"),
        "laws_mutant_run.json": (f"mutant {mutant}", out / "mutants" / f"{mutant}.report" / "report.json"),
    }
    executions = {
        "provenance": {**common, "runs": {name: run for name, (run, _) in reports.items()},
                       "workspace_version": vc.workspace_version(ROOT)},
        **{name: slim_build_executions(json.loads(report.read_text(encoding="utf-8")))
           for name, (_, report) in reports.items()},
    }
    docs = [("build_executions.json", executions)]
    if not only_executions:
        base = fixture(reports["laws_base_run.json"][1], out / "base.log", out / "base.lane.json",
                       {**common, "run": "base"})
        mut = fixture(reports["laws_mutant_run.json"][1], out / "mutants" / f"{mutant}.log",
                      out / "mutants" / f"{mutant}.lane.json",
                      {**common, "run": f"mutant {mutant}",
                       # the EXPANDED flips (a `flips` entry may be a glob), as the gate judges them
                       "flips": vc.expand_flips(names[mutant], vc.law_functions(ROOT))})
        docs += [("laws_base_run.json", base), ("laws_mutant_run.json", mut)]
    for name, doc in docs:
        (HERE / name).write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n", encoding="utf-8")
        print(f"wrote {HERE / name}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
