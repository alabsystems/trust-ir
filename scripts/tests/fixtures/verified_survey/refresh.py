#!/usr/bin/env python3
"""Regenerate the gate-15 fixtures from REAL kept runs of the verified survey.

    python3 scripts/verified_survey.py                       # a real survey (kept under target/)
    python3 scripts/tests/fixtures/verified_survey/refresh.py target/verified-survey/survey <crate>[=<name>]...

writes, per named crate, `<name>.ndjson`, `<name>.log` and `<name>.lane.json`
next to this file (`<name>` defaults to the crate; a run of a scratch tree
with planted code gets a name that says so): a PROJECTION of what the survey read,
never an invented run. The ndjson keeps every record of the primary unit's
functions with every row field `verified_survey.judge_crate` and
`verified_contracts.row_budget_attribution` read (site, kind, status, reason,
strength, solver, typed kind, description), the header fields the memory
rule reads (the primary unit's rustflags), and a footer whose count and
digest are RECOMPUTED over the slim records with the seal's algorithm
(`verified_survey.records_digest`) — the real footers were checked by the
runs themselves, where a mismatch is NOT JUDGED. A reason is cut at CUT
characters unless it carries a refutation or a demotion (the seal's
`refuted obligation` text sits past character 400), which is kept whole. The
log keeps the terminal lines the judge parses. Paths are scrubbed (the
fixtures ship with scripts/).

planted-panics.* (2026-09-30): a scratch copy of the tree at 8bcd939f with
`fn planted_unwrap(x: Option<u32>) -> u32 { x.unwrap() }` and
`fn planted_unreachable(x: usize) -> usize { if x == 7 { unreachable!() } x }`
added to trust-ir-fmt's main.rs and called from `main`, surveyed with
`--crates trust-ir-fmt`: JUDGED, and all three refutations published only as
demoted `unknown` rows.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "scripts"))

import verified_contracts as vc  # noqa: E402
import verified_survey as vs  # noqa: E402

PATH = re.compile(r"(?:/Users|/home|/private|/tmp|/var)/[^\s\"'`)]+")
KEPT_FLAGS = ("trust-verify-level", "trust-verify-timeout-ms", "trust-verify-function-budget-ms",
              vc.MEMORY_CEILING_OPTION, "trust-policy")
LOG_LINES = re.compile(
    r"memory|exceeded its per-function budget|^Publication boundary:|native verifier status:|"
    r"^(Summary|Gate|Coverage):"
)
CUT = 400


def scrub(value):
    if isinstance(value, str):
        return PATH.sub("<path>", value)
    if isinstance(value, list):
        return [scrub(v) for v in value]
    if isinstance(value, dict):
        return {k: scrub(v) for k, v in value.items()}
    return value


def slim_row(ob: dict) -> dict:
    outcome = ob.get("outcome") or {}
    slim = {"status": outcome.get("status")}
    whole = vs.refutation_route(ob) is not None or "refutation demoted" in str(outcome.get("reason") or "")
    for key in ("reason", "timeout_ms", "detail", "note"):
        if key in outcome:
            value = outcome[key]
            slim[key] = (scrub(value) if whole else scrub(value)[:CUT]) if isinstance(value, str) else value
    strength = outcome.get("strength") or {}
    if strength:
        slim["strength"] = {
            "assurance": strength.get("assurance"),
            "grade": {"validation": (strength.get("grade") or {}).get("validation")},
        }
    row = {k: ob[k] for k in ("obligation_id", "kind", "solver", "location") if k in ob}
    row["description"] = scrub(str(ob.get("description", "")))[:CUT]
    row["outcome"] = slim
    typed = (ob.get("transport_evidence") or {}).get("typed_kind")
    if typed is not None:
        row["transport_evidence"] = {"typed_kind": scrub(typed)}
    return row


def slim_header(header: dict) -> dict:
    roots = ((header.get("cargo_proof_inventory") or {}).get("completed") or {}).get("primary_roots") or []
    slim_roots = []
    for root in roots:
        flags = [str(f) for f in ((root.get("semantics") or {}).get("unit_rustflags") or [])]
        kept = []
        for i, flag in enumerate(flags):
            if flag == "-Z" and i + 1 < len(flags) and flags[i + 1].split("=", 1)[0] in KEPT_FLAGS:
                kept += ["-Z", flags[i + 1]]
        slim_roots.append({"semantics": {"unit_rustflags": kept}})
    return {
        "record_type": "header",
        "schema": header.get("schema"),
        "expected_functions": None,  # set once the kept records are counted
        "cargo_proof_inventory": {"completed": {"primary_roots": slim_roots}},
    }


def project(out: Path, crate: str, name: str) -> None:
    header = None
    functions = []
    with (out / crate / vs.REPORT).open("rb") as handle:
        for kind, value in vs.iter_stream(handle):
            if kind == "header":
                header = slim_header(value)
            elif kind == "function" and vc.primary_function(str(value.get("function", "")), crate):
                functions.append(
                    {
                        "record_type": "function",
                        "function": scrub(value["function"]),
                        "obligations": [slim_row(ob) for ob in value.get("obligations") or []],
                    }
                )
            elif kind == "problem":
                raise SystemExit(f"{crate}: the kept report is not whole: {value}")
    if header is None:
        raise SystemExit(f"{crate}: no header")
    header["expected_functions"] = len(functions)
    lines = [json.dumps(f, sort_keys=True).encode() for f in functions]
    footer = {
        "record_type": "footer",
        "functions_emitted": len(functions),
        "function_records_sha256": vs.records_digest(lines, len(lines)),
    }
    body = b"\n".join([json.dumps(header, sort_keys=True).encode(), *lines, json.dumps(footer).encode()]) + b"\n"
    (HERE / f"{name}.ndjson").write_bytes(body)
    log = (out / f"{crate}.log").read_text(encoding="utf-8", errors="replace").splitlines()
    kept = []
    i = 0
    while i < len(log):
        line = log[i]
        if vc.OMITTED_MENTION.search(line):  # the whole list, as verified_contracts.omitted_lists reads it
            kept.append(scrub(line))
            i += 1
            while i < len(log) and log[i].startswith("  "):
                if log[i].startswith("  ["):
                    kept.append(scrub(log[i]))
                i += 1
            continue
        if LOG_LINES.search(line):
            kept.append(scrub(line)[:CUT])
        i += 1
    (HERE / f"{name}.log").write_text("\n".join(kept) + "\n", encoding="utf-8")
    lane = json.loads((out / f"{crate}.lane.json").read_text(encoding="utf-8"))
    (HERE / f"{name}.lane.json").write_text(
        json.dumps({k: lane.get(k) for k in ("exit", "rss_bound_bytes", "wall_s", "features")}, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"{name} ({crate}): {len(functions)} functions, {sum(len(f['obligations']) for f in functions)} rows, "
          f"{len(kept)} log lines")


def main(argv) -> int:
    if len(argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    out = Path(argv[1]).resolve()
    for spec in argv[2:]:
        crate, _, name = spec.partition("=")
        project(out, crate, name or crate)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
