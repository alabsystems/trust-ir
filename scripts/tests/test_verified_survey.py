"""Guards for the verified survey (scripts/verified_survey.py, gate 15).

The survey's claims are per crate and per row, so its bookkeeping is held
here without the Trust compiler: which crates are JUDGED (the same rule as
gate 13, read from real survey runs projected by
fixtures/verified_survey/refresh.py and from the measured stop rows of gate
13's fixtures), the report stream's integrity, the ledger's grammar (a `true`
class is refused; a `policy` row cites a decision of the closed table and
stays inside its kinds), what a refutation IS (a `failed` row or a native
refutation the seal demotes to `unknown` — read from a real run with planted
reachable panics — and never a "constructs" demotion), the one class admitted
on gate 13's verdict, the refutation identity (site + kind, never the
obligation id), and what the gate does with a new refutation, an unkeyable
one, and a ledger row whose refutation is missing.
"""

import contextlib
import copy
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import verified_contracts as vc  # noqa: E402
import verified_survey as vs  # noqa: E402

FIXTURES = Path(__file__).resolve().parent / "fixtures" / "verified_survey"
LANE_FIXTURES = Path(__file__).resolve().parent / "fixtures" / "verified_lane"
# Real survey runs (2026-09-29), projected: one JUDGED crate, one NOT JUDGED by
# a MemoryAdmission stop (trustd refused its socket for every function).
JUDGED = "supremacy-fixture"
ADMISSION = "raft-fixture"
# A real run of a scratch tree whose trust-ir-fmt carries a reachable
# `x.unwrap()` and `unreachable!()` (fixtures/verified_survey/refresh.py
# says how it was made): JUDGED, and every refutation published `unknown`.
PLANTED = "trust-ir-fmt"
PLANTED_FIXTURE = "planted-panics"
# A "constructs" demotion as the seal publishes it (trust-ir-giveback's
# `has_back_edge::{closure#0}`, R3, trustc 321aaeda7), cut after the demotion.
CONSTRUCTS_REASON = (
    "`#[trust(static)]` requires a static proof, but the solver returned unknown: native full verifier evidence "
    "status: Unsupported; native trust_mc TrustIr CHC/PDR transport solved obligation "
    "`trust_ir-native-trust-mc-request-1-proof-1` without a proof: native proof-grade evidence rejected: proof "
    "evidence rejected for ChcPdr: solver did not prove the obligation: fail-closed lowering reachable: 1 "
    "unsupported trust_ir construct(s) lowered to unconditional error rules; refutation demoted to unknown "
    "(constructs: AggregateProjection)"
)
R7_TRUST_IR_CENSUS = (
    "note: trust: memory census: 10604 bodies verified and compacted, 47 compacted slots recomputed, "
    "0 bodies skipped at the memory ceiling; resident 1.6 GiB, peak 4.2 GiB, ceiling 3.0 GiB"
)
LEDGER_HEADER = "\t".join(vs.LEDGER_HEADER)


def fixture_name(crate):
    return PLANTED_FIXTURE if crate == PLANTED else crate


def kept(crate):
    """(stream lines, terminal output, lane record) of a projected real run."""
    name = fixture_name(crate)
    lines = (FIXTURES / f"{name}.ndjson").read_bytes().splitlines(keepends=True)
    output = (FIXTURES / f"{name}.log").read_text(encoding="utf-8")
    lane = json.loads((FIXTURES / f"{name}.lane.json").read_text(encoding="utf-8"))
    return lines, output, lane


def records(crate):
    lines, _, _ = kept(crate)
    return [json.loads(line) for line in lines]


def restream(recs):
    """Serialize records as a report stream with a footer RECOMPUTED over the
    function records (what a whole, unmodified report looks like)."""
    header = copy.deepcopy(next(r for r in recs if r["record_type"] == "header"))
    functions = [r for r in recs if r["record_type"] == "function"]
    body = [json.dumps(f, sort_keys=True).encode() for f in functions]
    header["expected_functions"] = len(body)
    footer = {"record_type": "footer", "functions_emitted": len(body),
              "function_records_sha256": vs.records_digest(body, len(body))}
    return [json.dumps(header).encode() + b"\n", *(b + b"\n" for b in body), json.dumps(footer).encode() + b"\n"]


def judge(crate, recs=None, output=None, rss=None, base=None, root=None):
    """Judge `crate` over the kept run of `base` (default: the crate's own)."""
    lines, out, lane = kept(base or crate)
    if recs is not None:
        lines = restream(recs)
    return vs.judge_crate(crate, lines, out if output is None else output,
                          lane["rss_bound_bytes"] if rss is None else rss, root)


def with_row(recs, crate, row, function="planted::f"):
    recs = copy.deepcopy(recs)
    recs.insert(1, {
        "record_type": "function",
        "function": f'cargo-target(package="{crate}",proof_unit_role="primary")::{function}',
        "obligations": [copy.deepcopy(row)],
    })
    return recs


def failed_row(file="crates/x/src/lib.rs", span=(3, 4, 3, 9), kind="arithmetic_overflow_add", oid="vc:f:ovf:0"):
    return {
        "obligation_id": oid, "kind": kind, "solver": "ay-in-process", "description": "arithmetic overflow (Add)",
        "location": {"file": file, "line_start": span[0], "col_start": span[1], "line_end": span[2], "col_end": span[3]},
        "outcome": {"status": "failed"},
    }


def lane_budget_rows():
    return json.loads((LANE_FIXTURES / "budget_rows.json").read_text(encoding="utf-8"))["entries"]


class Judged(unittest.TestCase):
    def assert_not_judged(self, result, needle):
        self.assertFalse(result.judged, "expected NOT JUDGED")
        self.assertTrue(all(r.startswith(vc.NOT_JUDGED) for r in result.reasons), result.reasons)
        self.assertTrue(any(needle in r for r in result.reasons), (needle, result.reasons))

    def test_the_real_judged_run_is_judged(self):
        result = judge(JUDGED)
        self.assertEqual(result.reasons, [])
        self.assertTrue(result.judged)
        self.assertGreater(result.statuses["unknown"], 0, "unknown rows are reported, not a reason")

    def test_the_real_admission_stop_is_not_judged(self):
        # Measured: trustd refused its socket and EVERY function of the crate
        # was published as one synthetic MemoryAdmission row, under exit 0.
        result = judge(ADMISSION)
        self.assert_not_judged(result, "MemoryAdmission")
        self.assertEqual(result.statuses.get("proved", 0), 0)

    def test_every_measured_stop_row_makes_the_crate_not_judged(self):
        base = records(JUDGED)
        admission = next(
            ob for r in records(ADMISSION) if r["record_type"] == "function" for ob in r["obligations"]
        )
        rows = {name: e["row"] for name, e in lane_budget_rows().items() if "note" not in e}
        rows["memory_admission"] = admission
        rows["type_lowering_budget"] = {
            "kind": "unknown", "obligation_id": "vc:f:custom:0",
            "description": "unsupported MIR `Unsupported`: type lowering exceeded the per-function verification budget",
            "outcome": {"status": "unknown", "reason": "type lowering exceeded the per-function verification budget"},
        }
        rows["certification_skipped"] = {
            "kind": "unreachable", "obligation_id": "vc:f:assertion:0",
            "outcome": {"status": "unknown", "reason": "`#[trust(static)]` requires a static proof, but the solver "
                        f"returned unknown: {vc.PROVED_WITHOUT_AUTHORITY}"},
        }
        rows["proved_without_recheck"] = {
            "kind": "unreachable", "obligation_id": "vc:f:assertion:1",
            "outcome": {"status": "proved", "strength": {"assurance": "SmtBacked", "grade": {"validation": "Unrecorded"}}},
        }
        rows["native_timed_out"] = {
            "kind": "assertion", "obligation_id": "vc:f:assertion:2",
            "outcome": {"status": "unknown", "reason": "native full verifier evidence status: TimedOut; …"},
        }
        # The memory-ceiling gap row as crate trust-ir's report published it
        # (second survey run, 2026-09-29: 10,659 bodies, one row each): the
        # description names only the kind, so the REASON must carry it.
        rows["memory_ceiling_gap"] = {
            "kind": "assertion", "solver": "trust-native", "description": "assertion: native-verification-gap",
            "outcome": {"status": "unknown", "reason": "`#[trust(static)]` requires a static proof, but the solver "
                        "returned unknown: the function was not verified; resident memory 3.3 GiB had reached the "
                        "verification memory ceiling of 3.0 GiB"},
        }
        for name, row in rows.items():
            with self.subTest(name):
                self.assert_not_judged(judge(JUDGED, with_row(base, JUDGED, row)), "attributable")

    def test_a_word_in_a_name_or_a_description_is_not_a_stop(self):
        # Measured in the survey (2026-09-29): every description-only hit of
        # the classifier's words was spurious, and so were identifiers.
        advice = ("unbounded allocation in `Vec::with_capacity` (count `_3`): bulk allocation may reach or exceed "
                  "268435456 elements: bound the size (e.g. `#[requires(n < BOUND)]` or a dominating check) or "
                  "route it through a budget-checked allocator that fails closed")
        spurious = {
            "advice in the description": {"kind": "unbounded_allocation", "description": advice,
                                          "outcome": {"status": "unknown", "reason": "solver returned unknown"}},
            "refuted with the advice": {"kind": "unbounded_allocation", "description": advice,
                                        "outcome": {"status": "failed"}},
            "identifier with _budget": {"kind": "assertion", "outcome": {"status": "unknown", "reason":
                                        "native evidence trust-mc:trust-contracts:trust_ir_ay__bvblast__proof_budget:rustc-crate"}},
            "CamelCase variant": {"kind": "assertion", "outcome": {"status": "unknown", "reason":
                                  'VariantDef { name: "DeclarationBudgetExhausted", discriminant: 17 }'}},
            "rlimit inside WithOtherLimit": {"kind": "assertion", "outcome": {"status": "unknown", "reason":
                                             "callee <bincode::config::WithOtherLimit<X>>::new"}},
            "oom inside TooManyNodes": {"kind": "assertion", "outcome": {"status": "unknown", "reason":
                                        'VariantDef { name: "TooManyNodes", discriminant: 5 }'}},
            "a word in a code span": {"kind": "assertion", "outcome": {"status": "unknown", "reason":
                                      "call to absent callee `clean_kernel::budget::check` may panic"}},
        }
        for name, row in spurious.items():
            with self.subTest(name):
                self.assertIsNone(vc.row_budget_attribution(row))
        real = {"kind": "unknown", "outcome": {"status": "unknown", "reason":
                'unsupported type: Unsupported { tail: "type lowering exceeded the per-function verification budget" }'}}
        self.assertIn("`budget`", vc.row_budget_attribution(real))
        base = records(JUDGED)
        for row in spurious.values():
            with_advice = with_row(base, JUDGED, dict(row, location=failed_row()["location"]))
            self.assertTrue(judge(JUDGED, with_advice).judged)

    def test_a_structural_unknown_does_not_unjudge(self):
        # A survey is ABOUT unknown rows: only a stop unjudges. These are the
        # structural unknowns the real judged run carries.
        base = records(JUDGED)
        reasons = {ob["outcome"].get("reason", "") for r in base if r["record_type"] == "function"
                   for ob in r["obligations"] if ob["outcome"]["status"] == "unknown"}
        self.assertTrue(any("global-alloc dealloc" in x or "native full verifier" in x or "did not complete" in x
                            for x in reasons), reasons)
        self.assertTrue(judge(JUDGED, base).judged)

    def test_memory_at_the_ceiling_is_not_judged(self):
        _, output, lane = kept(JUDGED)
        ceiling = 3 << 30
        for peak in (ceiling, ceiling + 1, 5 << 30):
            with self.subTest(peak=peak):
                self.assert_not_judged(judge(JUDGED, rss=peak), "reached the verification memory ceiling")
        self.assertTrue(judge(JUDGED, rss=ceiling - 1).judged)
        self.assert_not_judged(judge(JUDGED, output=output + "\n" + R7_TRUST_IR_CENSUS), "trustc memory note")
        self.assertLess(lane["rss_bound_bytes"], ceiling)

    def test_the_memory_ceiling_gap_echo_is_named_and_counted_once(self):
        _, output, _ = kept(JUDGED)
        echo = ("  [UNKNOWN] [native-verification-gap] verification was not attempted: the process was over the "
                "verification memory ceiling (trust-native, 0ms)")
        result = judge(JUDGED, output="\n".join([output, echo, echo, echo]))
        self.assert_not_judged(result, "a body was not verified")
        self.assertEqual(sum("a body was not verified" in r for r in result.reasons), 1)
        self.assertTrue(any(r.endswith("(x3)") for r in result.reasons), result.reasons)

    def test_a_budget_stop_line_is_not_judged(self):
        _, output, _ = kept(JUDGED)
        line = lane_budget_rows()["strict_budget_build_error"]["diagnostic"].replace("error:", "warning:")
        self.assert_not_judged(judge(JUDGED, output=output + "\n" + line), "exceeded its per-function budget")

    def test_an_omitted_request_is_admitted_only_as_a_withheld_claim(self):
        _, output, _ = kept(JUDGED)
        prefix = f'cargo-target(package="{JUDGED}",proof_unit_role="primary")::supremacy_fixture::main'
        header = "Compiler requests omitted from the published proof rows: 1 (diagnostics only; not discharged by this report)"
        entry = f"  [PROVED; proof withheld at publication] function={prefix} obligation=vc:m:0 kind=assertion claim_sha256=ab"
        self.assertTrue(judge(JUDGED, output=f"{output}\n{header}\n{entry}").judged)
        unknown = entry.replace("[PROVED; proof withheld at publication]", "[UNKNOWN]")
        self.assert_not_judged(judge(JUDGED, output=f"{output}\n{header}\n{unknown}"), "omitted from the published rows")
        self.assert_not_judged(judge(JUDGED, output=f"{output}\n{header}\n{entry}\n{entry}"), "prints 1 request(s)")
        self.assert_not_judged(judge(JUDGED, output=f"{output}\n{header}\n  [garbled"), "unparsed omitted-request")
        # Another crate's omission is not this crate's.
        other = unknown.replace(f'package="{JUDGED}"', 'package="elsewhere"')
        self.assertTrue(judge(JUDGED, output=f"{output}\n{header}\n{other}").judged)

    def test_counts_and_coverage_are_never_read(self):
        recs = records(JUDGED)
        recs[0]["verification_gate"] = {"counts": {"proved": 0, "total": 1}, "coverage": {"coverage_complete": False}}
        self.assertTrue(judge(JUDGED, recs).judged)


class Stream(unittest.TestCase):
    def test_the_projected_stream_is_whole(self):
        lines, _, _ = kept(JUDGED)
        problems = [v for k, v in vs.iter_stream(lines) if k == "problem"]
        self.assertEqual(problems, [])

    def test_a_stream_that_is_not_whole_is_not_judged(self):
        lines, output, lane = kept(JUDGED)
        flipped = list(lines)
        flipped[1] = flipped[1].replace(b'"record_type": "function"', b'"record_type": "function", "x": 1', 1)
        header_moved = [lines[1], lines[0], *lines[2:]]
        cases = {
            "truncated": lines[:-1],
            "dropped record": [lines[0], *lines[2:]],
            "duplicated record": [lines[0], lines[1], *lines[1:]],
            "edited record": flipped,
            "no header": lines[1:],
            "header not first": header_moved,
            "record after footer": [*lines, lines[1]],
            "not json": [*lines[:-1], b"{nope\n", lines[-1]],
            "empty": [],
        }
        for name, stream in cases.items():
            with self.subTest(name):
                self.assertNotEqual(stream, lines)
                result = vs.judge_crate(JUDGED, stream, output, lane["rss_bound_bytes"])
                self.assertFalse(result.judged, name)
                self.assertTrue(any("report stream" in r or "no report header" in r for r in result.reasons), result.reasons)

    def test_the_digest_is_the_seals_length_prefixed_one(self):
        body = [b'{"a":1}', b'{"b":22}']
        import hashlib
        import struct
        h = hashlib.sha256(b"trust.report.ndjson.function-records.v2" + struct.pack(">Q", 2))
        for b in body:
            h.update(struct.pack(">Q", len(b)) + b)
        self.assertEqual(vs.records_digest(body, 2), "sha256:" + h.hexdigest())
        self.assertNotEqual(vs.records_digest(body, 3), vs.records_digest(body, 2), "the count is bound")
        self.assertNotEqual(vs.records_digest([b'{"a":1}{"b":22}'], 1), vs.records_digest(body, 2))


REPRO_LIB = (vs.REPRO / "src" / "lib.rs").as_posix()


def repro_span(needle):
    """(line, col_start, line, col_end) of `needle` in the repro source."""
    lines = (ROOT / REPRO_LIB).read_text(encoding="utf-8").splitlines()
    n = next(i for i, l in enumerate(lines, 1) if needle in l)
    col = lines[n - 1].index(needle)
    return (n, col, n, col + len(needle))


class Identity(unittest.TestCase):
    def site(self, row, function="r::widen_past_u64", crate="c"):
        return vs.site_of(crate, function, row, ROOT)

    def test_the_identity_reads_the_source_text_not_the_line(self):
        row = failed_row(file=REPRO_LIB, span=repro_span("i128::from(x) + 1"))
        site = self.site(row)
        self.assertEqual(site.text, "i128::from(x) + 1")
        self.assertEqual(site.ledger_prefix(), f"c\t{REPRO_LIB}\tr::widen_past_u64\tarithmetic_overflow_add\ti128::from(x) + 1")

    def test_neither_the_obligation_id_nor_the_description_is_identity(self):
        a = failed_row(file=REPRO_LIB, span=repro_span("i128::from(x) + 1"), oid="vc:f:custom:0")
        b = failed_row(file=REPRO_LIB, span=repro_span("i128::from(x) + 1"), oid="vc:f:assertion:panic-freedom:0")
        b["description"] = "reworded"
        self.assertEqual(self.site(a), self.site(b))

    def test_a_moved_line_keeps_its_identity(self):
        # Two spans with the same text in one function are one identity: an
        # unrelated edit above a refuted line does not un-ledger it.
        (n, c0, _, c1) = repro_span("i += 1")
        lines = (ROOT / REPRO_LIB).read_text(encoding="utf-8").splitlines()
        m = next(i for i, l in enumerate(lines, 1) if "i += 1" in l and i != n)
        c = lines[m - 1].index("i += 1")
        here = failed_row(file=REPRO_LIB, span=(n, c0, n, c1))
        there = failed_row(file=REPRO_LIB, span=(m, c, m, c + 6))
        self.assertEqual(self.site(here, "f"), self.site(there, "f"))

    def test_kind_function_text_file_and_crate_each_distinguish(self):
        row = failed_row(file=REPRO_LIB, span=repro_span("i128::from(x) + 1"))
        base = self.site(row)
        other_text = failed_row(file=REPRO_LIB, span=repro_span("digits[i] -= 1"))
        for other in (
            self.site(failed_row(file=REPRO_LIB, span=repro_span("i128::from(x) + 1"), kind="hardened_panic_boundary")),
            self.site(row, function="r::count_args"),
            self.site(other_text),
            self.site(row, crate="d"),
            vs.site_of("c", "r::widen_past_u64", failed_row(file="crates/x/src/lib.rs", span=repro_span("i128::from(x) + 1")), ROOT),
        ):
            self.assertNotEqual(base, other)

    def test_a_span_outside_the_tree_is_named_by_position(self):
        row = failed_row(file="/rustc/abc/library/core/src/num/mod.rs", span=(3, 4, 3, 9))
        self.assertEqual(vs.site_of("c", "f", row, ROOT).text, "@3:4-3:9")
        self.assertEqual(vs.site_of("c", "f", failed_row(), None).text, "@3:4-3:9")

    def test_an_incomplete_site_has_no_identity(self):
        for mutate in (
            lambda r: r.pop("location"),
            lambda r: r["location"].pop("col_end"),
            lambda r: r["location"].update(file=""),
            lambda r: r["location"].update(line_start="x"),
            lambda r: r.pop("kind"),
        ):
            row = failed_row()
            mutate(row)
            self.assertIsNone(vs.site_of("c", "f", row, ROOT))
        self.assertIsNone(vs.site_of("c", "", failed_row(), ROOT))

    def test_span_text_reads_zero_based_end_exclusive_columns(self):
        (n, c0, _, c1) = repro_span("i128::from(x) + 1")
        self.assertEqual(vs.span_text(ROOT, REPRO_LIB, f"{n}:{c0}-{n}:{c1}"), "i128::from(x) + 1")
        self.assertEqual(vs.span_text(ROOT, REPRO_LIB, f"{n}:{c0 + 1}-{n}:{c1}"), "128::from(x) + 1")
        self.assertIsNone(vs.span_text(ROOT, REPRO_LIB, f"{n}:{c0}-{n}:999"))
        self.assertIsNone(vs.span_text(ROOT, "no/such/file.rs", "1:0-1:1"))
        self.assertIsNone(vs.span_text(ROOT, "/etc/hosts", "1:0-1:1"))
        # A `#[path]` module is reported through `..` (conformance's
        # `src/../tests/generate.rs`): inside the tree it is read, outside not.
        climbing = REPRO_LIB.replace("/src/lib.rs", "/src/../src/lib.rs")
        self.assertEqual(vs.span_text(ROOT, climbing, f"{n}:{c0}-{n}:{c1}"), "i128::from(x) + 1")
        self.assertIsNone(vs.span_text(ROOT, "../" + REPRO_LIB, f"{n}:{c0}-{n}:{c1}"))
        self.assertIsNone(vs.span_text(ROOT, "core/src/panic.rs", "62:8-62:72"), "std is not in the tree")
        lines = (ROOT / REPRO_LIB).read_text(encoding="utf-8").splitlines()
        long = vs.span_text(ROOT, REPRO_LIB, f"1:0-{len(lines)}:0")
        self.assertEqual(len(long), vs.TEXT_MAX)
        self.assertTrue(long.endswith("…"))


def ledger_text(*rows):
    return "# comment\n" + LEDGER_HEADER + "\n" + "".join("\t".join(r) + "\n" for r in rows)


GOOD = ("c", REPRO_LIB, "r::widen_past_u64", "arithmetic_overflow_add", "i128::from(x) + 1", "1", "verifier-false",
        "shape d: i128::from(u64) is at most u64::MAX")


def with_count(row, n):
    return row[:5] + (str(n),) + row[6:]


class Ledger(unittest.TestCase):
    def test_the_committed_ledger_parses_and_reads_as_the_tree(self):
        rows, errors = vs.load_ledger(ROOT)
        self.assertEqual(errors, [])
        for row in rows.values():
            self.assertIn(row.klass, vs.CLASSES)

    def test_a_good_row_parses(self):
        rows, errors = vs.parse_ledger(ledger_text(GOOD))
        self.assertEqual(errors, [])
        (row,) = rows.values()
        self.assertEqual(row.site, vs.Site(*GOOD[:5]))
        self.assertEqual(vs.ledger_text_errors(ROOT, rows), [])

    def test_a_true_row_is_forbidden_by_name(self):
        bad = GOOD[:2] + ("r::other",) + GOOD[3:6] + ("true", "it really overflows")
        rows, errors = vs.parse_ledger(ledger_text(GOOD, bad))
        self.assertEqual(len(rows), 1)
        self.assertEqual(len(errors), 1)
        self.assertIn("class `true` is FORBIDDEN", errors[0])

    def test_every_malformed_row_is_an_error(self):
        cases = {
            "unknown class": GOOD[:6] + ("maybe", "x"),
            "no shape": GOOD[:7] + ("bounded by a slice length",),
            "unknown shape": GOOD[:7] + ("shape z: something",),
            "zero count": with_count(GOOD, 0),
            "non-numeric count": with_count(GOOD, "two"),
            "unnormalized text": GOOD[:4] + ("i128::from(x)  + 1",) + GOOD[5:],
            "blank column": GOOD[:4] + ("",) + GOOD[5:],
            "padded column": GOOD[:4] + (" x + 1",) + GOOD[5:],
            "too few columns": GOOD[:7],
        }
        for name, row in cases.items():
            with self.subTest(name):
                rows, errors = vs.parse_ledger(ledger_text(row))
                self.assertEqual(rows, {})
                self.assertEqual(len(errors), 1, errors)
        _, errors = vs.parse_ledger(ledger_text(GOOD, GOOD))
        self.assertIn("duplicate identity", " ".join(errors))
        _, errors = vs.parse_ledger("# only comments\n")
        self.assertIn("no header row", " ".join(errors))
        _, errors = vs.parse_ledger("crate\tfile\n")
        self.assertIn("the header must be", " ".join(errors))

    def test_a_policy_row_parses_without_a_shape(self):
        row = GOOD[:3] + ("unbounded_allocation", "Vec::with_capacity(v.len())", "1", "policy",
                          "d5db1e5d POLICY rows: sized from a resident collection")
        rows, errors = vs.parse_ledger(ledger_text(row))
        self.assertEqual(errors, [])
        self.assertEqual(len(rows), 1)

    def test_a_policy_row_is_held_to_a_recorded_decision_and_its_kinds(self):
        # Measured in review: a planted TRUE `x + 1` overflow ledgered as
        # `policy` passed --check-ledger and the re-judge. A policy cause now
        # cites a decision of the CLOSED table, inside that decision's kinds.
        overflow = GOOD[:6] + ("policy", "d5db1e5d POLICY rows: kept")
        cases = {
            "a kind the decision does not cover": (overflow, "covers only unbounded_allocation"),
            "an unrecorded decision": (
                GOOD[:3] + ("unbounded_allocation", "Vec::with_capacity(n)", "1", "policy", "0123abcd POLICY rows: x"),
                "begins with a recorded decision"),
            "no decision at all": (
                GOOD[:3] + ("unbounded_allocation", "Vec::with_capacity(n)", "1", "policy", "kept by decision"),
                "begins with a recorded decision"),
            "a decision without its rule": (
                GOOD[:3] + ("unbounded_allocation", "Vec::with_capacity(n)", "1", "policy", "d5db1e5d"),
                "begins with a recorded decision"),
        }
        for name, (row, needle) in cases.items():
            with self.subTest(name):
                rows, errors = vs.parse_ledger(ledger_text(row))
                self.assertEqual(rows, {})
                self.assertEqual(len(errors), 1, errors)
                self.assertIn(needle, errors[0])
        for decision, kinds in vs.POLICY_DECISIONS.items():
            self.assertRegex(decision, r"^[0-9a-f]{8}$")
            self.assertTrue(kinds)

    def test_a_row_whose_code_is_gone_is_an_error(self):
        gone = GOOD[:4] + ("i128::from(x) + 2",) + GOOD[5:]
        rows, _ = vs.parse_ledger(ledger_text(gone))
        self.assertIn("no longer occurs", " ".join(vs.ledger_text_errors(ROOT, rows)))
        elsewhere = GOOD[:1] + ("crates/nowhere.rs",) + GOOD[2:]
        rows, _ = vs.parse_ledger(ledger_text(elsewhere))
        self.assertIn("not in the tree", " ".join(vs.ledger_text_errors(ROOT, rows)))
        outside = GOOD[:1] + ("/rustc/x/core.rs",) + GOOD[2:4] + ("@3:4-3:9", "1", "verifier-false", "shape a: x")
        rows, _ = vs.parse_ledger(ledger_text(outside))
        self.assertEqual(vs.ledger_text_errors(ROOT, rows), [], "a position-named row is not text-checked")

    def test_the_checkable_half_of_a_shape_claim_is_checked(self):
        # shape d: the refuted text widens with `i128::from(`.
        not_d = GOOD[:2] + ("r::count_args", "hardened_panic_boundary", "i += 1", "1", "verifier-false", "shape d: x")
        rows, _ = vs.parse_ledger(ledger_text(not_d))
        self.assertIn("on a widening `<int>::from(..)`", " ".join(vs.ledger_text_errors(ROOT, rows)))
        widened = GOOD[:2] + ("r::past_u32", "hardened_panic_boundary", "u64::from(u32::MAX) + 1", "1",
                              "verifier-false", "shape d: 2^32")
        rows, _ = vs.parse_ledger(ledger_text(widened))
        self.assertEqual(vs.ledger_text_errors(ROOT, rows), [])
        # A SHIFT of a widened value is not shape d: the shift amount can
        # overflow (measured: conformance's varint reader over arbitrary bytes).
        for text, ok in (("i128::from(u64::MAX) + 1", True), ("u64::from(u32::MAX) * 2", True),
                         ("u64::from(byte & 0x7f) << (7 * width)", False), ("u64::from(x)", False)):
            self.assertEqual(bool(vs.WIDENING_ARITH.search(text)), ok, text)
        # shape c: the row's crate has no `unsafe` block, fn or impl.
        c_row = GOOD[:2] + ("r::boxed", "hardened_unsafe_operation", "Box::new(x)", "1", "verifier-false", "shape c: x")
        rows, _ = vs.parse_ledger(ledger_text(c_row))
        self.assertEqual(vs.ledger_text_errors(ROOT, rows), [], "the repro crate has no unsafe")
        with tempfile.TemporaryDirectory() as tmp:
            crate = Path(tmp) / "k"
            (crate / "src").mkdir(parents=True)
            (crate / "Cargo.toml").write_text("[package]\nname = \"k\"\n", encoding="utf-8")
            (crate / "src" / "lib.rs").write_text(
                "pub fn f(x: u64) -> Box<u64> { Box::new(x) }\n// unsafe { in a comment }\n", encoding="utf-8"
            )
            row = ("k", "k/src/lib.rs", "k::f", "hardened_unsafe_operation", "Box::new(x)", "1", "verifier-false", "shape c: x")
            rows, _ = vs.parse_ledger(ledger_text(row))
            self.assertEqual(vs.ledger_text_errors(Path(tmp), rows), [], "a comment is not an unsafe site")
            (crate / "tests").mkdir()
            (crate / "tests" / "t.rs").write_text("fn t() { unsafe { std::hint::unreachable_unchecked() } }\n", encoding="utf-8")
            self.assertEqual(vs.ledger_text_errors(Path(tmp), rows), [], "`check` does not compile tests/")
            (crate / "src" / "raw.rs").write_text("pub fn g(p: *const u8) -> u8 { unsafe { *p } }\n", encoding="utf-8")
            self.assertIn("the crate has `unsafe` at src/raw.rs:1", " ".join(vs.ledger_text_errors(Path(tmp), rows)))

    def test_every_shape_the_repro_claims_is_a_function_of_the_repro(self):
        source = (ROOT / REPRO_LIB).read_text(encoding="utf-8")
        for fn in ("count_args", "dec_first_nonzero", "reverse_indices", "widen_past_u64", "past_u32",
                   "next_after_checked", "last_index", "boxed", "width"):
            self.assertIn(f"pub fn {fn}(", source)
        self.assertEqual(sorted(vs.SHAPES), ["a", "b", "c", "d", "e"])
        manifest = (ROOT / vs.REPRO / "Cargo.toml").read_text(encoding="utf-8")
        self.assertIn("[workspace]", manifest, "a standalone workspace, never a member of the root one")
        root_manifest = (ROOT / "Cargo.toml").read_text(encoding="utf-8")
        self.assertNotIn("false_refutation_repro", root_manifest)


def demoted_rows():
    """The planted run's three refutations, as published: status `unknown`."""
    return [ob for r in records(PLANTED) if r["record_type"] == "function" for ob in r["obligations"]
            if vc.REFUTED_LINE.search(ob["outcome"].get("reason", ""))]


class Refutations(unittest.TestCase):
    def test_the_seal_publishes_a_native_refutation_as_unknown(self):
        rows = demoted_rows()
        self.assertEqual(len(rows), 3)
        for ob in rows:
            self.assertEqual(ob["outcome"]["status"], "unknown")
            self.assertIn("refutation demoted to unknown", ob["outcome"]["reason"])
            self.assertEqual(vs.refutation_route(ob), vs.DEMOTED)
        _, output, _ = kept(PLANTED)
        self.assertIn("0 failed", output, "the run's own summary counts none of them")

    def test_a_judged_crate_with_demoted_refutations_fails(self):
        result = judge(PLANTED)
        self.assertTrue(result.judged, result.reasons)
        self.assertEqual(result.statuses.get("failed", 0), 0, "a status-only reader sees nothing")
        self.assertEqual(sorted(f.function for f in result.refutations),
                         ["trust_ir_fmt::planted_unreachable", "trust_ir_fmt::planted_unwrap",
                          "trust_ir_fmt::planted_unwrap"])
        self.assertEqual({f.route for f in result.refutations}, {vs.DEMOTED})
        v = vs.gate([result], {}, [])
        self.assertFalse(v.passed)
        self.assertEqual(len(v.failures), 3, v.failures)
        self.assertTrue(all("(1 demoted)" in f for f in v.failures), v.failures)

    def test_a_ledgered_identity_admits_either_route(self):
        # Identity is the site, never the route: one span can come back
        # `failed` in one run and demoted in the next.
        result = judge(PLANTED)
        ledger = {}
        for f in result.refutations:
            ledger[f.site] = vs.LedgerRow(f.site, 1, "verifier-false", "shape a: x", 1)
        self.assertTrue(vs.gate([result], ledger, []).passed)

    def test_one_definition_with_gate_13(self):
        failed = failed_row()
        self.assertEqual(vs.refutation_route(failed), vs.REFUTED)
        for ob in demoted_rows():
            self.assertTrue(vc.REFUTED_LINE.search(ob["outcome"]["reason"]), "gate 13's evidence text")
        self.assertIsNone(vs.refutation_route({"outcome": {"status": "unknown", "reason": "solver returned unknown"}}))
        self.assertIsNone(vs.refutation_route({"outcome": {"status": "proved"}}))

    def test_a_constructs_demotion_is_not_a_refutation(self):
        # The lowering turned an unsupported construct into an unconditional
        # error rule: the solver's path to it says nothing about the program.
        row = {"kind": "assertion", "outcome": {"status": "unknown", "reason": CONSTRUCTS_REASON},
               "location": failed_row()["location"]}
        self.assertIsNone(vs.refutation_route(row))
        result = judge(JUDGED, with_row(records(JUDGED), JUDGED, row))
        self.assertTrue(result.judged, result.reasons)
        self.assertEqual(result.refutations, [])


class Gate13Laws(unittest.TestCase):
    """The one class admitted on another gate's verdict (`gate13_law`)."""

    def setUp(self):
        self.laws = vc.law_functions(ROOT)
        self.law = self.laws[0]
        self.demoted = copy.deepcopy(demoted_rows()[0])
        self.demoted.update(kind="postcondition", location={
            "file": vc.LAWS_FILE.as_posix(), "line_start": 1, "col_start": 0, "line_end": 1, "col_end": 2})

    def judge_row(self, row, crate=vc.CRATE, function=None, root=ROOT):
        function = function or f"{vc.CRATE_IDENT}::laws::{self.law}"
        return judge(crate, with_row(records(JUDGED), crate, row, function), base=JUDGED, root=root)

    def test_a_demoted_law_postcondition_is_admitted_as_gate_13s(self):
        result = self.judge_row(self.demoted)
        self.assertTrue(result.judged, result.reasons)
        self.assertEqual(result.gate13_laws, [self.law])
        self.assertEqual(result.refutations, [])
        self.assertTrue(vs.gate([result], {}, []).passed)

    def test_nothing_else_is_admitted(self):
        failed = dict(copy.deepcopy(self.demoted), outcome={"status": "failed"})
        other_kind = dict(copy.deepcopy(self.demoted), kind="assertion")
        other_file = copy.deepcopy(self.demoted)
        other_file["location"]["file"] = (vc.CRATE_DIR / "src" / "lib.rs").as_posix()
        cases = {
            "a failed row": dict(row=failed),
            "another kind": dict(row=other_kind),
            "another file": dict(row=other_file),
            "a function that is not a law": dict(row=self.demoted, function=f"{vc.CRATE_IDENT}::laws::not_a_law"),
            "a table, not a law": dict(row=self.demoted, function=f"{vc.CRATE_IDENT}::{self.law}"),
            "another crate": dict(row=self.demoted, crate=JUDGED),
            "no tree to read the laws from": dict(row=self.demoted, root=None),
        }
        for name, kw in cases.items():
            with self.subTest(name):
                crate = kw.get("crate", vc.CRATE)
                function = kw.get("function") or f"{vc.CRATE_IDENT}::laws::{self.law}"
                result = judge(crate, with_row(records(JUDGED), crate, kw["row"], function), base=JUDGED,
                               root=kw.get("root", ROOT))
                self.assertEqual(result.gate13_laws, [])
                self.assertEqual(len(result.refutations), 1)
                self.assertFalse(vs.gate([result], {}, []).passed)

    def test_each_condition_holds_on_its_own(self):
        # `gate13_laws` already yields no law outside gate 13's crate; the
        # row check refuses one too, so neither guard leans on the other.
        laws = frozenset(self.laws)
        function = f"{vc.CRATE_IDENT}::laws::{self.law}"
        self.assertEqual(vs.gate13_law(vc.CRATE, function, self.demoted, vs.DEMOTED, laws), self.law)
        self.assertIsNone(vs.gate13_law(JUDGED, function, self.demoted, vs.DEMOTED, laws))
        self.assertIsNone(vs.gate13_law(vc.CRATE, function, self.demoted, vs.REFUTED, laws))
        self.assertEqual(vs.gate13_laws(JUDGED, ROOT), frozenset())


def result(crate, sites=(), judged=True):
    r = vs.CrateResult(crate)
    if not judged:
        r.reasons.append(f"{vc.NOT_JUDGED} planted")
    for site in sites:
        r.refutations.append(vs.Refutation(site, "f", "vc:f:0", "d", "x.rs:1:0-1:1"))
    return r


class Gate(unittest.TestCase):
    def setUp(self):
        self.site = vs.Site(*GOOD[:5])
        self.ledger, errors = vs.parse_ledger(ledger_text(GOOD))
        self.assertEqual(errors, [])

    def test_a_ledgered_refutation_passes(self):
        v = vs.gate([result("c", [self.site])], self.ledger, [])
        self.assertTrue(v.passed)
        self.assertEqual(v.missing, [])

    def test_the_ledger_is_a_multiset(self):
        # Several checks can share one span and kind (measured: null,
        # validity, alignment and bounds of one deref). One more refuted row
        # than the ledger counts is a new refutation; fewer is missing.
        two, _ = vs.parse_ledger(ledger_text(with_count(GOOD, 2)))
        v = vs.gate([result("c", [self.site, self.site, self.site])], two, [])
        self.assertFalse(v.passed)
        self.assertIn("3 refuted row(s) (3 failed), the ledger admits 2", v.failures[0])
        v = vs.gate([result("c", [self.site, self.site])], two, [])
        self.assertTrue(v.passed)
        self.assertEqual(v.missing, [])
        v = vs.gate([result("c", [self.site])], two, [])
        self.assertTrue(v.passed)
        self.assertEqual(len(v.missing), 1)
        self.assertIn("1 of 2 refuted row(s) absent", v.missing[0])

    def test_a_new_refutation_fails_naming_its_ledger_line(self):
        new = vs.Site("c", REPRO_LIB, "r::count_args", "hardened_panic_boundary", "i += 1")
        v = vs.gate([result("c", [self.site, new])], self.ledger, [])
        self.assertFalse(v.passed)
        self.assertEqual(len(v.failures), 1)
        self.assertIn("NEW refutation c", v.failures[0])
        self.assertIn(new.ledger_prefix(), v.failures[0])

    def test_an_unkeyable_refutation_fails(self):
        v = vs.gate([result("c", [self.site, None])], self.ledger, [])
        self.assertFalse(v.passed)
        self.assertIn("carries no complete site", v.failures[0])

    def test_a_missing_expected_refutation_is_not_judged_never_a_pass_never_deleted(self):
        before = dict(self.ledger)
        v = vs.gate([result("c", [])], self.ledger, [])
        self.assertEqual(v.failures, [])
        self.assertEqual(len(v.missing), 1)
        self.assertIn("expected refutation missing — NOT JUDGED for that row", v.missing[0])
        self.assertEqual(self.ledger, before, "the gate never edits the ledger")
        # Rows of other crates are not this crate's business.
        self.assertEqual(vs.gate([result("d", [])], self.ledger, []).missing, [])

    def test_a_not_judged_crate_gates_nothing_either_way(self):
        new = vs.Site("c", REPRO_LIB, "r::count_args", "hardened_panic_boundary", "i += 1")
        v = vs.gate([result("c", [new, None], judged=False)], self.ledger, [])
        self.assertTrue(v.passed)
        self.assertEqual(v.missing, [], "an unjudged crate's absent refutation says nothing")
        self.assertEqual([r.crate for r in v.not_judged], ["c"])

    def test_a_ledger_error_fails(self):
        v = vs.gate([], {}, ["line 3: class `true` is FORBIDDEN"])
        self.assertFalse(v.passed)


class Main(unittest.TestCase):
    def run_main(self, argv):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = vs.main(argv)
        return code, out.getvalue() + err.getvalue()

    def kept_dir(self, tmp, crates):
        out = Path(tmp) / "survey"
        for crate in crates:
            name = fixture_name(crate)
            (out / crate).mkdir(parents=True)
            (out / crate / vs.REPORT).write_bytes((FIXTURES / f"{name}.ndjson").read_bytes())
            (out / f"{crate}.log").write_bytes((FIXTURES / f"{name}.log").read_bytes())
            (out / f"{crate}.lane.json").write_bytes((FIXTURES / f"{name}.lane.json").read_bytes())
        return out

    def fake_root(self, tmp, ledger):
        root = Path(tmp) / "root"
        (root / vs.LEDGER).parent.mkdir(parents=True)
        (root / vs.LEDGER).write_text(ledger, encoding="utf-8")
        return root

    def test_a_true_row_fails_before_anything_runs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.fake_root(tmp, ledger_text(GOOD[:6] + ("true", "it overflows")))
            with mock.patch.object(vc, "resolve_targo", side_effect=AssertionError("must not run")):
                code, text = self.run_main(["--root", str(root)])
        self.assertEqual(code, 1)
        self.assertIn("FORBIDDEN", text)
        self.assertIn("nothing was run", text)

    def test_a_stale_ledger_row_fails_the_ledger_check(self):
        row = ("c", "crates/nowhere/src/lib.rs") + GOOD[2:]
        with tempfile.TemporaryDirectory() as tmp:
            root = self.fake_root(tmp, ledger_text(row))
            code, text = self.run_main(["--root", str(root), "--check-ledger"])
        self.assertEqual(code, 1)
        self.assertIn("the file is not in the tree", text)

    def test_targos_exit_status_is_ignored(self):
        # The advisory lane exits 1 on any refutation and 0 on thousands of
        # unknowns: a judged crate stays judged whatever targo returned.
        with tempfile.TemporaryDirectory() as tmp:
            root = self.fake_root(tmp, ledger_text())
            out = self.kept_dir(tmp, [JUDGED])
            lane = json.loads((out / f"{JUDGED}.lane.json").read_text(encoding="utf-8"))
            for code_seen in (1, 101):
                lane["exit"] = code_seen
                (out / f"{JUDGED}.lane.json").write_text(json.dumps(lane), encoding="utf-8")
                self.assertTrue(vs.judge_kept(out, JUDGED).judged, code_seen)

    def test_rejudge_reads_the_retained_run_instead_of_the_old_logical_slot(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = self.kept_dir(tmp, [JUDGED])
            capture = Path(tmp) / "retained run"
            capture.mkdir()
            (capture / vs.REPORT).write_bytes((FIXTURES / f"{JUDGED}.ndjson").read_bytes())
            # A stale logical report is unusable, but it must not replace the
            # actual run's explicitly recorded stream.
            (out / JUDGED / vs.REPORT).write_bytes(b"not the current report\n")
            lane_path = out / f"{JUDGED}.lane.json"
            lane = json.loads(lane_path.read_text(encoding="utf-8"))
            lane["report_dir"] = str(capture)
            lane_path.write_text(json.dumps(lane), encoding="utf-8")
            self.assertTrue(vs.judge_kept(out, JUDGED).judged)
            (capture / vs.REPORT).unlink()
            self.assertFalse(vs.judge_kept(out, JUDGED).judged)

    def test_a_malformed_retained_location_never_falls_back_to_a_stale_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = self.kept_dir(tmp, [JUDGED])
            lane_path = out / f"{JUDGED}.lane.json"
            lane = json.loads(lane_path.read_text(encoding="utf-8"))
            for location in (None, "", "relative/path", 3, [], {}):
                with self.subTest(location=location):
                    lane["report_dir"] = location
                    lane_path.write_text(json.dumps(lane), encoding="utf-8")
                    result = vs.judge_kept(out, JUDGED)
                    self.assertFalse(result.judged)
                    self.assertIn("invalid retained report directory", result.reasons[0])

    def test_rejudge_passes_and_lists_the_not_judged_crates(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.fake_root(tmp, ledger_text())
            out = self.kept_dir(tmp, [JUDGED, ADMISSION])
            # The run's own record: a re-judge (here of a subset) never overwrites it.
            (out / "summary.json").write_text('{"the run": "record"}\n', encoding="utf-8")
            code, text = self.run_main(["--root", str(root), "--out", str(out), "--rejudge"])
            code_subset, _ = self.run_main(["--root", str(root), "--out", str(out), "--rejudge", "--crates", JUDGED])
            summary = json.loads((out / "summary.rejudge.json").read_text(encoding="utf-8"))
            record = (out / "summary.json").read_text(encoding="utf-8")
        self.assertEqual(code, 0, text)
        self.assertEqual(code_subset, 0)
        self.assertEqual(record, '{"the run": "record"}\n')
        self.assertIn(f"JUDGED (1 of 2): {JUDGED}", text)
        self.assertIn(f"NOT JUDGED (1 of 2): {ADMISSION}", text)
        self.assertIn("verified-survey: PASS", text)
        self.assertIn("Unknown rows are not gated: no crate is claimed verified", text)
        self.assertEqual(list(summary), [JUDGED], "the last re-judge was of the subset")

    def test_rejudge_fails_on_the_real_demoted_refutations(self):
        # The same run a status-only reader PASSED (measured 2026-09-30:
        # exit 0, "every refutation in the ledger") fails by name here.
        with tempfile.TemporaryDirectory() as tmp:
            root = self.fake_root(tmp, ledger_text())
            out = self.kept_dir(tmp, [PLANTED])
            code, text = self.run_main(["--root", str(root), "--out", str(out), "--rejudge"])
        self.assertEqual(code, 1, text)
        self.assertEqual(text.count("NEW refutation trust-ir-fmt"), 3, text)
        self.assertIn("`trust_ir_fmt::planted_unwrap` assertion `@43:4-43:14`: 1 refuted row(s) (1 demoted)", text)
        self.assertIn("`trust_ir_fmt::planted_unwrap` hardened_panic_boundary", text)
        self.assertIn("`trust_ir_fmt::planted_unreachable` assertion", text)

    def test_rejudge_fails_on_a_planted_refutation_of_a_judged_crate(self):
        recs = records(JUDGED)
        planted = failed_row(file="benchmarks/supremacy-fixture/src/main.rs", span=(1, 0, 1, 2))
        with tempfile.TemporaryDirectory() as tmp:
            root = self.fake_root(tmp, ledger_text())
            out = self.kept_dir(tmp, [JUDGED])
            (out / JUDGED / vs.REPORT).write_bytes(b"".join(restream(with_row(recs, JUDGED, planted))))
            code, text = self.run_main(["--root", str(root), "--out", str(out), "--rejudge"])
        self.assertEqual(code, 1, text)
        self.assertIn("NEW refutation supremacy-fixture benchmarks/supremacy-fixture/src/main.rs `planted::f` "
                      "arithmetic_overflow_add `@1:0-1:2`", text)

    def test_the_same_refutation_under_a_stop_is_not_gated(self):
        recs = records(JUDGED)
        planted = failed_row(file="benchmarks/supremacy-fixture/src/main.rs", span=(1, 0, 1, 2))
        stop = lane_budget_rows()["strict_timeout"]["row"]
        with tempfile.TemporaryDirectory() as tmp:
            root = self.fake_root(tmp, ledger_text())
            out = self.kept_dir(tmp, [JUDGED])
            (out / JUDGED / vs.REPORT).write_bytes(
                b"".join(restream(with_row(with_row(recs, JUDGED, planted), JUDGED, stop, "planted::g")))
            )
            code, text = self.run_main(["--root", str(root), "--out", str(out), "--rejudge"])
        self.assertEqual(code, 0, text)
        self.assertIn("NOT JUDGED (1 of 1): supremacy-fixture", text)


class BuildTree(unittest.TestCase):
    def test_a_survey_clears_its_own_build_tree_and_nothing_else(self):
        # Measured: every run rebuilds its dependencies under fresh
        # fingerprints, so a kept tree only grows (6.2 -> 9.8 -> 13.4 GiB).
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / vs.LEDGER).parent.mkdir(parents=True)
            (root / vs.LEDGER).write_text(ledger_text(), encoding="utf-8")
            build = root / vs.TARGET / "debug" / "deps"
            build.mkdir(parents=True)
            (build / "liblibc-0123456789abcdef.rmeta").write_bytes(b"x" * 10)
            keep = root / vs.TARGET / "trust-cache" / "verification.json"
            keep.parent.mkdir(parents=True)
            keep.write_text("[]", encoding="utf-8")
            reports = root / vs.TARGET / "survey"
            (reports / "old").mkdir(parents=True)
            meta = {"workspace_members": [], "packages": [], "resolve": {"nodes": []}}
            with mock.patch.object(vc, "resolve_targo", return_value="targo"), \
                    mock.patch.object(vc, "toolchain_identity", return_value="t"), \
                    mock.patch.object(vs, "metadata", return_value=meta), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(vs.main(["--root", str(root)]), 0)
            self.assertFalse((root / vs.TARGET / "debug").exists())
            self.assertTrue(keep.exists())
            self.assertTrue((reports / "old").exists())
            self.assertIsNone(vs.clear_build_tree(root / vs.TARGET), "absent: nothing to clear")


class Members(unittest.TestCase):
    def test_members_carry_the_resolved_features(self):
        meta = {
            "workspace_members": ["b 0.1", "a 0.1"],
            "packages": [
                {"id": "a 0.1", "name": "a", "features": {"default": ["x"], "x": [], "y": []}},
                {"id": "b 0.1", "name": "b", "features": {"default": ["x"], "x": []}},
            ],
            "resolve": {"nodes": [{"id": "a 0.1", "features": ["default", "x", "y"]}, {"id": "b 0.1", "features": []}]},
        }
        a, b = vs.workspace_members(meta)
        self.assertEqual((a.name, a.features, a.no_default_features), ("a", ("x", "y"), False))
        self.assertEqual(a.cargo_args(), ["-p", "a", "--features", "x,y"])
        self.assertEqual(b.cargo_args(), ["-p", "b", "--no-default-features"])


class Wiring(unittest.TestCase):
    def test_gate_15_is_opt_in_and_named(self):
        text = (ROOT / "scripts" / "ci_gates.sh").read_text(encoding="utf-8")
        self.assertRegex(text, r"(?m)^gate verified-survey verified_survey$")
        self.assertIn(vs.OPT_IN, text)
        self.assertIn("SKIP", text)

    def test_the_fixtures_carry_no_local_path(self):
        for f in FIXTURES.glob("*.*"):
            if f.is_file():
                self.assertNotIn("/Users/", f.read_text(encoding="utf-8", errors="replace"), f.name)


if __name__ == "__main__":
    unittest.main()
