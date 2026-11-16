#!/usr/bin/env python3
"""The VERIFIED lane (standing gate 13, `verified-contracts`).

Every other gate in scripts/ci_gates.sh compiles through `targo --unverified`,
the lane that makes NO proof claim (CLAUDE.md, "Toolchain posture": a known
defect, not a design). This script is the one explicit, opt-in lane in which
Trust's verification pass is ON: it runs

    targo trust check --release -p trust-ir-laws --report-dir <fresh retained run> \
        --native-bundle-dir <fresh retained run>/native-bundles

over the ONE crate whose functions carry contracts — crates/trust-ir-laws: its
own decision tables (`coverage_supports`, `license_admits_body`,
`visibility_contradicts_linkage`, `evidence_admits_kind`,
`proof_ref_kind_is_ambiguous`) and the laws of every proved table
(crates/trust-ir-laws/src/laws.rs), including laws that call tables RESIDENT IN
TRUST-IR across the crate boundary (the inliner reads trust-ir's optimized MIR;
measured 2026-09-29) — and holds the result to five things:

  1. the strict gate is green (exit 0): every obligation of the crate proved;
  2. EVERY law function (each `pub fn` of laws.rs) is present in the report
     with at least one obligation, and every obligation is `proved` with
     `assurance == Certified` and `grade.validation == KernelRechecked`
     (Clean-kernel re-checked), so the claim is per row and never an empty
     report or a bare exit code (Trust guide: "an empty report is NOT a
     proof"; and a body the MIR inliner declines turns every wrapper into a
     fail-closed UNKNOWN, which an exit-code-only gate on a crate that also
     tolerated unknowns would not see);
  3. each SAME-SHAPE mutant of a table (MUTANTS below), built as a standalone
     copy of the crate — and, when it edits a trust-ir table, of trust-ir too —
     and run through the identical lane, is REFUTED: the strict gate exits
     non-zero, every law the mutation falsifies is no longer proved AND the
     runner's `refuted obligation` line names it (the fork publishes native
     refutations as UNKNOWN, so the evidence a mutant was DISTINGUISHED is
     that line plus the exit status), and every law of the mutant's SCOPE it
     does not touch stays proved. A mutant that is merely unknown everywhere
     (the inliner declined it) is a gate FAILURE, not a control. EVERY law is
     named by at least one mutant's `flips` (`laws_without_a_mutant` must be
     empty, checked before any run): a law no mutant refutes could stop
     calling its table and still prove, so it would be a proof of nothing.
     And every law's body is EXACTLY one call of the table and cell its name
     spells (`WIRING`, `law_wiring_errors`, also checked before any run): a
     mutant that edits several tables at once flips a law whichever of them
     it calls, so the flip shows a law is not proved about a constant, and
     the wiring shows which table it is about. And every table over enum
     cells has a law at EVERY cell of its operand enums, read from their
     definitions (`cell_completeness`, also checked before any run): the
     tables' source comments say "PROVED, every cell" and a citation may name
     a family by glob, and neither may stand for a cell no law states (a new
     variant, or a deleted law). These pre-run checks are stated once, in
     `holding`, which gate 0 also reads: a `(proved-contract)` entry of
     TRUST.md or docs/SPEC_RATIFICATIONS.md is witnessed only by a law
     `holding` holds, cited after a citation of the table its WIRING names
     (scripts/check_enforcement_links.py). And every law's contract is one
     `ensures` of `ENSURES_SHAPES` (also checked before any run): gate 0
     reads each law's verdict from it (`Holding.verdicts`, rule E5).
  4. every run — the base run AND each mutant run — is JUDGED: its report's
     resource accounting passes (schema-4 budget/typed stops, or an older
     seal's recorded memory ceiling and peak RSS), no row or diagnostic names
     a budget stop, and no compiler
     request — a published row or one publication omitted from the report —
     is left unexplained. Otherwise the run is NOT JUDGED and the gate fails by
     that name, whatever its rows say: on the older seal an RSS-ceiling
     trip is invisible to the checkpoint soundness rests on and has made
     strict/certify PROVE a panicking function (counter-program p4). THE
     RULE, its measurements and its report fields are stated once, above
     `not_judged` below; a missing expected refutation is NOT JUDGED too.
  5. every run's build-script executions — the units its report tags
     `build-execution-scope`, which ran uncontained outside the proof channel
     (Trust blocker B5, P-CORESIDENT) — EQUAL the committed list
     scripts/gates/verified-contracts-build-scripts.tsv, agree with the
     report's own unit inventory, and are printed: every verdict of the lane
     rests on those scripts, so a new one is a new premise, reviewed by
     adding its row. THE BUILD-SCRIPT PREMISE below states the rule once. A
     mutant workspace copies the root's Cargo.lock so that it builds, and
     executes, the same versions as the base run.

A mutant's `scope` is the law FAMILIES (name prefixes) its copy carries and is
held to: every family that calls a table the mutant edits, and nothing else.
The base run holds every law; a mutant need not re-verify laws of tables it
cannot reach (each law is a wrapper around ONE table call — `WIRING` holds
that — so an edit to one table cannot move another's law), and without the
scope each of ~20 mutant runs would re-verify ~300 laws (about 50 s each,
measured 2026-09-29).

The verdict lines the lane prints (`Summary:` / `Gate:` / `Result:`) are
echoed verbatim for each run with the memory reading rule 4 used, and the
lane's toolchain identity is recorded.

Every native run retains its report, request, output and RSS reading in a fresh
directory beside the stable compiled-target cache (`verified-inputs/`). When
Targo advertises its diagnostic export option, the same directory also receives
finalized native bundles. Older toolchains keep the identical verification lane
and explicitly record that export was not advertised. The printed path and
`.lane.json` locate each run; later runs and mutant-workspace cleanup do not
overwrite it. Native bundles are not a complete census, proof, refutation or
source-correspondence authority.

Why `--release`: the verdict is about OPTIMIZED MIR (Trust guide §9h); the
laws are wrappers whose clauses are about the table only because the inliner
puts the table's body inside them, and without `-O` every row is UNKNOWN
(measured). Why a leaf crate: `targo trust` verifies every function of the
primary package and excludes dependency units, so the unit must be small.

Never sets RUSTFLAGS and adds no Cargo config: the policy that applies is the
root manifest's `[trust]` table, and each mutant workspace carries the same
table. Mutant copies live under <ROOT>/target/verified-lane/ (owner-only:
`targo trust` refuses a world-writable path component, so never /tmp); a
trust-ir mutant compiles its own copy, which is why the trust-ir tables'
edits are BATCHED into two mutants (every table negated; one neighbour
spelling per table) rather than one trust-ir build per edit.

SCHEDULING (scripts/host_scale.py). The mutant runs are independent — own
workspace, own report directory — so they run in parallel SLOTS when the host
has room: after the base run, `mutant_workers` measures cores, load and
available memory and admits as many slots as fit both the memory (a slot
builds with -j c, c = the CPU the base run used per wall second, so it is
capped at c x the base run's peak process) and the cores the load leaves (c
per slot). One slot is the old gate exactly (Targo's default -j). Slot 0
reuses the base run's target directory, slot i uses target-<i> (removed at
the end). Every run is judged exactly as before, one after another in MUTANTS
order, after all have finished. A loaded host gets one slot: the serial gate.
`--serial` forces it.

Usage: verified_contracts.py [--root DIR] [--out DIR] [--keep] [--base-only] [--serial]
Exit 0 iff every check above holds; exit 1 on a FAIL or a NOT JUDGED finding.
Cost: every `targo trust check` run rebuilds its dependency graph (measured
2026-09-29: a second run in the SAME workspace with the SAME report directory
rebuilt all 12 units again), so each of the 19 runs (base + 18 mutants) costs
about a minute of dependency build before any verification; the whole gate
took 9 min 33 s at a load average of ~30 and 21 min 46 s at ~52 on 14 cores
(the 15-run gate before the second wave: 8 min 42 s and 5 min 16 s at ~40
and ~30). Batching the
laws-only mutants into one multi-package run is the known way down (not done:
it would lose the per-mutant exit status, one of the two refutation signals).
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import queue
import threading
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple

sys.path.insert(0, os.fspath(Path(__file__).resolve().parent))
# The shared Rust lexer (comments, strings, chars, raw strings masked), as gate 0
# uses it: the cell tables' enums are read from masked source.
from check_no_ignored_rust import mask_non_code  # noqa: E402

CRATE = "trust-ir-laws"
CRATE_IDENT = CRATE.replace("-", "_")
CRATE_DIR = Path("crates") / CRATE
LAWS_FILE = CRATE_DIR / "src" / "laws.rs"
TABLES_FILE = CRATE_DIR / "src" / "lib.rs"
# The format crate, whose resident tables some laws call across the crate
# boundary. A mutant that edits one copies it (never the tests or docs).
IR_CRATE = "trust-ir"
IR_CRATE_DIR = Path("crates") / IR_CRATE
CRATE_DIRS = {CRATE: CRATE_DIR, IR_CRATE: IR_CRATE_DIR}
# The subject functions themselves: verified in the base run (their own
# `unreachable` rows) so an edit that breaks the TABLE's verification, not just
# a law, is also seen. (The trust-ir-resident tables are dependency units the
# lane excludes; their laws are what it holds.)
SUBJECTS = (
    "coverage_supports",
    "license_admits_body",
    "visibility_contradicts_linkage",
    "evidence_admits_kind",
    "proof_ref_kind_is_ambiguous",
)
VERDICT_LINE = re.compile(r"^(Summary|Gate|Result|Coverage):")
REFUTED_LINE = re.compile(r"refuted obligation")
LAW_FN = re.compile(r"^pub fn (\w+)\(", re.M)
PUB_ITEM = re.compile(r"^pub (?!fn )", re.M)
# The name every finding of `not_judged` carries (and a missing expected
# refutation, `check_rows`): the run's verdict is not evidence either way.
NOT_JUDGED = "NOT JUDGED:"


@dataclass(frozen=True)
class Edit:
    """One same-shape edit: `old` must occur EXACTLY once in `file` (relative
    to `crate`'s directory) in the real source, and a mutant's edits of one
    file must not overlap (they are applied together, to the original text)."""

    crate: str
    file: str
    old: str
    new: str


def laws_edit(file: str, old: str, new: str) -> Edit:
    return Edit(CRATE, file, old, new)


def ir_edit(file: str, old: str, new: str) -> Edit:
    return Edit(IR_CRATE, file, old, new)


@dataclass(frozen=True)
class Mutant:
    """Same-shape edits of one or more tables, the laws they falsify, and the
    law families (`scope`, name prefixes) the mutant's run is held to."""

    name: str
    edits: Tuple[Edit, ...]
    flips: Tuple[str, ...]
    scope: Tuple[str, ...]
    why: str

    @property
    def mutates_trust_ir(self) -> bool:
        return any(e.crate == IR_CRATE for e in self.edits)


# The families of the pre-2026-09-29 tables: `coverage_supports` (and the
# integer half of its transitivity) and `license_admits_body`.
ORIGINAL_SCOPE = ("coverage_", "u64_ge_", "license_")
# The families of the tables resident in trust-ir, plus `visibility_`, whose
# table calls `Linkage::is_module_local` across the crate boundary.
IR_SCOPE = (
    "rc_",
    "interposable_",
    "module_local_",
    "contract_surface_linkage_",
    "visibility_",
    "discharged_tier_",
    "kernel_tier_",
    "atomic_load_",
    "atomic_store_",
    "cc_abi_surface_",
    "tag_abi_surface_",
    "hv_fail_closed_",
    "backed_by_",
    "inherited_",
    "call_edge_",
    "handle_declaration_",
    "grounded_contract_kind_",
    "free_var_proved_",
    "assert_class_",
    "terminator_",
    # the fresh-id rule's three u32 tables (value.rs, r11 R1)
    "fresh_",
    "borrow_permission_",
)
# The families of this crate's other local tables.
LOCAL_SCOPE = ("visibility_", "evidence_", "ambiguous_")

# ObligationKindShape variants, as law-name suffixes (`backed_by_<kind>`).
KINDS = (
    "precondition", "postcondition", "loop_invariant", "type_invariant", "refinement_type",
    "translation_validation", "memory_safety", "panic_freedom", "temporal_safety", "liveness",
    "arithmetic_safety", "bounds_check", "give_back_refinement", "termination", "ownership",
    "custom",
)


def cells(family: str, variants: Sequence[str]) -> Tuple[str, ...]:
    return tuple(f"{family}_{v}" for v in variants)


def negate(file: str, signature: str) -> Edit:
    """Negate a `matches!` table: `signature` is the fn line and the body's
    first line, which the edit rewrites from `matches!(` to `!matches!(`."""
    assert signature.endswith("matches!("), signature
    return ir_edit(file, signature, signature[: -len("matches!(")] + "!matches!(")


# A `flips` entry containing `*` is a GLOB over law names (`fnmatch`), naming
# every law it matches; it must match at least one. `rc_*` is how a mutant
# that NEGATES a table says "every law of this family": every cell changes, and
# a law quantified over the family's enum is refuted at every instance.
MUTANTS: Tuple[Mutant, ...] = (
    Mutant(
        name="coverage-unwind-supplies-model",
        edits=(
            laws_edit(
                "src/lib.rs",
                "        (CoverageBound::Unbounded, CoverageBound::ModelBounded { .. }) => true,\n",
                "        (CoverageBound::UnwindBounded { .. }, CoverageBound::ModelBounded { .. }) => true,\n",
            ),
        ),
        flips=("coverage_unwind_never_supplies_model", "coverage_unbounded_supplies_model"),
        scope=ORIGINAL_SCOPE,
        why="folds the two bounded axes into one (the bug the rule exists to prevent), "
        "spelled in place of the `Unbounded` arm so the decision tree keeps its shape "
        "and the inliner keeps the body — a literal added arm is declined by the "
        "inliner and fails closed UNKNOWN instead (measured 2026-09-24)",
    ),
    Mutant(
        name="coverage-strict-unwind-order",
        edits=(
            laws_edit(
                "src/lib.rs",
                "            CoverageBound::UnwindBounded { depth: need },\n        ) => have >= need,\n",
                "            CoverageBound::UnwindBounded { depth: need },\n        ) => have > need,\n",
            ),
        ),
        flips=("coverage_reflexive_unwind", "coverage_unwind_is_magnitude_order"),
        scope=ORIGINAL_SCOPE,
        why="strict order on the unwind axis: an equal depth no longer supplies itself",
    ),
    Mutant(
        name="license-absent-admitted-under-refuse",
        edits=(
            laws_edit(
                "src/lib.rs",
                "        (GateShape::Absent, UnlicensedBodyPolicy::Refuse) => false,\n",
                "        (GateShape::Absent, UnlicensedBodyPolicy::Refuse) => true,\n",
            ),
        ),
        flips=("license_absent_refused_under_refuse",),
        scope=ORIGINAL_SCOPE,
        why="the fail-closed default permits an unlicensed body: the interlock stops being one",
    ),
    Mutant(
        name="license-ungated-admitted",
        edits=(
            laws_edit(
                "src/lib.rs",
                "        (GateShape::Ungated, _) => false,\n",
                "        (GateShape::Ungated, _) => true,\n",
            ),
        ),
        flips=("license_ungated_refused_under_any_policy",),
        scope=ORIGINAL_SCOPE,
        why="an affirmative `Ungated` body is admitted: the must-refuse corpus row "
        "`refuse/body_gate_ungated` would pass",
    ),
    # --- the remaining rows: every law below is refuted by exactly one of
    # these (measured 2026-09-25; before them 20 of the 26 laws had no
    # mutant, so a wrapper that stopped calling the table would still have
    # "proved" — `ensures result == false` over a body of `false` proves).
    Mutant(
        name="coverage-unrecorded-supplies-unbounded",
        edits=(
            laws_edit(
                "src/lib.rs",
                "        (CoverageBound::Unbounded, CoverageBound::Unbounded) => true,\n",
                "        (CoverageBound::Unrecorded, CoverageBound::Unbounded) => true,\n",
            ),
        ),
        flips=(
            "coverage_reflexive_unbounded",
            "coverage_unbounded_supplies_unbounded",
            "coverage_unrecorded_never_supplies_unbounded",
        ),
        scope=ORIGINAL_SCOPE,
        why="`Unrecorded` gains unbounded standing by omission (the exact sentence its "
        "rustdoc forbids) and `Unbounded` stops supplying itself",
    ),
    Mutant(
        name="coverage-unrecorded-supplies-unwind",
        edits=(
            laws_edit(
                "src/lib.rs",
                "        (CoverageBound::Unbounded, CoverageBound::UnwindBounded { .. }) => true,\n",
                "        (CoverageBound::Unrecorded, CoverageBound::UnwindBounded { .. }) => true,\n",
            ),
        ),
        flips=("coverage_unbounded_supplies_unwind", "coverage_unrecorded_never_supplies_unwind"),
        scope=ORIGINAL_SCOPE,
        why="`Unrecorded` supplies an unwind depth (`depth: 0` included) and `Unbounded` no longer does",
    ),
    Mutant(
        name="coverage-unrecorded-supplies-model",
        edits=(
            laws_edit(
                "src/lib.rs",
                "        (CoverageBound::Unbounded, CoverageBound::ModelBounded { .. }) => true,\n",
                "        (CoverageBound::Unrecorded, CoverageBound::ModelBounded { .. }) => true,\n",
            ),
        ),
        flips=("coverage_unbounded_supplies_model", "coverage_unrecorded_never_supplies_model"),
        scope=ORIGINAL_SCOPE,
        why="`Unrecorded` supplies a model size and `Unbounded` no longer does",
    ),
    Mutant(
        name="coverage-model-supplies-unwind",
        edits=(
            laws_edit(
                "src/lib.rs",
                "        (CoverageBound::Unbounded, CoverageBound::UnwindBounded { .. }) => true,\n",
                "        (CoverageBound::ModelBounded { .. }, CoverageBound::UnwindBounded { .. }) => true,\n",
            ),
        ),
        flips=("coverage_unbounded_supplies_unwind", "coverage_model_never_supplies_unwind"),
        scope=ORIGINAL_SCOPE,
        why="the other cross-axis fold: a finite model instance supplies an unwind depth",
    ),
    Mutant(
        name="coverage-strict-model-order",
        edits=(
            laws_edit(
                "src/lib.rs",
                "            CoverageBound::ModelBounded { size: need },\n        ) => have >= need,\n",
                "            CoverageBound::ModelBounded { size: need },\n        ) => have > need,\n",
            ),
        ),
        flips=("coverage_reflexive_model", "coverage_model_is_magnitude_order"),
        scope=ORIGINAL_SCOPE,
        why="strict order on the model axis: an equal size no longer supplies itself",
    ),
    Mutant(
        name="coverage-unrecorded-demand-met-only-by-unbounded",
        edits=(
            laws_edit(
                "src/lib.rs",
                "        (_, CoverageBound::Unrecorded) => true,\n",
                "        (CoverageBound::Unbounded, CoverageBound::Unrecorded) => true,\n",
            ),
        ),
        flips=(
            "coverage_unrecorded_demand_met_by_unwind",
            "coverage_unrecorded_demand_met_by_model",
            "coverage_unrecorded_demand_met_by_unrecorded",
            "coverage_unrecorded_demand_met_by_any",
        ),
        scope=ORIGINAL_SCOPE,
        why="the `needs` column for `Unrecorded` narrows to one supplier: a no-grade demand "
        "is no longer met by a bounded or absent grade",
    ),
    Mutant(
        name="coverage-unbounded-demand-met-by-anything",
        edits=(
            laws_edit(
                "src/lib.rs",
                "        (_, CoverageBound::Unrecorded) => true,\n",
                "        (_, CoverageBound::Unbounded) => true,\n",
            ),
        ),
        flips=(
            "coverage_unbounded_supplies_unrecorded",
            "coverage_unrecorded_demand_met_by_unbounded",
            "coverage_unrecorded_demand_met_by_unwind",
            "coverage_unrecorded_demand_met_by_model",
            "coverage_unrecorded_demand_met_by_unrecorded",
            "coverage_unrecorded_demand_met_by_any",
            "coverage_unwind_never_supplies_unbounded",
            "coverage_model_never_supplies_unbounded",
            "coverage_unrecorded_never_supplies_unbounded",
        ),
        scope=ORIGINAL_SCOPE,
        why="the wildcard column moves from the `Unrecorded` demand to the `Unbounded` one: "
        "every bounded rung now supplies `Unbounded` (the residual-ledger case) and "
        "the `Unrecorded` demand is met by nothing",
    ),
    Mutant(
        name="u64-ge-transitive-strict",
        edits=(
            laws_edit(
                "src/laws.rs",
                "    a >= c\n",
                "    a > c\n",
            ),
        ),
        flips=("u64_ge_is_transitive",),
        scope=ORIGINAL_SCOPE,
        why="the integer half of transitivity, made strict: `a == b == c` refutes it",
    ),
    Mutant(
        name="license-gated-refused",
        edits=(
            laws_edit(
                "src/lib.rs",
                "        (GateShape::Gated, _) => true,\n",
                "        (GateShape::Gated, _) => false,\n",
            ),
        ),
        flips=("license_gated_admitted_under_any_policy",),
        scope=ORIGINAL_SCOPE,
        why="a gated body is refused by the admission table: the `Gated` arm in "
        "`license_errors_against` would become reachable",
    ),
    Mutant(
        name="license-absent-refused-under-permit",
        edits=(
            laws_edit(
                "src/lib.rs",
                "        (GateShape::Absent, UnlicensedBodyPolicy::Permit) => true,\n",
                "        (GateShape::Absent, UnlicensedBodyPolicy::Permit) => false,\n",
            ),
        ),
        flips=("license_absent_admitted_under_permit",),
        scope=ORIGINAL_SCOPE,
        why="the grandfather filter stops admitting: `Permit` becomes `Refuse`",
    ),
    # --- the tables resident in trust-ir (2026-09-29). Two BATCHED mutants,
    # each ONE trust-ir copy: the lane compiles that copy (about 30 s), so
    # one mutant per edit would cost a trust-ir build per edit. A batch that
    # edits every table flips a law WHICHEVER table the law calls, so the
    # flip alone does not show a law is about its own table (review,
    # 2026-09-29: a law re-pointed at another table still flipped and the
    # gate passed). That half is `law_wiring_errors`, checked before any run:
    # every law's body is exactly one call of the table and cell its name
    # spells (the one cross-table call, `visibility_contradicts_linkage` ->
    # `Linkage::is_module_local`, is inside a table, in the scope and in the
    # flips). Measured 2026-09-29: both batches refuted exactly the laws
    # listed here and moved none other.
    Mutant(
        name="trust-ir-every-table-negated",
        edits=(
            negate("src/inst.rs", "    pub const fn is_reference_counted(self) -> bool {\n        matches!("),
            ir_edit(
                "src/lib.rs",
                "            Linkage::Weak | Linkage::LinkOnce | Linkage::ExternalWeak => true,\n",
                "            Linkage::Weak | Linkage::LinkOnce | Linkage::ExternalWeak => false,\n",
            ),
            ir_edit(
                "src/lib.rs",
                "            | Linkage::LinkOnceOdr => false,\n",
                "            | Linkage::LinkOnceOdr => true,\n",
            ),
            negate("src/lib.rs", "    pub const fn is_module_local(self) -> bool {\n        matches!("),
            negate("src/lib.rs", "    pub const fn requires_contract_surface(self) -> bool {\n        matches!("),
            ir_edit(
                "src/proof/obligations.rs",
                "            ProofStatus::Discharged | ProofStatus::Certified => true,\n"
                "            ProofStatus::Pending | ProofStatus::Failed | ProofStatus::Trusted => false,\n",
                "            ProofStatus::Discharged | ProofStatus::Certified => false,\n"
                "            ProofStatus::Pending | ProofStatus::Failed | ProofStatus::Trusted => true,\n",
            ),
            ir_edit(
                "src/proof/obligations.rs",
                "            ProofStatus::Certified => true,\n",
                "            ProofStatus::Certified => false,\n",
            ),
            ir_edit(
                "src/proof/obligations.rs",
                "            | ProofStatus::Trusted => false,\n",
                "            | ProofStatus::Trusted => true,\n",
            ),
            negate("src/inst.rs", "    pub const fn is_legal_for_load(self) -> bool {\n        matches!("),
            negate("src/inst.rs", "    pub const fn is_legal_for_store(self) -> bool {\n        matches!("),
            ir_edit(
                "src/lib.rs",
                "    pub fn is_abi_surface(self) -> bool {\n        matches!(",
                "    pub fn is_abi_surface(self) -> bool {\n        !matches!(",
            ),
            ir_edit(
                "src/ty.rs",
                "    pub fn is_abi_surface(self) -> bool {\n        matches!(",
                "    pub fn is_abi_surface(self) -> bool {\n        !matches!(",
            ),
            ir_edit(
                "src/request/evidence.rs",
                "        !matches!(self, HardwareVectorContractStatus::Available)\n",
                "        matches!(self, HardwareVectorContractStatus::Available)\n",
            ),
            # `admits_shape` is inlined at a cost of 95 against 100, so it is
            # not negated (a `!` per row); its rows are RELABELLED instead:
            # the `backed_by` list moves to `CallEdge`, the inheritance list
            # (plus `Custom`, an alternative, which costs nothing) to
            # `SummaryBackedBy`, and the claim-free arm to the other two.
            ir_edit(
                "src/imports.rs",
                "            ExternRefSite::SummaryBackedBy => matches!(\n",
                "            ExternRefSite::CallEdge => matches!(\n",
            ),
            ir_edit(
                "src/imports.rs",
                "            ExternRefSite::InheritedFromCallee => matches!(\n",
                "            ExternRefSite::SummaryBackedBy => matches!(\n",
            ),
            ir_edit(
                "src/imports.rs",
                "            ExternRefSite::CallEdge | ExternRefSite::HandleDeclaration => false,\n",
                "            ExternRefSite::InheritedFromCallee | ExternRefSite::HandleDeclaration => false,\n",
            ),
            ir_edit(
                "src/imports.rs",
                "                    | ObligationKindShape::Ownership\n            ),\n",
                "                    | ObligationKindShape::Ownership\n                    | ObligationKindShape::Custom\n            ),\n",
            ),
            negate("src/proof/obligations.rs", "    pub const fn is_grounded_contract_kind(self) -> bool {\n        matches!("),
            negate("src/proof/obligations.rs", "    pub const fn free_var_is_proved(self) -> bool {\n        matches!("),
            negate("src/proof/obligations.rs", "    pub const fn is_assert_class(self) -> bool {\n        matches!("),
            negate("src/inst.rs", "    pub const fn is_terminator(self) -> bool {\n        matches!("),
            # the fresh-id rule's comparisons, each negated
            ir_edit("src/value.rs", "    id < u32::MAX\n", "    id >= u32::MAX\n"),
            ir_edit("src/value.rs", "    extra <= room\n", "    extra > room\n"),
            ir_edit("src/value.rs", "    id < end_exclusive\n", "    id >= end_exclusive\n"),
            negate("src/inst.rs", "    pub const fn uses_borrow_permissions(self) -> bool {\n        matches!("),
        ),
        flips=(
            "rc_*",
            "interposable_*",
            "module_local_*",
            "contract_surface_linkage_*",
            "discharged_tier_*",
            "kernel_tier_*",
            "atomic_load_*",
            "atomic_store_*",
            "cc_abi_surface_*",
            "tag_abi_surface_*",
            "hv_fail_closed_*",
            "grounded_contract_kind_*",
            "free_var_proved_*",
            "assert_class_*",
            "terminator_*",
            "fresh_*",
            "borrow_permission_*",
            # `backed_by` now admits every kind: its thirteen refusals flip.
            *cells("backed_by", [k for k in KINDS if k not in ("precondition", "postcondition", "termination")]),
            # inheritance admits nothing: its fifteen admissions flip.
            *cells("inherited", [k for k in KINDS if k != "custom"]),
            "call_edge_admits_nothing",
            # module-locality negated: a local linkage's Hidden/Protected no
            # longer contradicts, and every other linkage's now does.
            *cells("visibility_internal", ("hidden", "protected")),
            *cells("visibility_private", ("hidden", "protected")),
            *(f"visibility_{l}_never_contradicts" for l in (
                "external", "weak", "link_once", "available_externally", "external_weak",
                "weak_odr", "link_once_odr",
            )),
        ),
        scope=IR_SCOPE,
        why="every trust-ir table negated (the exhaustive ones by swapping their arms): "
        "every cell law of each flips, so none is proved about a constant; that each "
        "calls ITS table is the wiring check, not this flip",
    ),
    Mutant(
        name="trust-ir-neighbour-spellings",
        edits=(
            ir_edit(
                "src/inst.rs",
                "        matches!(self, AllocOrigin::SwiftHeap | AllocOrigin::CleanHeap)\n",
                "        matches!(self, AllocOrigin::RustHeap | AllocOrigin::CleanHeap)\n",
            ),
            ir_edit(
                "src/lib.rs",
                "            Linkage::Weak | Linkage::LinkOnce | Linkage::ExternalWeak => true,\n"
                "            Linkage::External\n",
                "            Linkage::Weak | Linkage::LinkOnce => true,\n"
                "            Linkage::ExternalWeak\n"
                "            | Linkage::External\n",
            ),
            ir_edit(
                "src/lib.rs",
                "        matches!(self, Linkage::Internal | Linkage::Private)\n",
                "        matches!(self, Linkage::Internal | Linkage::Weak)\n",
            ),
            ir_edit(
                "src/lib.rs",
                "                | Linkage::LinkOnceOdr\n        )\n",
                "                | Linkage::LinkOnce\n        )\n",
            ),
            ir_edit(
                "src/proof/obligations.rs",
                "            ProofStatus::Discharged | ProofStatus::Certified => true,\n"
                "            ProofStatus::Pending | ProofStatus::Failed | ProofStatus::Trusted => false,\n",
                "            ProofStatus::Discharged | ProofStatus::Trusted => true,\n"
                "            ProofStatus::Pending | ProofStatus::Failed | ProofStatus::Certified => false,\n",
            ),
            ir_edit(
                "src/proof/obligations.rs",
                "            ProofStatus::Certified => true,\n"
                "            ProofStatus::Pending\n"
                "            | ProofStatus::Discharged\n",
                "            ProofStatus::Discharged => true,\n"
                "            ProofStatus::Pending\n"
                "            | ProofStatus::Certified\n",
            ),
            ir_edit(
                "src/inst.rs",
                "            Ordering::Relaxed | Ordering::Acquire | Ordering::SeqCst\n",
                "            Ordering::Relaxed | Ordering::AcqRel | Ordering::SeqCst\n",
            ),
            ir_edit(
                "src/inst.rs",
                "            Ordering::Relaxed | Ordering::Release | Ordering::SeqCst\n",
                "            Ordering::Relaxed | Ordering::AcqRel | Ordering::SeqCst\n",
            ),
            ir_edit(
                "src/lib.rs",
                "                | CallingConv::RustCold\n        )\n",
                "                | CallingConv::Cold\n        )\n",
            ),
            ir_edit(
                "src/ty.rs",
                "        matches!(self, EnumTagRepr::U128 | EnumTagRepr::I128)\n",
                "        matches!(self, EnumTagRepr::U128 | EnumTagRepr::I64)\n",
            ),
            ir_edit(
                "src/request/evidence.rs",
                "        !matches!(self, HardwareVectorContractStatus::Available)\n",
                "        !matches!(self, HardwareVectorContractStatus::Unavailable)\n",
            ),
            # The other relabelling of `admits_shape`: the `backed_by` list
            # (plus `Custom`) moves to `InheritedFromCallee`, the inheritance
            # list to `HandleDeclaration`, the claim-free arm to the other two.
            ir_edit(
                "src/imports.rs",
                "            ExternRefSite::SummaryBackedBy => matches!(\n",
                "            ExternRefSite::InheritedFromCallee => matches!(\n",
            ),
            ir_edit(
                "src/imports.rs",
                "            ExternRefSite::InheritedFromCallee => matches!(\n",
                "            ExternRefSite::HandleDeclaration => matches!(\n",
            ),
            ir_edit(
                "src/imports.rs",
                "            ExternRefSite::CallEdge | ExternRefSite::HandleDeclaration => false,\n",
                "            ExternRefSite::SummaryBackedBy | ExternRefSite::CallEdge => false,\n",
            ),
            ir_edit(
                "src/imports.rs",
                "                    | ObligationKindShape::Termination\n            ),\n",
                "                    | ObligationKindShape::Termination\n                    | ObligationKindShape::Custom\n            ),\n",
            ),
            ir_edit(
                "src/proof/obligations.rs",
                "                | ObligationKindShape::LoopInvariant\n"
                "                | ObligationKindShape::RefinementType\n        )\n",
                "                | ObligationKindShape::LoopInvariant\n"
                "                | ObligationKindShape::TypeInvariant\n        )\n",
            ),
            ir_edit(
                "src/proof/obligations.rs",
                "            ObligationKindShape::Postcondition | ObligationKindShape::RefinementType\n",
                "            ObligationKindShape::Postcondition | ObligationKindShape::LoopInvariant\n",
            ),
            ir_edit(
                "src/proof/obligations.rs",
                "            ObligationKindShape::BoundsCheck | ObligationKindShape::ArithmeticSafety\n",
                "            ObligationKindShape::Liveness | ObligationKindShape::ArithmeticSafety\n",
            ),
            ir_edit(
                "src/inst.rs",
                "                | InstShape::AssertInvoke\n                | InstShape::Unreachable\n",
                "                | InstShape::AssertInvoke\n                | InstShape::Assert\n",
            ),
            # THE WRAP: `u32::MAX` given a successor. The cursor decides by
            # this table alone, so under this edit it steps from `u32::MAX`
            # onto id 0 (measured 2026-10-01, value.rs tests:
            # `after([0, u32::MAX])` is no longer exhausted), the defect class
            # the fresh-id rule exists to refuse.
            ir_edit("src/value.rs", "    id < u32::MAX\n", "    id <= u32::MAX\n"),
            # a run that exactly fills the room refused (strict room order)
            ir_edit("src/value.rs", "    extra <= room\n", "    extra < room\n"),
            # the bound's own id admitted: a run reaches into the reserved range
            ir_edit("src/value.rs", "    id < end_exclusive\n", "    id <= end_exclusive\n"),
            # `EndBorrow` leaves the permission table and `Copy` joins it: the
            # end of a borrow no longer counts, and the Rust producers' spelling
            # of a reference becomes a permission instruction.
            ir_edit(
                "src/inst.rs",
                "            InstShape::Borrow | InstShape::BorrowMut | InstShape::EndBorrow\n        )\n",
                "            InstShape::Borrow | InstShape::BorrowMut | InstShape::Copy\n        )\n",
            ),
        ),
        flips=(
            "rc_rust_heap",
            "rc_swift_heap",
            # core_reflection.rs's own spelling of "replaceable" ({Weak, LinkOnce})
            "interposable_external_weak",
            "module_local_private",
            "module_local_weak",
            "visibility_private_hidden",
            "visibility_private_protected",
            "visibility_weak_never_contradicts",
            "contract_surface_linkage_link_once",
            "contract_surface_linkage_link_once_odr",
            # a Trusted row counted as discharged; a Certified one not
            "discharged_tier_trusted",
            "discharged_tier_certified",
            "kernel_tier_discharged",
            "kernel_tier_certified",
            "atomic_load_acquire",
            "atomic_load_acq_rel",
            "atomic_store_release",
            "atomic_store_acq_rel",
            "cc_abi_surface_cold",
            "cc_abi_surface_rust_cold",
            "tag_abi_surface_i64",
            "tag_abi_surface_i128",
            "hv_fail_closed_available",
            "hv_fail_closed_unavailable",
            # `backed_by` admits nothing: its three admissions flip; inheritance
            # admits only the contract kinds and `Custom`.
            *cells("backed_by", ("precondition", "postcondition", "termination")),
            *cells("inherited", [k for k in KINDS if k not in ("precondition", "postcondition", "termination")]),
            "handle_declaration_admits_nothing",
            "grounded_contract_kind_type_invariant",
            "grounded_contract_kind_refinement_type",
            # a RefinementType ASSUMED and a LoopInvariant PROVED: the
            # catastrophic direction the table's doc names
            "free_var_proved_loop_invariant",
            "free_var_proved_refinement_type",
            "assert_class_liveness",
            "assert_class_bounds_check",
            "terminator_assert",
            "terminator_unreachable",
            # the wrap: u32::MAX has a successor
            "fresh_successor_iff_below_max",
            "fresh_successor_absent_at_max",
            # the strict room: a run filling its room (a one-id run at the
            # last id, the whole space from 0) is refused
            "fresh_run_fits_iff_within_room",
            "fresh_run_fits_single_id_anywhere",
            "fresh_run_fits_whole_space",
            # the bound's own id admitted
            "fresh_below_iff_less",
            "fresh_below_refuses_the_bound",
            "borrow_permission_end_borrow",
            "borrow_permission_copy",
        ),
        scope=IR_SCOPE,
        why="one NEIGHBOUR spelling per trust-ir table (the variant each rule exists to "
        "tell apart moved across its line): exactly the two cells it swaps flip",
    ),
    # --- this crate's other local tables (2026-09-29), two batches: the three
    # tables are disjoint and none calls another. As for the trust-ir batches,
    # which table each law is about is `law_wiring_errors`, not the flip.
    Mutant(
        name="local-tables-relabelled",
        edits=(
            laws_edit(
                "src/lib.rs",
                "    linkage.is_module_local() && matches!(visibility, Visibility::Hidden | Visibility::Protected)\n",
                "    linkage.is_module_local() && matches!(visibility, Visibility::Default | Visibility::Protected)\n",
            ),
            laws_edit(
                "src/lib.rs",
                "        ProofEvidenceShape::TranslationValidation => {\n",
                "        ProofEvidenceShape::SmtProof => {\n",
            ),
            laws_edit(
                "src/lib.rs",
                "        ProofEvidenceShape::GammaCrownBound => matches!(\n",
                "        ProofEvidenceShape::LeanProof => matches!(\n",
            ),
            laws_edit(
                "src/lib.rs",
                "        ObligationKindShape::Precondition\n"
                "            | ObligationKindShape::Postcondition\n"
                "            | ObligationKindShape::LoopInvariant\n"
                "            | ObligationKindShape::TypeInvariant\n"
                "            | ObligationKindShape::RefinementType\n"
                "            | ObligationKindShape::TranslationValidation\n"
                "            | ObligationKindShape::TemporalSafety\n"
                "            | ObligationKindShape::Liveness\n",
                "        ObligationKindShape::MemorySafety\n"
                "            | ObligationKindShape::PanicFreedom\n"
                "            | ObligationKindShape::ArithmeticSafety\n"
                "            | ObligationKindShape::BoundsCheck\n"
                "            | ObligationKindShape::GiveBackRefinement\n"
                "            | ObligationKindShape::Termination\n"
                "            | ObligationKindShape::Ownership\n"
                "            | ObligationKindShape::Custom\n",
            ),
        ),
        flips=(
            # `Default` contradicts a local linkage; `Hidden` no longer does
            *cells("visibility_internal", ("default", "hidden")),
            *cells("visibility_private", ("default", "hidden")),
            # the TranslationValidation and GammaCrownBound rows move to
            # SmtProof and LeanProof: the moved evidence becomes unconstrained
            *cells("evidence_tv", [k for k in KINDS if k != "translation_validation"]),
            *cells("evidence_gamma", [k for k in KINDS if k not in ("postcondition", "custom")]),
            "evidence_smt_proof_unconstrained",
            "evidence_lean_proof_unconstrained",
            # the ambiguous set replaced by its complement (also eight kinds)
            "ambiguous_*",
        ),
        scope=LOCAL_SCOPE,
        why="the three local tables relabelled at the same shape: visibility's contradicting "
        "column, the two constrained evidence rows, and the ambiguous set's complement",
    ),
    Mutant(
        name="local-tables-neighbour-spellings",
        edits=(
            laws_edit(
                "src/lib.rs",
                "    linkage.is_module_local() && matches!(visibility, Visibility::Hidden | Visibility::Protected)\n",
                "    !linkage.is_module_local() && matches!(visibility, Visibility::Hidden | Visibility::Protected)\n",
            ),
            laws_edit(
                "src/lib.rs",
                "            matches!(kind, ObligationKindShape::TranslationValidation)\n",
                "            matches!(kind, ObligationKindShape::Termination)\n",
            ),
            laws_edit(
                "src/lib.rs",
                "            ObligationKindShape::Postcondition | ObligationKindShape::Custom\n",
                "            ObligationKindShape::Liveness | ObligationKindShape::Ownership\n",
            ),
            laws_edit("src/lib.rs", "        _ => true,\n", "        _ => false,\n"),
            laws_edit(
                "src/lib.rs",
                "            | ObligationKindShape::Liveness\n    )\n",
                "            | ObligationKindShape::MemorySafety\n    )\n",
            ),
        ),
        flips=(
            # module-locality inverted: local Hidden/Protected stop
            # contradicting and every other linkage's start to
            *cells("visibility_internal", ("hidden", "protected")),
            *cells("visibility_private", ("hidden", "protected")),
            "visibility_*_never_contradicts",
            "evidence_tv_translation_validation",
            "evidence_tv_termination",
            *cells("evidence_gamma", ("postcondition", "custom", "liveness", "ownership")),
            # every other evidence shape refused for every kind
            "evidence_*_unconstrained",
            "ambiguous_memory_safety",
            "ambiguous_liveness",
        ),
        scope=LOCAL_SCOPE,
        why="visibility with module-locality inverted, each constrained evidence row moved to "
        "a neighbour kind with the unconstrained rows refused, and one ambiguous kind swapped",
    ),
)


@dataclass
class Obligation:
    id: str
    kind: str
    status: str
    assurance: Optional[str]
    validation: Optional[str]
    reason: str


@dataclass
class FunctionResult:
    name: str  # path after the cargo-target prefix, e.g. trust_ir_laws::laws::foo
    verdict: str
    obligations: List[Obligation] = field(default_factory=list)

    @property
    def leaf(self) -> str:
        return self.name.rsplit("::", 1)[-1]

    def fully_proved(self) -> bool:
        return bool(self.obligations) and self.every_row_proved()

    def every_row_proved(self) -> bool:
        return all(
            o.status == "proved" and o.assurance == "Certified" and o.validation == "KernelRechecked"
            for o in self.obligations
        )


def law_functions(root: Path) -> List[str]:
    """Every `pub fn` of laws.rs, in file order. The file's contract is that a
    `pub fn` there IS a law; a `pub` item of any other kind is refused."""
    text = (root / LAWS_FILE).read_text(encoding="utf-8")
    if PUB_ITEM.search(text):
        raise SystemExit(f"{LAWS_FILE}: only `pub fn` laws may be public in this file")
    names = LAW_FN.findall(text)
    if not names:
        raise SystemExit(f"{LAWS_FILE}: no laws found")
    if len(set(names)) != len(names):
        raise SystemExit(f"{LAWS_FILE}: duplicate law names")
    return names


def expand_flips(m: Mutant, laws: Sequence[str]) -> List[str]:
    """The laws `m` names in `flips`, in file order: a plain entry names one
    law (which must exist), an entry containing `*` is a glob over law names
    (which must match at least one). Refuses an entry that names nothing."""
    out: Set[str] = set()
    law_set = set(laws)
    for entry in m.flips:
        if "*" in entry:
            hit = [law for law in laws if fnmatch.fnmatchcase(law, entry)]
            if not hit:
                raise SystemExit(f"mutant {m.name}: flips glob `{entry}` matches no law")
            out.update(hit)
        elif entry in law_set:
            out.add(entry)
        else:
            raise SystemExit(f"mutant {m.name} flips unknown law `{entry}`")
    return [law for law in laws if law in out]


def scoped_laws(m: Mutant, laws: Sequence[str]) -> List[str]:
    """The laws of `m`'s scope (the families it is held to), in file order."""
    return [law for law in laws if law.startswith(m.scope)]


def laws_without_a_mutant(laws: Sequence[str]) -> List[str]:
    """The laws no entry of MUTANTS names in `flips`, in file order. The lane's
    per-row claim ("proved under a refuting same-shape mutant") needs this to
    be empty: a wrapper whose body no mutant can flip is not shown to be
    about its table at all (`ensures result == false` over `false` proves)."""
    flipped: Set[str] = set()
    for m in MUTANTS:
        flipped.update(expand_flips(m, laws))
    return [law for law in laws if law not in flipped]


@dataclass(frozen=True)
class Wiring:
    """One law family's WIRING: the one call its laws' bodies make (`body`, a
    template over whitespace-normalized source) and the name that call gives
    a law (`name`). A `{X}` placeholder in `body` captures an enum VARIANT
    (an identifier), and the same `{X}` in `name` is that variant in
    snake_case, so a cell law's name is DERIVED from its body. `{ARGS}` in
    `body` captures a paren-free argument list, and then `name` is an
    `fnmatch` glob (the pre-2026-09-29 laws, whose names are the English
    laws' names). `table` names the table the call reaches, for messages."""

    name: str
    body: str
    table: str

    @property
    def table_fn(self) -> Optional[str]:
        """The table as a citable path (`Type::method` or a free `fn` name),
        or None for a family that calls no table (`u64_ge_is_transitive`).
        Gate 0 holds a `(proved-contract)` entry to citing exactly this path
        for every law it cites, so it must name the call `body` makes
        (tested: `test_every_wiring_table_names_the_call_its_body_makes`)."""
        return self.table if TABLE_PATH.fullmatch(self.table) else None


TABLE_PATH = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:::[A-Za-z_][A-Za-z0-9_]*)*")


# Every law's body is EXACTLY one of these calls. A batched mutant (every
# trust-ir table negated at once) flips a law whichever table it calls, so the
# flip alone cannot show a law is about ITS table; this list can: a law named
# `kernel_tier_pending` must be the body `ProofStatus::Pending.is_kernel_tier()`
# and nothing else, and a body calling another table or another cell derives
# another name and is refused before any run (`law_wiring_errors`).
WIRING: Tuple[Wiring, ...] = (
    Wiring("coverage_*", "coverage_supports({ARGS})", "coverage_supports"),
    Wiring("u64_ge_is_transitive", "if a<b{return true;}if b<c{return true;}a>=c", "(u64 `>=`, no table)"),
    Wiring("license_*", "license_admits_body({ARGS})", "license_admits_body"),
    Wiring("rc_{V}", "AllocOrigin::{V}.is_reference_counted()", "AllocOrigin::is_reference_counted"),
    Wiring("interposable_{V}", "Linkage::{V}.is_interposable()", "Linkage::is_interposable"),
    Wiring("module_local_{V}", "Linkage::{V}.is_module_local()", "Linkage::is_module_local"),
    Wiring(
        "contract_surface_linkage_{V}",
        "Linkage::{V}.requires_contract_surface()",
        "Linkage::requires_contract_surface",
    ),
    Wiring("discharged_tier_{V}", "ProofStatus::{V}.is_discharged_tier()", "ProofStatus::is_discharged_tier"),
    Wiring("kernel_tier_{V}", "ProofStatus::{V}.is_kernel_tier()", "ProofStatus::is_kernel_tier"),
    Wiring("atomic_load_{V}", "Ordering::{V}.is_legal_for_load()", "Ordering::is_legal_for_load"),
    Wiring("atomic_store_{V}", "Ordering::{V}.is_legal_for_store()", "Ordering::is_legal_for_store"),
    Wiring("cc_abi_surface_{V}", "CallingConv::{V}.is_abi_surface()", "CallingConv::is_abi_surface"),
    Wiring("tag_abi_surface_{V}", "EnumTagRepr::{V}.is_abi_surface()", "EnumTagRepr::is_abi_surface"),
    Wiring(
        "hv_fail_closed_{V}",
        "HardwareVectorContractStatus::{V}.fail_closed()",
        "HardwareVectorContractStatus::fail_closed",
    ),
    Wiring(
        "backed_by_{K}",
        "ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::{K})",
        "ExternRefSite::admits_shape",
    ),
    Wiring(
        "inherited_{K}",
        "ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::{K})",
        "ExternRefSite::admits_shape",
    ),
    Wiring("{S}_admits_nothing", "ExternRefSite::{S}.admits_shape(kind)", "ExternRefSite::admits_shape"),
    Wiring(
        "grounded_contract_kind_{K}",
        "ObligationKindShape::{K}.is_grounded_contract_kind()",
        "ObligationKindShape::is_grounded_contract_kind",
    ),
    Wiring(
        "free_var_proved_{K}",
        "ObligationKindShape::{K}.free_var_is_proved()",
        "ObligationKindShape::free_var_is_proved",
    ),
    Wiring("assert_class_{K}", "ObligationKindShape::{K}.is_assert_class()", "ObligationKindShape::is_assert_class"),
    Wiring("terminator_{V}", "InstShape::{V}.is_terminator()", "InstShape::is_terminator"),
    Wiring(
        "borrow_permission_{V}",
        "InstShape::{V}.uses_borrow_permissions()",
        "InstShape::uses_borrow_permissions",
    ),
    Wiring(
        "visibility_{L}_{V}",
        "visibility_contradicts_linkage(Linkage::{L},Visibility::{V})",
        "visibility_contradicts_linkage",
    ),
    Wiring(
        "visibility_{L}_never_contradicts",
        "visibility_contradicts_linkage(Linkage::{L},visibility)",
        "visibility_contradicts_linkage",
    ),
    Wiring(
        "evidence_tv_{K}",
        "evidence_admits_kind(ProofEvidenceShape::TranslationValidation,ObligationKindShape::{K})",
        "evidence_admits_kind",
    ),
    Wiring(
        "evidence_gamma_{K}",
        "evidence_admits_kind(ProofEvidenceShape::GammaCrownBound,ObligationKindShape::{K})",
        "evidence_admits_kind",
    ),
    Wiring(
        "evidence_{E}_unconstrained",
        "evidence_admits_kind(ProofEvidenceShape::{E},kind)",
        "evidence_admits_kind",
    ),
    Wiring(
        "ambiguous_{K}",
        "proof_ref_kind_is_ambiguous(ObligationKindShape::{K})",
        "proof_ref_kind_is_ambiguous",
    ),
    # The fresh-id rule's three u32 tables (trust-ir value.rs, r11 R1). Each
    # law is named by the ROW it states, and the ratification cites each row
    # by its law, so each law is wired to its EXACT call: the row over every
    # input passes its own parameters, a boundary row its own constants. An
    # `{ARGS}` glob would bind no row to its name (measured 2026-10-01 by
    # review: three laws re-pointed at other arguments of their own table
    # passed WIRING and gate 13).
    Wiring("fresh_successor_iff_below_max", "fresh_id_has_successor(id)", "fresh_id_has_successor"),
    Wiring("fresh_successor_absent_at_max", "fresh_id_has_successor(4294967295)", "fresh_id_has_successor"),
    Wiring("fresh_successor_present_below_max", "fresh_id_has_successor(4294967294)", "fresh_id_has_successor"),
    Wiring("fresh_successor_present_at_zero", "fresh_id_has_successor(0)", "fresh_id_has_successor"),
    Wiring("fresh_run_fits_iff_within_room", "fresh_run_fits(extra,room)", "fresh_run_fits"),
    Wiring("fresh_run_fits_single_id_anywhere", "fresh_run_fits(0,room)", "fresh_run_fits"),
    Wiring("fresh_run_fits_whole_space", "fresh_run_fits(4294967295,4294967295)", "fresh_run_fits"),
    Wiring("fresh_run_fits_refused_past_max", "fresh_run_fits(1,0)", "fresh_run_fits"),
    Wiring("fresh_below_iff_less", "fresh_id_below(id,end_exclusive)", "fresh_id_below"),
    Wiring("fresh_below_refuses_the_bound", "fresh_id_below(3758096384,3758096384)", "fresh_id_below"),
    Wiring(
        "fresh_below_admits_the_last_id_under_the_bound",
        "fresh_id_below(3758096383,3758096384)",
        "fresh_id_below",
    ),
)

PLACEHOLDER = re.compile(r"\{([A-Z]+)\}")


def snake(variant: str) -> str:
    """`SysV64` -> `sys_v64`, `CMalloc` -> `c_malloc`, `GEP` -> `gep`: the
    law-name spelling of an enum variant."""
    return re.sub(r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])", "_", variant).lower()


def normalize_body(body: str) -> str:
    """Whitespace-insensitive, token-preserving form of a law body: runs of
    whitespace collapse, whitespace next to punctuation goes, and a trailing
    comma before `)` (trustfmt's multi-line call) is dropped."""
    s = re.sub(r"\s+", " ", body).strip()
    s = re.sub(r" ?([^\w ]) ?", r"\1", s)
    return s.replace(",)", ")")


def wiring_regex(w: Wiring) -> "re.Pattern[str]":
    out = []
    pos = 0
    for m in PLACEHOLDER.finditer(w.body):
        out.append(re.escape(w.body[pos : m.start()]))
        if m.group(1) == "ARGS":
            out.append(r"(?P<ARGS>[^()]*)")
        else:
            out.append(rf"(?P<{m.group(1)}>[A-Z][A-Za-z0-9]*)")
        pos = m.end()
    out.append(re.escape(w.body[pos:]))
    return re.compile("".join(out))


def law_bodies(text: str) -> List[Tuple[str, str]]:
    """`(name, body)` of every law of a laws.rs text: the body is the source
    between the law's column-0 `{` line and its column-0 `}` line."""
    out: List[Tuple[str, str]] = []
    for name, start, end in law_blocks(text):
        block = text[start:end]
        lines = block.splitlines()
        try:
            open_at = lines.index("{")
        except ValueError:
            raise SystemExit(f"{LAWS_FILE}: law `{name}` has no column-0 opening brace")
        out.append((name, "\n".join(lines[open_at + 1 : -1])))
    return out


def law_wiring_errors(text: str) -> List[str]:
    """Every law whose body is not EXACTLY the one call its name spells: the
    body must match exactly one WIRING entry, and the name that entry derives
    from the body (the family, and each captured variant in snake_case) must
    be the law's name. Empty = every law calls its own table at its own cell.

    This is what makes a batched mutant's flip evidence about the RIGHT
    table: a law body that called another table (or another cell of its
    own) would still flip when every table is negated at once (measured
    2026-09-29 by review: `kernel_tier_pending` re-pointed at
    `is_discharged_tier` and `terminator_bin_op` at `is_reference_counted`
    both proved and both flipped, and the gate passed)."""
    return [error for _, _, error in law_wiring(text) if error is not None]


def law_wiring(text: str) -> List[Tuple[str, Optional[Wiring], Optional[str]]]:
    """`(law, family, error)` for every law of a laws.rs text, in file order:
    the WIRING family its body is the one call of when its name is the one
    that family derives (`error` None), else no family and the reason
    (`law_wiring_errors` is the list of reasons)."""
    out: List[Tuple[str, Optional[Wiring], Optional[str]]] = []
    compiled = [(w, wiring_regex(w)) for w in WIRING]
    for name, body in law_bodies(text):
        norm = normalize_body(body)
        hits = [(w, m) for w, rx in compiled for m in [rx.fullmatch(norm)] if m]
        if not hits:
            out.append((name, None, (
                f"{name}: body `{norm}` is not the one-call shape of any family in WIRING "
                "(a law is exactly one call of its table at the cell its name spells)"
            )))
            continue
        if len(hits) > 1:
            out.append((name, None, f"{name}: body `{norm}` matches {len(hits)} WIRING entries; they must be disjoint"))
            continue
        w, m = hits[0]
        if "{ARGS}" in w.body:
            if not fnmatch.fnmatchcase(name, w.name):
                out.append((name, None, f"{name}: its body calls `{w.table}`, whose laws are named `{w.name}`"))
            else:
                out.append((name, w, None))
            continue
        expected = w.name.format(**{k: snake(v) for k, v in m.groupdict().items()})
        if expected != name:
            out.append((name, None, (
                f"{name}: its body calls `{w.table}` as `{norm}`, which is the law `{expected}` "
                "(a law must call its own table at the cell its name spells)"
            )))
        else:
            out.append((name, w, None))
    return out


# --- Cell completeness ------------------------------------------------------
# The source comments of the tables say "PROVED, every cell: `laws::rc_*`",
# and a `(proved-contract)` entry may cite a family by glob. Both are claims
# about EVERY cell, and a glob names only the laws that exist: before this
# rule a new variant (a 17th `ObligationKind`, whose `matches!` table is then
# silently false there) or a deleted law left every gate green (measured
# 2026-09-30 by review: `ambiguous_custom` deleted, gate 13 PASS with 312
# laws). So gate 13 enumerates each table's domain from the source and
# refuses, before any run, a CELL TABLE with a cell no law states.
#
# A law is a CELL LAW when every operand of its one call — the receiver of a
# `Type::Variant.method(..)` call included — is a unit variant
# (`Linkage::Weak`, one variant) or a by-value parameter of an enum type
# (`kind: ObligationKindShape`, every variant). A table every one of whose
# laws is a cell law is a CELL TABLE; its domain is the product of its operand
# enums' variants, read from the enum definitions in the crates a law can call
# (`CRATE_DIRS`, comments and literals masked). A table with a law over a
# payload (`coverage_supports`'s `u64` depths, the fresh-id tables' `u32`
# ids) has no finite domain: it is not enumerated, and its rows are exactly
# its named laws — for the fresh-id tables, the row over every input and each
# boundary constant (`u32::MAX`, the reserved bound). Such a table leaves the
# rule only BY NAME, in PAYLOAD_TABLES: any other table with a law that is not
# a cell law is refused, so a law that stops parsing as one (a parameter
# retyped, a payload added) cannot silently take its table out of the rule.
PAYLOAD_TABLES: Tuple[str, ...] = (
    "coverage_supports",
    # the fresh-id rule's tables range over every `u32` (r11 R1)
    "fresh_id_has_successor",
    "fresh_run_fits",
    "fresh_id_below",
)
CELL_CALL = re.compile(
    r"(?:(?P<recv>[A-Za-z_]\w*(?:::[A-Za-z_]\w*)?)\.[A-Za-z_]\w*|[A-Za-z_]\w*(?:::[A-Za-z_]\w*)*)"
    r"\((?P<args>[^(){}]*)\)"
)
VARIANT_OPERAND = re.compile(r"([A-Za-z_]\w*)::([A-Za-z_]\w*)")
PARAM_OPERAND = re.compile(r"[a-z_]\w*")
ENUM_TYPE = re.compile(r"(?:[A-Za-z_]\w*::)*([A-Z]\w*)")
LAW_SIGNATURE = re.compile(r"^pub fn (\w+)\((?P<params>[^)]*)\)", re.M)
IDENT = re.compile(r"[A-Za-z_]\w*")


@dataclass(frozen=True)
class EnumDefinition:
    """One `enum NAME { .. }` (or `variant_shape!`'s `enum NAME for DATA { .. }`)
    in the source of a crate a law can call: where, and its variants in
    declaration order."""

    path: str
    variants: Tuple[str, ...]


def enum_variant_names(body: str) -> Tuple[str, ...]:
    """The variant names of a MASKED enum body (the text between its braces):
    each top-level comma-separated piece's first identifier, once its
    attributes (`#[..]`), payload (`(..)` / `{..}`) and discriminant (`= ..`)
    are dropped. Bracket depth, not a Rust parser: the body is masked first,
    so no comment or literal can open a bracket."""
    names: List[str] = []
    depth = 0
    piece: List[str] = []

    def flush() -> None:
        head = "".join(piece).split("=", 1)[0].replace("#", " ")
        m = IDENT.search(head)
        if m:
            names.append(m.group(0))
        piece.clear()

    for ch in body:
        if ch in "([{":
            depth += 1
            continue
        if ch in ")]}":
            depth -= 1
            continue
        if depth:
            continue
        if ch == ",":
            flush()
        else:
            piece.append(ch)
    flush()
    return tuple(names)


def enum_definitions(root: Path, names: Set[str]) -> Tuple[Dict[str, List[EnumDefinition]], List[str]]:
    """Every definition of each enum in `names` in the source of the crates a
    law can call (`CRATE_DIRS`), and the errors met reading them. Never
    raises. A file that cannot be read is an error, never a silent skip: a
    definition it holds could be the one that makes a table incomplete."""
    found: Dict[str, List[EnumDefinition]] = {name: [] for name in names}
    errors: List[str] = []
    if not names:
        return found, errors
    item = re.compile(
        r"\benum\s+(" + "|".join(re.escape(n) for n in sorted(names)) + r")(?:\s+for\s+[A-Za-z_]\w*)?\s*\{"
    )
    for crate_dir in sorted(CRATE_DIRS.values()):
        for path in sorted((root / crate_dir / "src").rglob("*.rs")):
            rel = path.relative_to(root).as_posix()
            try:
                text = path.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError) as err:
                errors.append(f"{rel}: unreadable while enumerating the cell tables' enums: {err}")
                continue
            if not item.search(text):
                continue
            masked = mask_non_code(text)
            for m in item.finditer(masked):
                depth, end = 1, m.end()
                while depth and end < len(masked):
                    if masked[end] in "([{":
                        depth += 1
                    elif masked[end] in ")]}":
                        depth -= 1
                    end += 1
                if depth:
                    errors.append(f"{rel}: `enum {m.group(1)}` has no closing brace")
                    continue
                found[m.group(1)].append(EnumDefinition(rel, enum_variant_names(masked[m.end() : end - 1])))
    return found, errors


def law_parameters(text: str) -> Dict[str, Dict[str, str]]:
    """`{law: {parameter: type}}` of a laws.rs text, from each signature."""
    out: Dict[str, Dict[str, str]] = {}
    for m in LAW_SIGNATURE.finditer(text):
        params: Dict[str, str] = {}
        for param in m.group("params").split(","):
            if ":" in param:
                name, ty = param.split(":", 1)
                params[name.strip()] = ty.strip()
        out[m.group(1)] = params
    return out


# An operand of a cell law: ("variant", Type, Variant) or ("all", Type).
Operand = Tuple[str, ...]


def cell_operands(norm: str, params: Dict[str, str]) -> Optional[List[Operand]]:
    """The operands of a normalized law body that is ONE call over unit
    variants and enum-typed parameters, receiver first; None for any other
    body (a payload, a `u64`, a literal, no call)."""
    m = CELL_CALL.fullmatch(norm)
    if not m:
        return None
    raw = ([m.group("recv")] if m.group("recv") else []) + [a for a in m.group("args").split(",") if a]
    operands: List[Operand] = []
    for operand in raw:
        variant = VARIANT_OPERAND.fullmatch(operand)
        if variant:
            operands.append(("variant", variant.group(1), variant.group(2)))
        elif PARAM_OPERAND.fullmatch(operand) and ENUM_TYPE.fullmatch(params.get(operand, "")):
            operands.append(("all", ENUM_TYPE.fullmatch(params[operand]).group(1)))
        else:
            return None
    return operands


CellRows = Dict[str, List[Tuple[str, Wiring, Optional[List[Operand]]]]]


def cell_rows(text: str, wiring: Sequence[Tuple[str, Optional[Wiring], Optional[str]]]) -> CellRows:
    """`{table: [(law, family, operands)]}` over the well-wired laws that call
    a table; `operands` is None for a law that is not a cell law."""
    params = law_parameters(text)
    bodies = dict(law_bodies(text))
    rows: CellRows = {}
    for name, w, error in wiring:
        if w is None or error is not None or w.table_fn is None:
            continue
        operands = cell_operands(normalize_body(bodies[name]), params.get(name, {}))
        rows.setdefault(w.table_fn, []).append((name, w, operands))
    return rows


def cell_tables_of(rows: CellRows) -> CellRows:
    """The CELL TABLES: every law of the table is a cell law."""
    return {t: laws for t, laws in rows.items() if all(ops is not None for _, _, ops in laws)}


def cell_enum_names(text: str) -> Set[str]:
    """The enums the cell tables of a laws.rs text range over."""
    tables = cell_tables_of(cell_rows(text, law_wiring(text)))
    return {op[1] for laws in tables.values() for _, _, ops in laws for op in ops or []}


@dataclass(frozen=True)
class CellReading:
    """What `cell_completeness` read of a laws file: the cell tables held
    complete, the refusals, each CELL LAW's operands (`law -> operands`, its
    receiver first: `("variant", Type, Variant)` or `("all", Type)`), and the
    variants of each operand enum that has exactly one definition (`enum ->
    variants`). Gate 0 reads the last two (rule E5: a variant an entry
    names beside a law's verdict must be a cell of a law it gives one)."""

    complete: Tuple[str, ...]
    errors: List[str]
    cells: Dict[str, Tuple[Operand, ...]]
    domains: Dict[str, Tuple[str, ...]]


def cell_completeness(
    root: Path, text: str, wiring: Sequence[Tuple[str, Optional[Wiring], Optional[str]]]
) -> CellReading:
    """The cell tables held complete and the errors (with what was read on
    the way, `CellReading`): a refusal for each CELL TABLE (the comment above
    `CELL_CALL`) whose domain has a cell no law states, whose laws disagree
    on its operand types or name a variant its enum lacks, and for each
    operand enum that cannot be enumerated (no definition in the source a law
    can call, or two)."""
    rows = cell_rows(text, wiring)
    tables = cell_tables_of(rows)
    law_cells = {name: tuple(ops) for laws in tables.values() for name, _, ops in laws if ops is not None}
    enums, errors = enum_definitions(root, {op[1] for laws in tables.values() for _, _, ops in laws for op in ops or []})
    enum_domains = {ty: defs[0].variants for ty, defs in enums.items() if len(defs) == 1}
    for table, laws in sorted(rows.items()):
        if table in PAYLOAD_TABLES and table in tables:
            errors.append(f"`{table}` is named in PAYLOAD_TABLES but every law of it is a cell law: take it off the list, so its cells are held")
        elif table not in PAYLOAD_TABLES and table not in tables:
            others = [name for name, _, ops in laws if ops is None]
            errors.append(
                f"cell table `{table}` has laws that are not one call over unit variants and enum-typed "
                f"parameters: {others}. A table over enums is held to a law at every cell; only a table over "
                "payloads, named in PAYLOAD_TABLES, is not enumerated"
            )
    users: Dict[str, List[str]] = {}
    for table, laws in tables.items():
        for ty in sorted({op[1] for _, _, ops in laws for op in ops or []}):
            users.setdefault(ty, []).append(table)
    unenumerable = {ty for ty in users if len(enums.get(ty, [])) != 1}
    for ty in sorted(unenumerable):
        where = ", ".join(d.path for d in enums.get(ty, [])) or "none"
        errors.append(
            f"cannot enumerate `{ty}`, an operand of the cell table(s) {sorted(users[ty])}: "
            f"{len(enums.get(ty, []))} definitions of `enum {ty}` under "
            f"{', '.join(sorted(d.as_posix() for d in CRATE_DIRS.values()))} ({where}); a cell table is held "
            "to a law at every cell of its operand enums, so each must be defined exactly once there"
        )
    complete: List[str] = []
    for table, laws in sorted(tables.items()):
        shapes = {tuple(op[1] for op in ops or []) for _, _, ops in laws}
        if len(shapes) != 1:
            errors.append(f"cell table `{table}`: its laws disagree on its operand types: {sorted(shapes)}")
            continue
        (axes,) = shapes
        if unenumerable.intersection(axes):
            continue
        domains = [enums[ty][0].variants for ty in axes]
        covered: Set[Tuple[str, ...]] = set()
        stray: List[str] = []
        for name, _, ops in laws:
            choices: List[Tuple[str, ...]] = []
            for op, domain in zip(ops or [], domains):
                if op[0] == "all":
                    choices.append(domain)
                elif op[2] in domain:
                    choices.append((op[2],))
                else:
                    stray.append(f"{name} (`{op[1]}::{op[2]}` is no variant of `enum {op[1]}`)")
                    choices.append(())
            covered.update(product_of(choices))
        cells = product_of(domains)
        missing = [cell for cell in cells if cell not in covered]
        if stray:
            errors.append(f"cell table `{table}`: laws over no cell of it: {stray}")
        if missing:
            shown = ", ".join(
                "(" + ", ".join(f"{ty}::{v}" for ty, v in zip(axes, cell)) + ")" + law_hint(cell, laws)
                for cell in missing[:12]
            )
            more = f" and {len(missing) - 12} more" if len(missing) > 12 else ""
            errors.append(
                f"cell table `{table}` (families {sorted({w.name for _, w, _ in laws})}) has no law at "
                f"{len(missing)} of its {len(cells)} cells: {shown}{more}. Gate 13 holds a cell table to a "
                "law at every cell (a `PROVED, every cell` comment and a glob over its family both mean every "
                "cell), so add the law, and a mutant `flips` entry that names it"
            )
        if not stray and not missing:
            complete.append(table)
    return CellReading(tuple(complete), errors, law_cells, enum_domains)


def product_of(domains: Sequence[Tuple[str, ...]]) -> List[Tuple[str, ...]]:
    cells: List[Tuple[str, ...]] = [()]
    for domain in domains:
        cells = [cell + (v,) for cell in cells for v in domain]
    return cells


def law_hint(cell: Tuple[str, ...], laws: Sequence[Tuple[str, Wiring, Optional[List[Operand]]]]) -> str:
    """` — e.g. `pub fn rc_new_heap``: the law a family of the table spells
    for exactly that cell (each operand of its template a `{X}` placeholder
    or that cell's own fixed variant), else empty."""
    for w in dict.fromkeys(w for _, w, _ in laws):
        placeholders = PLACEHOLDER.findall(w.body)
        template = cell_operands(normalize_body(PLACEHOLDER.sub(r"\1", w.body)), {})
        if not placeholders or template is None or len(template) != len(cell):
            continue
        values: Dict[str, str] = {}
        for op, v in zip(template, cell):
            if op[2] in placeholders:
                values[op[2]] = v
            elif op[2] != v:
                break
        else:
            if set(values) == set(placeholders):
                return f" — e.g. `pub fn {w.name.format(**{k: snake(v) for k, v in values.items()})}`"
    return ""


@dataclass(frozen=True)
class Holding:
    """What gate 13 HOLDS of a laws file before any run — THE statement of its
    pre-run rules, which `main` refuses on and gate 0
    (`scripts/check_enforcement_links.py`, class `proved-contract`) reads, so
    the rule a law must meet to be cited as proved is stated once.

    `laws` is every `pub fn` of the file, in file order; `tables` maps each
    well-wired law to the table its WIRING family calls (`Wiring.table_fn`,
    None for a family that calls no table); `cell_tables` are the tables held
    to a law at every cell (`cell_completeness`: every table not named in
    PAYLOAD_TABLES); `errors` are the pre-run refusals. A law is
    HELD only when there are none: gate 13 refuses to run on a file with one,
    so it proves no law of it, not merely the offending one. HELD is what
    gate 13 checks before it runs — the law exists, is exactly one call of
    its own table at the cell its name spells, some mutant's `flips` names
    it, and every cell of every cell table has a law — never that a run
    passed: the run is gate 13 itself, a standing gate that fails where the
    verified lane is missing.

    What gate 0's rule E5 (an entry says what its statement says) reads,
    computed here once: `verdicts`, each law's verdict read from its
    `ensures` (`law_verdicts`, one of `ENSURES_SHAPES`); `families`, each
    well-wired law's WIRING family (`Wiring.name`); `cells`, each cell law's
    operands; and `domains`, each operand enum's variants (`CellReading`)."""

    laws: Tuple[str, ...]
    tables: Dict[str, Optional[str]]
    errors: Tuple[str, ...]
    cell_tables: Tuple[str, ...] = ()
    verdicts: Dict[str, "Verdict"] = field(default_factory=dict)
    families: Dict[str, str] = field(default_factory=dict)
    cells: Dict[str, Tuple[Operand, ...]] = field(default_factory=dict)
    domains: Dict[str, Tuple[str, ...]] = field(default_factory=dict)

    @property
    def held(self) -> Tuple[str, ...]:
        return () if self.errors else self.laws


def holding(root: Path) -> Holding:
    """Gate 13's pre-run rules over `root`'s laws file (see `Holding`). Never
    raises: an unreadable file, a `pub` item that is not a law, a mutant
    whose `flips` names nothing or reaches outside its scope, a law no
    mutant names, a law not wired to its own table, a law whose contract is
    not one `ensures` of `ENSURES_SHAPES`, and a cell table with a cell no
    law states are each an error."""
    try:
        laws = law_functions(root)
        text = (root / LAWS_FILE).read_text(encoding="utf-8")
    except OSError as err:
        return Holding((), {}, (f"{LAWS_FILE}: {err.strerror or err}",))
    except SystemExit as err:
        return Holding((), {}, (str(err.code),))
    errors: List[str] = []
    try:
        for m in MUTANTS:
            outside = [f for f in expand_flips(m, laws) if not f.startswith(m.scope)]
            if outside:
                errors.append(f"mutant {m.name} flips laws outside its scope: {outside}")
        unrefuted = laws_without_a_mutant(laws)
    except SystemExit as err:
        errors.append(str(err.code))
        unrefuted = []
    if unrefuted:
        errors.append(
            "every law must be flipped by at least one mutant (a law no mutant refutes could "
            f"stop calling its table and still prove); none names: {unrefuted}"
        )
    try:
        wiring = law_wiring(text)
    except SystemExit as err:  # a law block without its column-0 braces
        return Holding(tuple(laws), {}, tuple(errors) + (str(err.code),))
    miswired = [error for _, _, error in wiring if error is not None]
    if miswired:
        errors.append(
            "every law must be exactly one call of its own table at the cell its name spells "
            "(a batched mutant flips a law whichever table it calls):\n  " + "\n  ".join(miswired)
        )
    tables = {name: w.table_fn for name, w, error in wiring if w is not None and error is None}
    families = {name: w.name for name, w, error in wiring if w is not None and error is None}
    verdicts, unreadable = law_verdicts(text)
    errors.extend(unreadable)
    cells = cell_completeness(root, text, wiring)
    errors.extend(cells.errors)
    return Holding(tuple(laws), tables, tuple(errors), cells.complete, verdicts, families, cells.cells, cells.domains)


# --- Verdicts ---------------------------------------------------------------
# Gate 0 (`scripts/check_enforcement_links.py`, rule E5) holds a
# `(proved-contract)` entry to giving each law it cites the verdict the law's
# `ensures` states, and reads that verdict from HERE, so its shapes are stated
# once. Every law's contract is exactly one `ensures` clause of one of these
# shapes (whitespace-normalized); any other contract is a pre-run error, and
# then gate 13 holds no law. A `<relation>` is the text between the outer
# parentheses, which must balance.
ENSURES_SHAPES: Tuple[Tuple[str, str], ...] = (
    ("true", "result"),
    ("false", "result == false"),
    ("relation", "result == (<relation>)"),
)
CONTRACT_KEYWORD = re.compile(r"\b(?:requires|ensures|decreases|invariant|modifies)\b")
LAW_HEADER = re.compile(r"pub fn (?P<name>\w+)\s*\((?P<params>[^)]*)\)\s*->\s*bool\s+ensures\s+(?P<clause>.+)", re.S)


@dataclass(frozen=True)
class Verdict:
    """A law's verdict: `kind` is `true`, `false` or `relation` (the first
    word of its `ENSURES_SHAPES` row), and `relation` the relation's text
    for the last."""

    kind: str
    relation: str = ""

    def __str__(self) -> str:
        return f"true exactly when {self.relation}" if self.kind == "relation" else self.kind

    @property
    def ensures(self) -> str:
        """The `ensures` clause this verdict was read from."""
        shape = dict(ENSURES_SHAPES)[self.kind]
        return shape.replace("<relation>", self.relation)


def balanced(text: str) -> bool:
    """Do `text`'s parentheses balance without ever closing one not open?"""
    depth = 0
    for ch in text:
        depth += {"(": 1, ")": -1}.get(ch, 0)
        if depth < 0:
            return False
    return depth == 0


def ensures_verdict(clause: str) -> Optional[Verdict]:
    """The verdict of one `ensures` clause, or None for a shape outside
    `ENSURES_SHAPES`."""
    clause = " ".join(clause.split())
    if clause == dict(ENSURES_SHAPES)["true"]:
        return Verdict("true")
    if clause == dict(ENSURES_SHAPES)["false"]:
        return Verdict("false")
    prefix = "result == ("
    if clause.startswith(prefix) and clause.endswith(")"):
        relation = clause[len(prefix) : -1].strip()
        if relation and balanced(relation) and not CONTRACT_KEYWORD.search(relation):
            return Verdict("relation", relation)
    return None


def law_verdicts(text: str) -> Tuple[Dict[str, Verdict], List[str]]:
    """`({law: verdict}, errors)` of a laws.rs text: each law's contract,
    read from its signature through the line before its column-0 `{`, must
    be exactly one `ensures` clause of `ENSURES_SHAPES` (no `requires`, no
    second clause), and its verdict is read from it. Never raises."""
    verdicts: Dict[str, Verdict] = {}
    errors: List[str] = []
    shapes = ", ".join(f"`ensures {shape}`" for _, shape in ENSURES_SHAPES)
    try:
        blocks = law_blocks(text)
    except SystemExit as err:
        return verdicts, [str(err.code)]
    for name, start, end in blocks:
        lines = text[start:end].splitlines()
        signature = next((i for i, line in enumerate(lines) if LAW_FN.match(line)), None)
        opening = lines.index("{") if "{" in lines else None
        header = " ".join(" ".join(lines[signature:opening]).split()) if signature is not None and opening is not None else ""
        m = LAW_HEADER.fullmatch(header)
        verdict = None
        if m and m.group("name") == name and not CONTRACT_KEYWORD.search(m.group("clause")):
            verdict = ensures_verdict(m.group("clause"))
        if verdict is None:
            contract = header.split("-> bool", 1)[1].strip() if "-> bool" in header else header
            errors.append(
                f"{name}: its contract `{contract}` is not exactly one of {shapes} "
                "(gate 0 reads each law's verdict from its `ensures`, rule E5)"
            )
            continue
        verdicts[name] = verdict
    return verdicts, errors


def law_blocks(text: str) -> List[Tuple[str, int, int]]:
    """`(name, start, end)` of every law in a laws.rs text: from the first line
    of the `///` doc comment directly above `pub fn <name>(` (or that line)
    through the next line that is exactly `}` — the file's formatting
    contract (trustfmt: signature, `ensures`, a column-0 `{` ... `}` body)."""
    lines = text.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    blocks: List[Tuple[str, int, int]] = []
    i = 0
    while i < len(lines):
        m = LAW_FN.match(lines[i])
        if not m:
            i += 1
            continue
        first = i
        while first > 0 and lines[first - 1].lstrip().startswith("///"):
            first -= 1
        j = i
        while j < len(lines) and lines[j].rstrip("\n") != "}":
            j += 1
        if j == len(lines):
            raise SystemExit(f"{LAWS_FILE}: law `{m.group(1)}` has no column-0 closing brace")
        blocks.append((m.group(1), offsets[first], offsets[j + 1]))
        i = j + 1
    return blocks


def scope_laws_source(text: str, keep: Set[str]) -> str:
    """laws.rs with every law outside `keep` removed (its doc comment too)."""
    out = []
    pos = 0
    for name, start, end in law_blocks(text):
        if name not in keep:
            out.append(text[pos:start])
            pos = end
    out.append(text[pos:])
    return "".join(out)


def parse_report(path: Path) -> Dict[str, FunctionResult]:
    """Per-function results of a `--report-dir` report.json, keyed by the path
    after the `cargo-target(...)::` prefix. Only the PRIMARY unit's functions
    of this crate are kept; a dependency-role row would not be about the laws."""
    return parse_report_data(json.loads(path.read_text(encoding="utf-8")))


def parse_report_data(data: dict) -> Dict[str, FunctionResult]:
    """`parse_report` over an already-loaded report."""
    out: Dict[str, FunctionResult] = {}
    for entry in data.get("functions", []):
        name = primary_function(entry.get("function", ""))
        if name is None:
            continue
        summary = entry.get("summary", {})
        fr = FunctionResult(name=name, verdict=str(summary.get("verdict", "?")))
        for ob in entry.get("obligations", []):
            outcome = ob.get("outcome", {}) or {}
            strength = outcome.get("strength", {}) or {}
            grade = strength.get("grade", {}) or {}
            fr.obligations.append(
                Obligation(
                    id=str(ob.get("obligation_id", "")),
                    kind=str(ob.get("kind", "")),
                    status=str(outcome.get("status", "")),
                    assurance=strength.get("assurance"),
                    validation=grade.get("validation"),
                    reason=str(outcome.get("reason", "") or ""),
                )
            )
        out[name] = fr
    return out


def by_leaf(results: Dict[str, FunctionResult]) -> Dict[str, FunctionResult]:
    """Index by bare name exactly the functions the lane is about: a law
    (`trust_ir_laws::laws::<name>`) or a top-level subject
    (`trust_ir_laws::<name>`). Trait-impl paths (`<T as Clone>::clone`, one
    per derive) and inherent methods (`GateShape::name`) are neither, and are
    skipped rather than allowed to collide."""
    idx: Dict[str, FunctionResult] = {}
    for fr in results.values():
        parts = fr.name.split("::")
        if fr.name.startswith("<") or parts[0] != CRATE_IDENT:
            continue
        if len(parts) == 2:
            key = parts[1]
        elif len(parts) == 3 and parts[1] == "laws":
            key = parts[2]
        else:
            continue
        if key in idx:
            raise SystemExit(f"report names `{key}` twice: {idx[key].name} and {fr.name}")
        idx[key] = fr
    return idx


def check_rows(
    results: Dict[str, FunctionResult],
    laws: Sequence[str],
    expect_proved: Set[str],
    expect_refuted: Set[str],
    output: str,
) -> List[str]:
    """The per-row verdict of one run. Returns the list of failures (empty =
    pass). `expect_proved` must be fully proved (Certified, KernelRechecked);
    `expect_refuted` must NOT be fully proved and must be named by a
    `refuted obligation` line of the terminal output."""
    failures: List[str] = []
    idx = by_leaf(results)
    refuted_lines = [line for line in output.splitlines() if REFUTED_LINE.search(line)]
    for name in expect_proved:
        fr = idx.get(name)
        if fr is None:
            failures.append(f"{name}: absent from the report (not verified at all)")
        elif not fr.fully_proved():
            rows = "; ".join(
                f"{o.kind}={o.status}/{o.assurance}/{o.validation}" for o in fr.obligations
            ) or "no obligations"
            failures.append(f"{name}: expected every row proved+Certified+KernelRechecked, got {rows}")
    # A missing EXPECTED refutation is NOT JUDGED, never a pass: on the
    # installed seal a budget stop can both hide a refutation and forge a
    # proof (see `not_judged`), so its absence says nothing either way.
    for name in expect_refuted:
        fr = idx.get(name)
        if fr is None:
            failures.append(f"{NOT_JUDGED} expected refutation missing: {name} is absent from the mutant report")
            continue
        if fr.fully_proved():
            failures.append(
                f"{NOT_JUDGED} expected refutation missing: {name} is still proved under the mutation"
            )
        if not any(f"__{name}:" in line for line in refuted_lines):
            failures.append(
                f"{NOT_JUDGED} expected refutation missing: no `refuted obligation` line names "
                f"{name} — not proved, but not REFUTED either (an inliner decline is "
                "fail-closed unknown, not a control)"
            )
    for name in laws:
        if name not in idx:
            failures.append(f"{name}: law missing from the report")
    return failures


def check_subjects(results: Dict[str, FunctionResult], subjects: Sequence[str]) -> List[str]:
    """Every subject TABLE was verified in the primary unit and every row it
    has is proved + Certified + KernelRechecked. Unlike a law, a table may
    carry no row at all (a `matches!` with no reachable panic: verdict
    `NoObligations`, measured on `evidence_admits_kind` and
    `proof_ref_kind_is_ambiguous`) — its correctness is its laws' business;
    this check only sees an edit that breaks the table's OWN verification."""
    failures: List[str] = []
    idx = by_leaf(results)
    for name in subjects:
        fr = idx.get(name)
        if fr is None:
            failures.append(f"{name}: subject table absent from the report (not verified at all)")
        elif not fr.every_row_proved():
            rows = "; ".join(f"{o.kind}={o.status}/{o.assurance}/{o.validation}" for o in fr.obligations)
            failures.append(f"{name}: subject table has a row not proved+Certified+KernelRechecked: {rows}")
    return failures


# ---------------------------------------------------------------------------
# THE BUILD-SCRIPT PREMISE — what every verdict of this lane rests on uncontained
# ---------------------------------------------------------------------------
#
# `targo trust check` runs every build script of the lane's unit graph outside
# the proof channel: uncontained, as the same uid (Trust blocker B5; the
# premise is P-CORESIDENT). The report states each such execution as an
# `assumptions` row tagged `build-execution-scope` ("proof is conditional on
# this exact execution unit's correctness"), and lists the unit in its
# `cargo_proof_inventory` with `proof_unit_mode == "run-custom-build"`.
# So every law this lane proves, and every mutant it refutes, rests on those
# scripts. The rule: the build-script executions of every JUDGED run EQUAL the
# committed list `BUILD_SCRIPTS`, both report views agree on them, and the gate
# prints them. A unit the run carried that the list lacks fails the gate (a new
# uncontained executable under the verdict, unreviewed), and so does a listed
# unit the run did not carry (the list would state a premise the run did not
# rest on). A NOT JUDGED run's findings are set aside like any other.
# Measured 2026-10-01 (trustc 321aaeda7) over every report.json of a kept
# gate-13 run on this machine, before this check existed: 5 base runs and 18
# mutant runs (2026-09-30 and 2026-10-01, six worktrees). Each carries exactly
# three such rows — generic-array 0.14.7, libc 0.2.189 and trust-ir's own
# build script — and its inventory agrees. The terminal output names none of
# them; report.json (and report.ndjson) are where they are. The first gate run
# with this check (tree a53f3320, 2026-10-01; 19 min 11 s at a load average of
# ~35 on 14 cores) printed exactly those three for each of its 19 runs and
# passed; all 18 mutant workspaces' Cargo.lock files, seeded from the root's,
# kept libc 0.2.189 and generic-array 0.14.7.

BUILD_SCRIPTS = Path("scripts") / "gates" / "verified-contracts-build-scripts.tsv"
BUILD_SCRIPTS_HEADER = ("package", "source", "version", "does")
BUILD_EXECUTION_TAG = "build-execution-scope"
BUILD_EXECUTION_MODE = "run-custom-build"
# A path unit's version is spelled `workspace` when it is the root's
# `[workspace.package]` version, so a version bump does not move the list.
WORKSPACE_VERSION = "workspace"
PATH_SOURCE = "path"
SUBJECT_FIELD = re.compile(r'\b(package_id|package|compile_mode)="([^"]*)"')
SUBJECT_INDEX = re.compile(r"\bproof_unit_index=(\d+)")


@dataclass(frozen=True, order=True)
class BuildScript:
    """One build script, as the list and the report both name it: the package,
    its source (the package id's source, or `path` for a path package), and its
    version (`workspace` for a path package at the root's workspace version)."""

    package: str
    source: str
    version: str

    def __str__(self) -> str:
        return f"{self.package}@{self.version} [{self.source}]"


def parse_build_scripts(text: str) -> Tuple[Dict[BuildScript, str], List[str]]:
    """The committed list: `#` comments, one header line, then one TAB-separated
    row per build script — package, source, version, and what the script does
    (a review note, never empty). Duplicates and short rows are errors."""
    rows: Dict[BuildScript, str] = {}
    errors: List[str] = []
    header_seen = False
    for n, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        cols = line.split("\t")
        if not header_seen:
            header_seen = True
            if tuple(cols) != BUILD_SCRIPTS_HEADER:
                errors.append(f"line {n}: the header must be {chr(9).join(BUILD_SCRIPTS_HEADER)!r}, got {line!r}")
            continue
        if len(cols) != len(BUILD_SCRIPTS_HEADER) or not all(c.strip() == c and c for c in cols):
            errors.append(
                f"line {n}: a row is {len(BUILD_SCRIPTS_HEADER)} non-empty TAB-separated columns "
                f"({', '.join(BUILD_SCRIPTS_HEADER)}), got {line!r}"
            )
            continue
        unit = BuildScript(cols[0], cols[1], cols[2])
        if unit.source.startswith("path+"):
            errors.append(f"line {n}: a path package's source is spelled `{PATH_SOURCE}`, never its local path")
        if (unit.source == PATH_SOURCE) != (unit.version == WORKSPACE_VERSION):
            errors.append(
                f"line {n}: `{WORKSPACE_VERSION}` is the version of exactly the `{PATH_SOURCE}` rows "
                "(a path package at the root's workspace version)"
            )
        if unit in rows:
            errors.append(f"line {n}: {unit} is listed twice")
        rows[unit] = cols[3]
    if not header_seen:
        errors.append("no header line")
    return rows, errors


def load_build_scripts(root: Path) -> Tuple[Set[BuildScript], List[str]]:
    """The committed list under `root`, or the errors that refuse it. An empty
    list is refused too: every run of this lane executes build scripts
    (trust-ir's own among them), so an empty list could only be wrong."""
    path = root / BUILD_SCRIPTS
    if not path.is_file():
        return set(), [f"{BUILD_SCRIPTS}: missing"]
    rows, errors = parse_build_scripts(path.read_text(encoding="utf-8"))
    if not rows and not errors:
        errors.append("no row: the list names the build scripts every run executes, and there are some")
    return set(rows), [f"{BUILD_SCRIPTS}: {e}" for e in errors]


def workspace_version(root: Path) -> str:
    """The root manifest's `[workspace.package] version`."""
    m = re.search(r'(?m)^version\s*=\s*"([^"]+)"', workspace_package_table(root))
    if not m:
        raise SystemExit("root Cargo.toml: no [workspace.package] version")
    return m.group(1)


def build_script_of(package: str, package_id: str, ws_version: str) -> Tuple[Optional[BuildScript], Optional[str]]:
    """The list's name for the build script of `package` with Cargo package id
    `package_id` (`<source>#<name>@<version>`, or `<source>#<version>` when the
    name is the path's last component), or (None, why-not)."""
    if "#" not in package_id:
        return None, f"package id {package_id!r} has no `#<version>` fragment"
    source, fragment = package_id.rsplit("#", 1)
    name, _, version = fragment.rpartition("@")
    if name and name != package:
        return None, f"package id {package_id!r} names `{name}`, the row names `{package}`"
    if not version or not source or not package:
        return None, f"package id {package_id!r} of `{package}` does not parse"
    if source.startswith("path+"):
        return BuildScript(package, PATH_SOURCE, WORKSPACE_VERSION if version == ws_version else version), None
    return BuildScript(package, source, version), None


def inventory_units(data: dict) -> List[dict]:
    """Every unit the report's `cargo_proof_inventory` lists, each once (by
    `proof_unit_index`; declared, completed and covered repeat their units)."""
    inv = data.get("cargo_proof_inventory") or {}
    lists = [inv.get("excluded_active_units") or []]
    for stage in ("declared", "completed", "covered"):
        part = inv.get(stage) or {}
        lists += [part.get(key) or [] for key in ("primary_roots", "test_execution_units", "dependency_units")]
    seen: Dict[int, dict] = {}
    for units in lists:
        for unit in units:
            index = unit.get("proof_unit_index")
            if isinstance(index, int):
                seen.setdefault(index, unit)
    return [seen[i] for i in sorted(seen)]


def build_executions(data: dict, ws_version: str) -> Tuple[List[BuildScript], List[str]]:
    """The build scripts a run executed outside the proof channel — its
    `build-execution-scope` rows — and every reason that reading is not whole:
    no `assumptions` table at all (absent is never "none"), a row that does
    not parse or is not a build-script execution, or a disagreement with the
    report's own unit inventory (a `run-custom-build` unit with no row, or a
    row whose unit the inventory lacks or names differently)."""
    errors: List[str] = []
    assumptions = data.get("assumptions")
    if not isinstance(assumptions, list):
        return [], [
            "report.json carries no `assumptions` table, so the build scripts this run rested on are unknown"
        ]
    by_index: Dict[int, BuildScript] = {}
    for row in assumptions:
        if row.get("tag") != BUILD_EXECUTION_TAG:
            continue
        subject = str(row.get("subject", ""))
        fields = dict(SUBJECT_FIELD.findall(subject))
        index = SUBJECT_INDEX.search(subject)
        if fields.get("compile_mode") != BUILD_EXECUTION_MODE or index is None:
            errors.append(f"a {BUILD_EXECUTION_TAG} row that is not one build-script execution: {subject[:240]}")
            continue
        unit, why = build_script_of(fields.get("package", ""), fields.get("package_id", ""), ws_version)
        if unit is None:
            errors.append(f"a {BUILD_EXECUTION_TAG} row does not parse: {why}")
            continue
        if int(index.group(1)) in by_index:
            errors.append(f"two {BUILD_EXECUTION_TAG} rows name unit {index.group(1)}")
        by_index[int(index.group(1))] = unit
    inventory: Dict[int, BuildScript] = {}
    for u in inventory_units(data):
        if u.get("proof_unit_mode") != BUILD_EXECUTION_MODE:
            continue
        unit, why = build_script_of(str(u.get("package_name", "")), str(u.get("package_id", "")), ws_version)
        if unit is None:
            errors.append(f"an inventory {BUILD_EXECUTION_MODE} unit does not parse: {why}")
            continue
        inventory[u["proof_unit_index"]] = unit
    for index in sorted(set(by_index) | set(inventory)):
        row, inv = by_index.get(index), inventory.get(index)
        if row != inv:
            errors.append(
                f"the report's two views of build-script execution {index} disagree: "
                f"{BUILD_EXECUTION_TAG} row {row or 'absent'}, cargo_proof_inventory {inv or 'absent'}"
            )
    return [by_index[i] for i in sorted(by_index)], errors


def check_build_scripts(
    data: dict, expected: Set[BuildScript], ws_version: str
) -> Tuple[List[BuildScript], List[str]]:
    """(the build scripts the run executed, every way they are not exactly
    `expected`). See THE BUILD-SCRIPT PREMISE above. A report with no
    `assumptions` table is that one finding: its units are unknown, not none."""
    carried, failures = build_executions(data, ws_version)
    if not isinstance(data.get("assumptions"), list):
        return carried, failures
    for unit in sorted(set(carried) - expected):
        remedy = (
            "read the script, then add its row (or take it out of the lane's graph)"
            if unit.source != PATH_SOURCE or unit.version == WORKSPACE_VERSION
            # a path package off the workspace version is not this workspace's
            # crate (a local checkout elsewhere): the list cannot name it
            else f"a path package not at the workspace version ({unit.version}) is not this workspace's "
            "crate and cannot be listed; take it out of the lane's graph"
        )
        failures.append(
            f"build script {unit} ran uncontained under this verdict ({BUILD_EXECUTION_TAG}) and is not in "
            f"{BUILD_SCRIPTS}: {remedy}"
        )
    for unit in sorted(expected - set(carried)):
        failures.append(
            f"build script {unit} is in {BUILD_SCRIPTS} but this run executed no such unit: "
            "the list would state a premise the verdict did not rest on; delete the row"
        )
    return carried, failures


def build_script_line(carried: Sequence[BuildScript]) -> str:
    """What the gate prints for each run."""
    names = ", ".join(str(u) for u in sorted(set(carried))) or "none"
    return f"build scripts run uncontained ({BUILD_EXECUTION_TAG}, P-CORESIDENT): {names}"


# ---------------------------------------------------------------------------
# NOT JUDGED — schema-specific resource accounting and per-row authority
# ---------------------------------------------------------------------------
#
# THE RULE (one statement; CLAUDE.md's gate-13 row and the trust-ir-laws crate
# docs cite it; gate 15, scripts/verified_survey.py, judges every crate of its
# survey by (a) and (b) through these same functions — `memory_not_judged`,
# `budget_stop_not_judged`, `row_budget_attribution` — and (c) is this lane's
# own, because a survey is about unknown rows). A run of this lane — the base
# run and every mutant run — is JUDGED only if
#   (a) a current report has a valid schema-4 budget profile bound to EVERY
#       primary unit's tracked compiler controls, a matching typed verdict
#       vector/digest/tally and no resource, unexplained or out-of-row stops;
#       its determinism outcome is measured. The current compiler removed the
#       old RSS-ceiling option: absence is never filled in as zero. An older
#       report without typed accounting instead requires its explicit ceiling
#       and every peak reading below it, as measured on the old seal below;
#   (b) no row of the primary unit is budget- or resource-attributable
#       (`row_budget_attribution`: a timeout, a synthetic whole-function stop
#       row, a reason in the words of Trust's ResourceLimit classifier, a
#       native `TimedOut`, a kernel certification skipped or declined), and no
#       line of the run says a function "exceeded its per-function budget", and
#   (c) every compiler request of the primary unit is explained: a PUBLISHED
#       row (report.json) is proved + Certified + KernelRechecked or belongs to
#       a law this run expects to be refuted; a request the report OMITS from
#       its published rows (listed only in the terminal, under "Compiler
#       requests omitted from the published proof rows") is a favorable
#       compiler claim "withheld at publication" or belongs to such a law; the
#       omitted-request list parses whole (its printed count = its entries);
#       and the publication boundary attributes every withheld row.
# Anything else is NOT JUDGED, in BOTH directions: its proved rows are not
# evidence and a refutation it lacks is not a pass; its other findings are
# set aside, never counted as FAIL (`sort_findings`). No historical count floor
# is gated. The current vector must account for every published row, without
# dropping duplicates; its count is an integrity check, never a proof grade.
#
# WHY the older (a). On seal trustc 321aaeda7 the per-function budget is
# one ambient boolean fed by three sources, and the phase checkpoints that
# DISCARD a truncated result read only two of them:
# `verify_budget::budget_exhausted` answers true once peak RSS (`ru_maxrss`)
# reaches the ceiling, `verify_budget::exhausted_readonly` — what the
# checkpoints read — reads only the step counter and the clock. An RSS trip is
# therefore never discarded. Measured on that seal with direct trustc and the
# counter-program p4 (`fn p4(x: u32, c: bool) -> u32 { let mut y = x % 100;
# if c { y = u32::MAX; } y + 1 }`, which panics when `c`):
# `-Ztrust-verify-memory-ceiling-bytes=1 -Ztrust-verify-function-budget-steps=
# 65851` (one RSS sample at poll 316) makes `-Ztrust-policy=strict` AND
# `=certify` exit 0 with the row `no_obligations / proved / trust-structural /
# "trivially panic-free"`; the same steps with no ceiling exit 1 with
# `[overflow:add] FAILED` (reproduced 2026-09-29 for this change, first found
# by the r8 budget challenge). targo injects the ceiling as physical memory / 8
# (3 GiB on this 24 GiB host), and trust-ir's own verified-lane survey of crate
# trust-ir peaked at 4.2 GiB against it. The rule is an INTERIM guard: it holds
# for reports of that seal. Current accounting follows Trust's determinism
# plan §3.6–3.7 and crates/trust-types/src/determinism.rs: schema 4's effort
# count, derived clocks, typed vector and backstop ledger. The retained C6
# fixture is structurally current but NOT JUDGED: 790 stops are unclassified.
#
# WHY (b) and (c). The older seal records no stop cause on a row, and its stop rows
# carry no common marker (all measured on this lane, 2026-09-29, with the r7
# false-refutation repro crate): advisory `function_budget_ms = 1` gives
# `solver: trust-verify-budget` rows (`typed_kind` UnsupportedMir
# `TrustPreprocessingBudget`); strict `= 1` gives rows whose only text is "the
# function was not proved; native lowering or dispatch did not complete" — the
# budget is named only by the diagnostic "Trust verification exceeded its
# per-function budget"; strict `= 100` gives "per-function verification budget
# expired during native trust-ir bundle construction"; strict `= 300` / `=
# 1000` give `status: timeout` rows and hide 4 of the 5 refutations the same
# strict lane finds at `= 3000`; and an RSS trip at an early poll (direct
# trustc) gives "BinaryOp(Rem) does not match the audited Rust binary
# operation operand/destination types" — no budget word at all. Kernel certification
# (`certify_all(.., deadline)`) stops at the function deadline and leaves a
# proved row without its re-check, again with no reason. And a stopped request
# can leave report.json entirely: publication (seal targo-trust `types.rs`,
# `elide_rows_proved_only_by`) deletes a non-proved row its alias checker pairs
# one-to-one with a genuinely proved sibling — a def-site `obligation:` marker
# with its body VC, a hardened panic twin with the same-span direct check — and
# lists it only in the terminal; strict `timeout_ms = 1` on the r7 crate turned
# `panic_boundary:10` (a published FAILED row at `function_budget_ms = 3000`)
# into such an omitted `[UNKNOWN]` request with no budget word. So (b) NAMES the
# stops the run can name, and (c) is what makes the rule sound: a request
# nobody can explain is not evidence. The one omission (c) admits is a request
# the compiler reported FAVORABLY, demoted at publication for want of
# attachable evidence and then elided as the alias of a proved sibling (the
# seal's own label: "proof withheld at publication"). Every real run of this
# lane carries such omissions — in the base run one def-site `obligation:`
# marker per law, each the alias of its `vc:` body VC. One is admitted
# as a claim, never counted: the sibling it aliases is a published row, held
# to (c) like every other. The pairing is the seal's alias checker
# (`subsume_redundant_postcondition_markers`, `subsume_hardened_panic_twins`),
# and it pairs by obligation-id suffix and span, not by meaning: in mutant
# u64-ge-transitive-strict (measured 2026-09-29) the law's WHOLE-clause marker
# `obligation:…:postcondition:0`, UNKNOWN at the compiler, was elided as the
# alias of the ONE return path `vc:…:postcondition:0` that proved, while path
# `:2` was refuted. Such an omission is admitted only inside an expected
# refutation; that the admitted, withheld ones are about what their sibling
# proves is class external, not checked here.

GIB = 1 << 30
# The one `-Z` flag that carries the ceiling. targo places it in every unit's
# rustflags (seal targo-trust `verification_control_options`), and the report
# records the flags the primary unit ran with at
# `cargo_proof_inventory.completed.primary_roots[].semantics.unit_rustflags`.
MEMORY_CEILING_OPTION = "trust-verify-memory-ceiling-bytes"
# trustc's three memory notes (seal `trust_verify.rs`: `emit_memory_census_note`,
# the memory checkpoint note, `report_memory_ceiling_stop`). Values are GiB
# printed to one decimal, so a printed peak `p` bounds the true peak below
# `p + 0.05` GiB. The census is SILENT unless compacted slots were recomputed,
# a body was skipped, or the peak reached 4 GiB (`MEMORY_CHECKPOINT_STEP_BYTES`)
# — ABOVE the 3 GiB ceiling on this host — so its silence cannot decide (a),
# and the gate also takes its own reading (`LaneRun.rss_bound`).
MEMORY_NOTES = (
    re.compile(
        r"trust: memory census: \d+ bodies verified and compacted, \d+ compacted slots "
        r"recomputed, (?P<skipped>\d+) bodies skipped at the memory ceiling; resident "
        r"[\d.]+ GiB, peak (?P<peak>[\d.]+) GiB, ceiling (?P<ceiling>disabled|[\d.]+ GiB)"
    ),
    re.compile(
        r"trust: memory checkpoint after \d+ verified bodies: resident [\d.]+ GiB, "
        r"peak (?P<peak>[\d.]+) GiB, ceiling (?P<ceiling>disabled|[\d.]+ GiB)"
    ),
    re.compile(
        r"trust: verification memory ceiling (?P<reached>reached) after \d+ verified bodies "
        r"\(resident [\d.]+ GiB, peak (?P<peak>[\d.]+) GiB, ceiling (?P<ceiling>disabled|[\d.]+ GiB)\)"
    ),
)
# Any line of the run that speaks of trustc's memory accounting must parse as
# one of MEMORY_NOTES: a reworded note on a new toolchain fails closed.
MEMORY_MENTION = re.compile(r"trust: (?:verification )?memory|memory ceiling")
# Rule (b) over the terminal: EVERY line that says a function "exceeded its
# per-function budget" is a stop. The seal prints two such diagnostics
# (`trust_verify.rs`): the preprocessing checkpoint
# (`preprocessing_budget_exceeded`; a build error under strict/certify, a
# warning under advisory — under strict the only place a preprocessing stop is
# named, measured above) and the overflow-check origin replay (a warning in
# every policy, which the seal says only declines overflow-check elision and
# leaves verification unaffected). The replay is refused all the same: the
# rule has no per-diagnostic exceptions to keep in step with the seal, and a
# replay that tripped the function's wall-clock deadline leaves every later
# phase of that function past it. BUDGET_DIAGNOSTICS only name the function
# and phase in the finding; a line that says it and matches neither form is
# refused verbatim, so a reworded diagnostic fails closed.
BUDGET_STOP_MENTION = re.compile(r"exceeded its per-function budget")
BUDGET_DIAGNOSTICS = (
    re.compile(
        r"Trust verification exceeded its per-function budget \((?P<ms>\d+) ms / (?P<steps>\d+) "
        r"steps\) during (?P<phase>.+?) of `(?P<function>[^`]+)`"
    ),
    re.compile(
        r"Trust: the (?P<phase>overflow-check origin replay) for `(?P<function>[^`]+)` exceeded its "
        r"per-function budget \((?P<ms>\d+) ms / (?P<steps>\d+) steps\)"
    ),
)
# Rule (c) over the terminal: the requests publication omitted from
# report.json (seal targo-trust `report.rs`, `elided_publication_diagnostic_lines`:
# a header with the count, then one `  [<OUTCOME>[; proof withheld at
# publication]] function=… obligation=… kind=… claim_sha256=…` entry per
# request, each followed by deeper-indented detail lines), and the publication
# boundary's accounting-defect clause (`publication_boundary_line`). Any line
# that mentions an omitted-request list must be that header.
OMITTED_MENTION = re.compile(r"omitted from the published proof rows")
OMITTED_HEADER = re.compile(
    r"^Compiler requests omitted from the published proof rows: (?P<count>\d+) "
    r"\(diagnostics only; not discharged by this report\)$"
)
OMITTED_ENTRY = re.compile(
    r"^  \[(?P<outcome>[A-Z][A-Z-]*)(?P<withheld>; proof withheld at publication)?\] "
    r"function=(?P<function>.+) obligation=(?P<obligation>\S+) kind=(?P<kind>\S+) "
    r"claim_sha256=(?P<claim>\S+)$"
)
UNATTRIBUTED_WITHHELD = re.compile(r"^Publication boundary: .*\bunattributed\b")
# The report schema's stop-bearing fields: `ObligationOutcome::Timeout`
# (`status: timeout`), the preprocessing-budget row
# (`preprocessing_budget_artifacts`: `solver: trust-verify-budget`, `typed_kind`
# UnsupportedMir `TrustPreprocessingBudget`), and the free-text reason, read
# with the keywords of the `ResourceLimit` arm of Trust's own reason
# classifier (seal `crates/trust-report/src/repair.rs`,
# `classify_unsupported_reason`, verbatim) — but WITHOUT that classifier's
# "native-lowering first" precedence, which files "type lowering exceeded the
# per-function verification budget" (the row an RSS trip leaves at a
# function's first poll, measured) under `unsupported_mir`.
BUDGET_SOLVER = "trust-verify-budget"
BUDGET_TYPED_KIND = "TrustPreprocessingBudget"
# Every synthetic row with which the seal REPLACES a function's inventory
# because the function was not verified, other than for want of support: the
# seal's compiler mints four `UnsupportedMir` kinds for whole-function rows
# (`trust_verify.rs`: `preprocessing_budget_artifacts`,
# `memory_admission_artifacts`, `dump_only_artifacts`,
# `unsupported_contract_artifacts`), and all but the last — an unsupported
# contract, the same verdict in every run — are stops. MemoryAdmission was
# measured in the verified survey (2026-09-29): a trustd that refused its
# socket ("Connection refused") left EVERY function of crate raft-fixture
# unverified behind one such row, under a run that exited 0.
STOP_TYPED_KINDS = {
    BUDGET_TYPED_KIND: "the per-function budget ran out during preprocessing",
    "MemoryAdmission": "trustd memory admission failed before solver dispatch",
    "TrustDumpOnly": "verification dispatch skipped (-Ztrust-dump=mir-only)",
}
STOP_SOLVERS = (BUDGET_SOLVER, "trust-memory-coordinator", "trust-dump-mir-only")
# The between-bodies RSS check's row (`transport_memory_ceiling_gap_row`):
# every body after the process crossed the ceiling is published with it — its
# description says the first phrase, its reason the second.
MEMORY_CEILING_GAP = "over the verification memory ceiling"
MEMORY_CEILING_GAP_REASON = "had reached the verification memory ceiling"
# Two stops the classifier's words miss (seal `trust_verify.rs`). The native
# full verifier's status is spelled by `{:?}` of its enum, so a native timeout
# reads `TimedOut`, never "timed out". And kernel certification
# (`certify_all(.., deadline)`) STOPS at the function deadline with no reason
# recorded: a Proved result left without its certificate is published proved
# without `KernelRechecked`, or — when no other authority permits the proof —
# as `unknown` / `runtime_checked` with exactly PROVED_WITHOUT_AUTHORITY
# (`build_proof_results`), the text a kernel MISS also gets. A skipped
# certification cannot be told from a declined one, so both are stops.
NATIVE_TIMED_OUT = re.compile(r"\bTimedOut\b")
PROVED_WITHOUT_AUTHORITY = "solver reported Proved without exact kernel/native proof authority"
# The words are matched in the row's VERDICT text only — `outcome.reason` and
# an `UnsupportedMir` typed detail, never `description`, the obligation's
# static text — with backticked code spans dropped and each word standing
# alone (no letter, digit or `_` on either side). Measured in the verified
# survey (2026-09-29, all twelve members): EVERY description-only hit was
# spurious — 45 rows whose description is the unbounded_allocation advice
# "route it through a budget-checked allocator", and identifiers (`proof_budget`,
# `serde_budget::with_decode_resource_limits`, `recheck_one_theorem_budgeted`,
# `DeclarationBudgetExhausted`, bincode's `WithOtherLimit` as "rlimit",
# `TooManyNodes` as "oom") — each of which unjudged a crate for a word in a name.
RESOURCE_LIMIT_KEYWORDS = (
    "skipped solver dispatch",
    "skipping solver dispatch",
    "memory guard",
    "memory limit",
    "resource limit",
    "oom",
    "out of memory",
    "rlimit",
    "budget",
    "timed out",
    "deadline",
)
RESOURCE_LIMIT_WORDS = tuple(
    (keyword, re.compile(r"(?<![a-z0-9_])" + re.escape(keyword) + r"(?![a-z0-9_])"))
    for keyword in RESOURCE_LIMIT_KEYWORDS
)
CODE_SPAN = re.compile(r"`[^`]*`")


@dataclass
class LaneRun:
    """One `targo trust check` run: its exit status, its terminal output, and
    `rss_bound` — the peak resident set of the run's whole process tree
    (`wait4`'s `ru_maxrss` over targo and every descendant it reaped, the
    primary unit's trustc included; measured 2026-09-29: every trustc of a run
    descends from its targo, and the bound, 0.748 GiB, sat above the largest
    sampled trustc, 0.740 GiB). `None` where no such reading exists."""

    code: int
    output: str
    rss_bound: Optional[int]
    wall_s: Optional[float] = None
    cpu_s: Optional[float] = None
    tree_mb: Optional[int] = None  # sampled peak RSS of the whole tree (scripts/host_scale.py)
    procs_at_peak: Optional[int] = None
    largest_mb: Optional[int] = None  # the largest process at that sampled peak
    report_dir: Optional[str] = None  # fresh retained outputs; old/stubbed runs use their caller's path


def retained_report_dir(run: LaneRun, legacy: Path) -> Path:
    """Locate this run's outputs, never a previous run's logical report slot."""
    return Path(run.report_dir) if run.report_dir is not None else legacy


def primary_function(full: str, crate: str = CRATE) -> Optional[str]:
    """The function path after the `cargo-target(...)::` prefix when `full`
    names a function of `crate`'s PRIMARY unit (default: this lane's crate),
    else None. scripts/verified_survey.py reads every crate through it."""
    if ")::" not in full:
        return None
    prefix, name = full.split(")::", 1)
    if f'package="{crate}"' not in prefix or 'proof_unit_role="primary"' not in prefix:
        return None
    return name


def primary_rows(data: dict, crate: str = CRATE) -> List[Tuple[str, dict]]:
    """Every obligation row of the PRIMARY unit of `crate`, as (function
    path after the cargo-target prefix, row). The unit is judged as a whole:
    a stop in any of its functions taints it (R1 facts feed other functions)."""
    rows: List[Tuple[str, dict]] = []
    for entry in data.get("functions", []):
        name = primary_function(entry.get("function", ""), crate)
        if name is None:
            continue
        for ob in entry.get("obligations", []):
            rows.append((name, ob))
    return rows


@dataclass
class OmittedList:
    """One "Compiler requests omitted from the published proof rows" list of
    the terminal: its header line, the count it prints (None when the header
    does not parse), and every `  [` entry line under it, verbatim."""

    header: str
    count: Optional[int]
    entries: List[str] = field(default_factory=list)


def omitted_lists(output: str) -> List[OmittedList]:
    """Every omitted-request list of a run's terminal output (the entries run
    to the first line that is not indented)."""
    lines = output.splitlines()
    lists: List[OmittedList] = []
    i = 0
    while i < len(lines):
        if not OMITTED_MENTION.search(lines[i]):
            i += 1
            continue
        header = OMITTED_HEADER.match(lines[i])
        found = OmittedList(lines[i], int(header["count"]) if header else None)
        i += 1
        while i < len(lines) and lines[i].startswith("  "):
            if lines[i].startswith("  ["):
                found.entries.append(lines[i])
            i += 1
        lists.append(found)
    return lists


def omitted_not_judged(output: str, expect_refuted: Set[str]) -> List[str]:
    """Rule (c) over what publication kept out of report.json."""
    reasons: List[str] = []
    for line in output.splitlines():
        if UNATTRIBUTED_WITHHELD.search(line):
            reasons.append(
                f"{NOT_JUDGED} the publication boundary cannot attribute every withheld row: {line.strip()[:240]}"
            )
    for found in omitted_lists(output):
        if found.count is None:
            reasons.append(f"{NOT_JUDGED} unparsed omitted-request list header: {found.header.strip()[:240]}")
        elif found.count != len(found.entries):
            reasons.append(
                f"{NOT_JUDGED} the omitted-request list prints {found.count} request(s) but carries "
                f"{len(found.entries)} entry line(s)"
            )
        for line in found.entries:
            entry = OMITTED_ENTRY.match(line)
            if entry is None:
                reasons.append(f"{NOT_JUDGED} unparsed omitted-request entry: {line.strip()[:240]}")
                continue
            name = primary_function(entry["function"])
            if name is None or entry["withheld"] or law_key(name) in expect_refuted:
                continue
            reasons.append(
                f"{NOT_JUDGED} `{name}` {entry['obligation']} was omitted from the published rows as "
                f"{entry['outcome']}, not as a favorable claim withheld at publication: the request did "
                "not prove on its own and the seal records no stop cause, so it cannot be ruled out as one"
            )
    return reasons


def law_key(name: str) -> Optional[str]:
    """The `by_leaf` key of a function path, or None for a function that is
    neither a law nor a top-level subject."""
    parts = name.split("::")
    if name.startswith("<") or parts[0] != CRATE_IDENT:
        return None
    if len(parts) == 2:
        return parts[1]
    if len(parts) == 3 and parts[1] == "laws":
        return parts[2]
    return None


def memory_ceiling(data: dict) -> Tuple[Optional[int], Optional[str]]:
    """The ceiling (bytes; 0 = disabled) the primary unit ran under, read from
    the report, or (None, why-not). Exactly one value over the primary roots."""
    roots = ((data.get("cargo_proof_inventory") or {}).get("completed") or {}).get("primary_roots") or []
    if not roots:
        return None, "the report records no completed primary unit (cargo_proof_inventory.completed.primary_roots)"
    values: Set[int] = set()
    for root in roots:
        flags = [str(f) for f in ((root.get("semantics") or {}).get("unit_rustflags") or [])]
        for i, flag in enumerate(flags):
            spelled = flag[2:] if flag.startswith("-Z") and flag != "-Z" else (
                flags[i + 1] if flag == "-Z" and i + 1 < len(flags) else ""
            )
            if spelled.startswith(MEMORY_CEILING_OPTION + "="):
                try:
                    values.add(int(spelled.split("=", 1)[1]))
                except ValueError:
                    return None, f"unparseable memory ceiling flag `{spelled}`"
    if not values:
        return None, (
            f"the report records no -Z{MEMORY_CEILING_OPTION} for the primary unit, so the "
            "ceiling it ran under is unknown (the seal's trustc default is 0 = disabled, but "
            "the gate cannot know the default of the toolchain that ran)"
        )
    if len(values) != 1:
        return None, f"the primary unit records {len(values)} different memory ceilings: {sorted(values)}"
    return values.pop(), None


def printed_gib(text: str) -> Optional[float]:
    return None if text == "disabled" else float(text.split()[0])


DETERMINISM_SCHEMA = 4
# Trust's crates/trust-types/src/determinism.rs: StopCause, BudgetProfile::id
# and VerdictVector::digest. Counts and the compiler's backstop ledger are
# data about why work stopped, never proof authority.
STOP_CAUSES = frozenset({
    "solved", "steps", "effort", "term-memory", "frames", "solver-incomplete", "unsupported",
    "not-dispatched", "wall-backstop", "rss-backstop", "solver-fault", "unclassified", "admission-refused",
})
RESOURCE_STOPS = STOP_CAUSES - {"solved", "solver-incomplete", "unsupported", "not-dispatched"}


def determinism_digest(domain: bytes, fields: Sequence[str], count: Optional[int] = None) -> str:
    """The producer's length-prefixed UTF-8 encoding (u64 little-endian)."""
    digest = hashlib.sha256(domain)
    if count is not None:
        digest.update(count.to_bytes(8, "little"))
    for field in fields:
        encoded = field.encode("utf-8")
        digest.update(len(encoded).to_bytes(8, "little"))
        digest.update(encoded)
    return digest.hexdigest()


def primary_z_options(data: dict) -> List[List[str]]:
    """Every primary root's tracked -Z options, preserving duplicates."""
    roots = ((data.get("cargo_proof_inventory") or {}).get("completed") or {}).get("primary_roots") or []
    result = []
    for root in roots:
        flags = ((root.get("semantics") or {}).get("unit_rustflags") or [])
        options = []
        for i, flag in enumerate(flags):
            if flag == "-Z" and i + 1 < len(flags) and isinstance(flags[i + 1], str):
                options.append(flags[i + 1])
            elif isinstance(flag, str) and flag.startswith("-Z") and flag != "-Z":
                options.append(flag[2:])
        result.append(options)
    return result


def determinism_not_judged(data: dict) -> List[str]:
    """Validate current resource accounting without inventing a disabled RSS
    ceiling. The current compiler removed that control; schema-4 budgets and
    typed stops expose the work that ended. A valid record is still not a
    proof: not_judged/check_rows retain their per-row,
    Certified + KernelRechecked and expected-refutation requirements.

    The survey streams functions separately, so a header validates the vector
    itself; a full report additionally binds every vector entry to its row.
    """
    reasons = []

    def refuse(why: str) -> None:
        reasons.append(f"{NOT_JUDGED} determinism: {why}")

    record = (data.get("verification_gate") or {}).get("determinism")
    if not isinstance(record, dict):
        return [f"{NOT_JUDGED} determinism: the report carries no determinism record"]
    profile = record.get("budget_profile")
    if not isinstance(profile, dict):
        return [f"{NOT_JUDGED} determinism: the report carries no budget profile"]
    schema = profile.get("schema")
    if type(schema) is not int or schema != DETERMINISM_SCHEMA:
        return [f"{NOT_JUDGED} determinism: budget profile schema {schema!r} is not readable; "
                f"this reader accepts schema {DETERMINISM_SCHEMA} only; regenerate the report"]
    bounds = {"effort": (1, 100_000), "backstop": (1, (1 << 32) - 1), "worker_threads": (0, (1 << 64) - 1)}
    if set(profile) != {"schema", "name", *bounds} or not isinstance(profile.get("name"), str):
        refuse("schema 4 budget profile must carry exactly schema, name, effort, backstop and worker_threads")
    for key, (low, high) in bounds.items():
        value = profile.get(key)
        if type(value) is not int or not low <= value <= high:
            refuse(f"budget profile {key} must be an integer in {low}..={high}, got {value!r}")
    if reasons:
        return reasons
    expected_id = determinism_digest(b"trust-budget-profile\0", [
        "backstop", str(profile["backstop"]), "effort", str(profile["effort"]), "schema", str(schema),
    ])
    if record.get("budget_profile_id") != expected_id:
        refuse("budget_profile_id does not match the recorded schema-4 bounds")
    expected_options = {
        "trust-verify-effort": profile["effort"],
        "trust-verify-timeout-ms": max(1, 5000 * profile["backstop"] // 1000),
        "trust-verify-function-budget-ms": max(1, 120000 * profile["backstop"] // 1000),
    }
    if profile["worker_threads"]:
        expected_options["trust-verify-worker-threads"] = profile["worker_threads"]
    roots = primary_z_options(data)
    if not roots:
        refuse("the report records no completed primary unit to bind to the budget profile")
    for index, options in enumerate(roots):
        for name, value in expected_options.items():
            actual = [option for option in options if option.split("=", 1)[0] == name]
            if actual != [f"{name}={value}"]:
                refuse(f"primary root {index} must record exactly -Z{name}={value}, got {actual!r}")
        if not profile["worker_threads"] and any(o.startswith("trust-verify-worker-threads=") for o in options):
            refuse(f"primary root {index} records a worker-thread cap absent from the budget profile")
        if any(o.split("=", 1)[0] == MEMORY_CEILING_OPTION for o in options):
            refuse(f"primary root {index} records the retired memory-ceiling option in a schema-4 report")
    # The producer omits an empty vector; only an explicit matching gate
    # total and digest can validate it. Gate 13 separately requires law rows.
    vector = record.get("vector", [])
    if not isinstance(vector, list):
        refuse("the report carries no typed verdict vector")
        return reasons
    statuses = {"proved", "failed", "unknown", "timeout", "runtime_checked"}
    entries = []
    for index, entry in enumerate(vector):
        if (not isinstance(entry, dict) or set(entry) != {"obligation", "status", "stop"}
                or not isinstance(entry.get("obligation"), str) or not entry["obligation"]
                or not isinstance(entry.get("status"), str) or entry["status"] not in statuses
                or not isinstance(entry.get("stop"), str) or entry["stop"] not in STOP_CAUSES):
            refuse(f"malformed typed verdict vector entry {index}")
            return reasons
        if entry["status"] in ("proved", "failed") and entry["stop"] != "solved":
            refuse(f"verdict vector entry {index} records a decided row with stop {entry['stop']}")
        entries.append((entry["obligation"], entry["status"], entry["stop"]))
    if entries != sorted(entries):
        refuse("the verdict vector is not in canonical obligation/status/stop order")
    expected_vector = determinism_digest(b"trust-verdict-vector/v2\0", [f for e in entries for f in e], len(entries))
    if record.get("vector_digest") != expected_vector:
        refuse("vector_digest does not match the typed verdict vector")
    total = ((data.get("verification_gate") or {}).get("counts") or {}).get("total")
    if type(total) is not int or total != len(entries):
        refuse("the gate's total does not match the typed verdict vector's row count")
    tally = dict(Counter(e[2] for e in entries))
    reported = record.get("stop_causes")
    if (not isinstance(reported, dict) or any(type(n) is not int or n <= 0 for n in reported.values())
            or reported != tally):
        refuse("stop_causes does not match the typed verdict vector's positive counts")
    stops = sorted(RESOURCE_STOPS.intersection(tally))
    if stops:
        refuse("typed verdict vector records resource or unexplained stops: " + ", ".join(f"{s}={tally[s]}" for s in stops))
    for key in ("volatile_keys", "unkeyed_functions", "noted_stops"):
        value = record.get(key, [])
        if not isinstance(value, list) or value:
            refuse(f"{key} is not empty: {str(value)[:240]}")
    if record.get("stop_items", {}) != {}:
        refuse("the compiler records named stop_items")
    if record.get("outcome") != "measured":
        refuse(f"the run's outcome is {record.get('outcome')!r}, not measured")
    if "functions" in data:
        rows = [ob for entry in data["functions"] for ob in entry.get("obligations", [])]
        row_keys = []
        for ob in rows:
            identity = (ob.get("transport_evidence") or {}).get("identity") or {}
            key = identity.get("key") if isinstance(identity, dict) else None
            if not isinstance(key, str) or not key:
                refuse("a published row carries no stable transport identity key")
                break
            row_keys.append((key, (ob.get("outcome") or {}).get("status")))
        if Counter(row_keys) != Counter((key, status) for key, status, _ in entries):
            refuse("the typed verdict vector does not match every published row's stable key and status")
    return reasons


def memory_not_judged(data: dict, output: str, rss_bound: Optional[int]) -> List[str]:
    """Rule (a), by report schema: typed current accounting, or the older
    seal's explicit ceiling and peak readings. Absence never means zero."""
    if ("determinism" in (data.get("verification_gate") or {})
            or any(o.startswith("trust-verify-effort=") for opts in primary_z_options(data) for o in opts)):
        reasons = determinism_not_judged(data)
        if MEMORY_MENTION.search(output):
            reasons.append(f"{NOT_JUDGED} memory: legacy memory-ceiling diagnostic in a current-schema run")
        return reasons
    reasons: List[str] = []
    ceiling, why = memory_ceiling(data)
    if ceiling is None:
        return [f"{NOT_JUDGED} memory: {why}"]
    readings: List[Tuple[str, int]] = []
    if rss_bound is None:
        reasons.append(
            f"{NOT_JUDGED} memory: no peak-RSS reading of the run's process tree (wait4 unavailable), "
            "and trustc's census is silent below 4 GiB, above the ceiling"
        )
    else:
        readings.append(("wait4 ru_maxrss over targo's process tree", rss_bound))
    for line in output.splitlines():
        if not MEMORY_MENTION.search(line):
            continue
        match = next((m for m in (p.search(line) for p in MEMORY_NOTES) if m), None)
        if match is None and (MEMORY_CEILING_GAP in line or MEMORY_CEILING_GAP_REASON in line):
            # The terminal echo of a memory-ceiling gap row: a body the seal
            # did not verify because the process was over the ceiling
            # (measured: after one body, every later body of crate trust-ir).
            reasons.append(
                f"{NOT_JUDGED} memory: a body was not verified — the process was over the verification memory "
                f"ceiling: {line.strip()[:200]}"
            )
            continue
        if match is None:
            reasons.append(f"{NOT_JUDGED} memory: unparsed trustc memory line: {line.strip()[:240]}")
            continue
        fields = match.groupdict()
        printed = printed_gib(fields["ceiling"])
        if (printed is None) != (ceiling == 0) or (
            printed is not None and abs(printed * GIB - ceiling) > 0.05 * GIB + 1
        ):
            reasons.append(
                f"{NOT_JUDGED} memory: trustc prints ceiling {fields['ceiling']} but the report "
                f"records {ceiling} bytes: {line.strip()[:200]}"
            )
        if fields.get("reached"):
            reasons.append(f"{NOT_JUDGED} memory: trustc reports the ceiling reached: {line.strip()[:240]}")
        if int(fields.get("skipped") or 0):
            reasons.append(
                f"{NOT_JUDGED} memory: {fields['skipped']} bodies skipped at the memory ceiling: "
                f"{line.strip()[:200]}"
            )
        readings.append(("trustc memory note (printed peak + 0.05 GiB rounding)", int((float(fields["peak"]) + 0.05) * GIB)))
    if ceiling == 0:
        return reasons  # no ceiling, no RSS latch: (a) holds vacuously
    for source, peak in readings:
        if peak >= ceiling:
            reasons.append(
                f"{NOT_JUDGED} memory: peak RSS {peak / GIB:.2f} GiB ({source}) reached the "
                f"verification memory ceiling {ceiling / GIB:.2f} GiB — on the installed seal an "
                "RSS trip is invisible to the phase checkpoint (verify_budget::exhausted_readonly "
                "reads only steps and the clock) and one made strict/certify PROVE the panicking "
                "counter-program p4, so no row of this run is evidence"
            )
    return reasons


def row_budget_attribution(ob: dict) -> Optional[str]:
    """Rule (b), per row: the stop the report's own fields name, or None.
    scripts/verified_survey.py judges every crate by this same function."""
    outcome = ob.get("outcome") or {}
    status = outcome.get("status")
    if status == "timeout":
        return f"status timeout ({outcome.get('timeout_ms')} ms)"
    if ob.get("solver") == BUDGET_SOLVER:
        return f"solver {BUDGET_SOLVER} (the preprocessing-budget row)"
    typed = (ob.get("transport_evidence") or {}).get("typed_kind")
    unsupported = typed.get("UnsupportedMir") if isinstance(typed, dict) else None
    if isinstance(unsupported, dict) and unsupported.get("kind") in STOP_TYPED_KINDS:
        return f"typed_kind UnsupportedMir {unsupported['kind']} ({STOP_TYPED_KINDS[unsupported['kind']]})"
    if ob.get("solver") in STOP_SOLVERS:
        return f"solver {ob.get('solver')} (a synthetic whole-function stop row)"
    gap_text = f"{ob.get('description', '')} | {outcome.get('reason', '')}"
    if MEMORY_CEILING_GAP in gap_text or MEMORY_CEILING_GAP_REASON in gap_text:
        return f"the memory-ceiling gap row: {str(ob.get('description'))[:160]}"
    if status == "proved":
        strength = outcome.get("strength") or {}
        validation = (strength.get("grade") or {}).get("validation")
        if strength.get("assurance") != "Certified" or validation != "KernelRechecked":
            return (
                f"certification skipped or declined: proved {strength.get('assurance')}/{validation} "
                "without a Clean-kernel re-check (the seal's certify_all stops at the function "
                "deadline and records no cause)"
            )
        return None
    detail = unsupported.get("detail") if isinstance(unsupported, dict) else None
    text = " | ".join(str(t) for t in (outcome.get("reason"), detail) if t)
    if PROVED_WITHOUT_AUTHORITY in text:
        return (
            f"certification skipped or declined: a Proved result published {status} as "
            f"\"{PROVED_WITHOUT_AUTHORITY}\" (a deadline skip and a kernel miss read alike)"
        )
    native = NATIVE_TIMED_OUT.search(text)
    if native:
        at = native.start()
        return f"a native verifier `TimedOut`: …{text[max(0, at - 90):at + 90]}…"
    prose = CODE_SPAN.sub("`…`", text)
    lowered = prose.lower()
    for keyword, word in RESOURCE_LIMIT_WORDS:
        found = word.search(lowered)
        if found:
            at = found.start()
            return f"its text names `{keyword}`: …{prose[max(0, at - 90):at + 90]}…"
    return None


def budget_stop_not_judged(output: str) -> List[str]:
    """Rule (b) over the terminal: every line that says a function "exceeded
    its per-function budget" (BUDGET_STOP_MENTION) is a stop."""
    reasons: List[str] = []
    for line in output.splitlines():
        if not BUDGET_STOP_MENTION.search(line):
            continue
        m = next((m for m in (p.search(line) for p in BUDGET_DIAGNOSTICS) if m), None)
        if m is None:
            reasons.append(f"{NOT_JUDGED} budget stop (unparsed diagnostic): {line.strip()[:240]}")
        else:
            reasons.append(
                f"{NOT_JUDGED} budget stop: `{m['function']}` exceeded its per-function budget "
                f"({m['ms']} ms / {m['steps']} steps) during {m['phase']}"
            )
    return reasons


def not_judged(data: dict, run: LaneRun, expect_refuted: Set[str]) -> List[str]:
    """Every reason the run is NOT JUDGED (empty = judged); see THE RULE above."""
    reasons = memory_not_judged(data, run.output, run.rss_bound)
    reasons += budget_stop_not_judged(run.output)
    reasons += omitted_not_judged(run.output, expect_refuted)
    rows = primary_rows(data)
    if not rows:
        reasons.append(f"{NOT_JUDGED} the report carries no row of the primary unit")
    for name, ob in rows:
        oid = ob.get("obligation_id") or ob.get("kind") or "?"
        outcome = ob.get("outcome") or {}
        status = outcome.get("status")
        stop = row_budget_attribution(ob)
        if stop is not None:
            reasons.append(f"{NOT_JUDGED} budget-attributable row `{name}` {oid}: {stop}")
        elif status not in ("proved", "failed") and law_key(name) not in expect_refuted:
            accounting = ("the typed stop vector establishes no proof authority" if
                          "determinism" in (data.get("verification_gate") or {}) else
                          "the older seal records no stop cause on a row, so it cannot be ruled out as one")
            reasons.append(
                f"{NOT_JUDGED} `{name}` {oid} is {status}, neither proved nor an expected refutation; "
                f"{accounting}: "
                f"{str(outcome.get('reason') or ob.get('description') or '')[:200]}"
            )
    return reasons


def apply_edits(text: str, edits: Sequence[Edit], what: str) -> str:
    """Apply `edits` of ONE file to its ORIGINAL `text`, together: every
    anchor must occur exactly once in `text` and no two may overlap (so an
    edit's replacement can never be matched by another's anchor)."""
    spans: List[Tuple[int, int, str]] = []
    for e in edits:
        n = text.count(e.old)
        if n != 1:
            raise SystemExit(f"{what}: anchor occurs {n} times in {e.file}, need exactly 1: {e.old!r}")
        if e.old == e.new:
            raise SystemExit(f"{what}: an edit of {e.file} changes nothing")
        start = text.index(e.old)
        spans.append((start, start + len(e.old), e.new))
    spans.sort()
    for (_, end_a, _), (start_b, _, _) in zip(spans, spans[1:]):
        if start_b < end_a:
            raise SystemExit(f"{what}: two edits of the same file overlap")
    for start, end, new in reversed(spans):
        text = text[:start] + new + text[end:]
    return text


def apply_mutation(crate_dirs: Dict[str, Path], m: Mutant) -> None:
    """Apply every edit of `m` to the copies in `crate_dirs` (crate -> dir)."""
    by_file: Dict[Tuple[str, str], List[Edit]] = {}
    for e in m.edits:
        by_file.setdefault((e.crate, e.file), []).append(e)
    for (crate, file), edits in by_file.items():
        if crate not in crate_dirs:
            raise SystemExit(f"mutant {m.name}: edits {crate}, which this mutant did not copy")
        path = crate_dirs[crate] / file
        path.write_text(
            apply_edits(path.read_text(encoding="utf-8"), edits, f"mutant {m.name}"),
            encoding="utf-8",
        )


def require_targo(candidate: str) -> str:
    """Refuse upstream Cargo installed under the name `targo`: only the real
    targo accepts `--unverified --version` (the discriminator Trust's CLAUDE.md
    names; a cargo-in-disguise would give this lane no verification at all)."""
    probe = subprocess.run(
        [candidate, "--unverified", "--version"], capture_output=True, text=True, check=False
    )
    if probe.returncode != 0:
        raise SystemExit(
            f"{candidate} is not Trust's targo: `targo --unverified --version` failed "
            "(upstream Cargo under that name rejects the flag)"
        )
    return candidate


def resolve_targo() -> str:
    """Mirror of scripts/run-targo.sh: TRUST_TARGO_BIN, PATH, then the rustup
    `trust` toolchain, each held to the targo discriminator. Deliberately no
    fallback to upstream Cargo."""
    env = os.environ.get("TRUST_TARGO_BIN")
    if env is not None:
        if not env or not os.access(env, os.X_OK) or Path(env).name != "targo":
            raise SystemExit(f"TRUST_TARGO_BIN must name an executable `targo`, got {env!r}")
        return require_targo(env)
    found = shutil.which("targo")
    if found:
        return require_targo(found)
    if shutil.which("rustup"):
        probe = subprocess.run(
            ["rustup", "which", "--toolchain", "trust", "targo"],
            capture_output=True,
            text=True,
            check=False,
        )
        if probe.returncode == 0 and probe.stdout.strip():
            return require_targo(probe.stdout.strip())
    raise SystemExit("Trust targo was not found; set TRUST_TARGO_BIN or install the trust toolchain")


def root_trust_table(root: Path) -> str:
    """The root manifest's `[trust]` table, verbatim (the budget every run
    of this lane, mutants included, is held to)."""
    text = (root / "Cargo.toml").read_text(encoding="utf-8")
    m = re.search(r"(?ms)^\[trust\]\n(.*?)(?=^\[|\Z)", text)
    return m.group(1).strip() + "\n" if m else ""


def workspace_edition(root: Path) -> str:
    text = (root / "Cargo.toml").read_text(encoding="utf-8")
    m = re.search(r'(?ms)^\[workspace\.package\]\n.*?^edition\s*=\s*"(\d+)"', text)
    if not m:
        raise SystemExit("root Cargo.toml: no [workspace.package] edition")
    return m.group(1)


def workspace_package_table(root: Path) -> str:
    """The root manifest's `[workspace.package]` table, verbatim: a copied
    trust-ir inherits its package keys from it (`version.workspace = true`)."""
    text = (root / "Cargo.toml").read_text(encoding="utf-8")
    m = re.search(r"(?ms)^\[workspace\.package\]\n(.*?)(?=^\[|\Z)", text)
    if not m:
        raise SystemExit("root Cargo.toml: no [workspace.package] table")
    return m.group(1).strip() + "\n"


def write_mutant_crate(root: Path, dest: Path, m: Mutant, laws: Sequence[str]) -> None:
    """A standalone mutant WORKSPACE at `dest` (the root's `[workspace.package]`
    and `[trust]` tables): a copy of this crate whose laws.rs keeps only the
    laws of `m.scope`, and — when `m` edits a trust-ir table — a copy of
    trust-ir (never its tests or docs) that the crate depends on instead of
    the real one. The mutation is applied to the copies before the laws file
    is scoped, so every anchor is checked against the full real text. The
    root's Cargo.lock is copied too: the base run resolves through it, and a
    mutant must build the same dependency versions — so execute the same build
    scripts (THE BUILD-SCRIPT PREMISE) — not what a fresh resolution picks
    from the index that day (before 2026-10-01 every mutant resolved afresh;
    the 12 kept mutant runs measured then had resolved the root's versions of
    the build-script packages)."""
    lock = root / "Cargo.lock"
    if not lock.is_file():
        raise SystemExit(f"{lock} is missing: a mutant workspace would resolve its dependencies afresh")
    if dest.exists():
        shutil.rmtree(dest)
    laws_dir = dest / CRATE
    shutil.copytree(root / CRATE_DIR / "src", laws_dir / "src")
    crate_dirs = {CRATE: laws_dir}
    members = [CRATE]
    if m.mutates_trust_ir:
        ir_dir = dest / IR_CRATE
        shutil.copytree(
            root / IR_CRATE_DIR,
            ir_dir,
            ignore=shutil.ignore_patterns("tests", "docs", "target"),
        )
        crate_dirs[IR_CRATE] = ir_dir
        members.append(IR_CRATE)
        ir_path = f"../{IR_CRATE}"
    else:
        ir_path = (root / IR_CRATE_DIR).as_posix()
    (laws_dir / "Cargo.toml").write_text(
        "# Generated by scripts/verified_contracts.py — a MUTANT of "
        f"{CRATE_DIR.as_posix()}; never commit.\n"
        "[package]\n"
        f'name = "{CRATE}"\n'
        'version = "0.0.0"\n'
        f'edition = "{workspace_edition(root)}"\n'
        "\n[dependencies]\n"
        f'trust-ir = {{ path = "{ir_path}" }}\n'
        "\n[lints.rust]\n"
        "unexpected_cfgs = { level = \"warn\", check-cfg = ['cfg(trust_verify)'] }\n",
        encoding="utf-8",
    )
    trust = root_trust_table(root)
    member_list = ", ".join('"' + member + '"' for member in members)
    (dest / "Cargo.toml").write_text(
        "# Generated by scripts/verified_contracts.py — a MUTANT workspace; never commit.\n"
        "[workspace]\n"
        'resolver = "2"\n'
        f"members = [{member_list}]\n"
        "\n[workspace.package]\n"
        + workspace_package_table(root)
        + ("\n[trust]\n" + trust if trust else ""),
        encoding="utf-8",
    )
    shutil.copyfile(lock, dest / "Cargo.lock")
    apply_mutation(crate_dirs, m)
    laws_file = laws_dir / "src" / "laws.rs"
    keep = set(scoped_laws(m, laws))
    laws_file.write_text(
        scope_laws_source(laws_file.read_text(encoding="utf-8"), keep), encoding="utf-8"
    )


def maxrss_bytes(ru_maxrss: int) -> int:
    """`ru_maxrss` is bytes on macOS and KiB on Linux (the unit trap the
    seal's own `peak_resident_bytes` spells out)."""
    return ru_maxrss if sys.platform == "darwin" else ru_maxrss * 1024


def run_lane(
    targo: str, cwd: Path, report_dir: Path, target_dir: Path, extra: Sequence[str], release: bool = True
) -> LaneRun:
    """Run the lane and reap it with `wait4`, whose `ru_maxrss` is the peak of
    targo and every descendant it reaped — the bound rule (a) of `not_judged`
    compares with the ceiling (trustc's own census is silent below 4 GiB).
    `release=False` is the debug profile scripts/verified_survey.py runs.
    Finalized native inputs and the report share a fresh retained namespace;
    they are diagnostic data, never completeness or proof authority. Compiled
    target paths remain stable across runs."""
    env = dict(os.environ)
    env["CARGO_TARGET_DIR"] = str(target_dir)
    for key in ("RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS"):
        if key in env:
            raise SystemExit(f"{key} is set; the verified lane takes its policy from the manifest only")
    # The diagnostic exporter postdates some otherwise supported toolchains.
    # An advertised option requests data; it establishes no proof capability.
    probe = subprocess.run([targo, "trust", "--help"], cwd=str(cwd), env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                           timeout=30, check=False)
    if probe.returncode != 0:
        raise SystemExit(f"targo trust --help failed (exit {probe.returncode}): {probe.stdout[:400]}")
    native_output = bool(re.search(r"(?m)^\s*--native-bundle-dir(?:\s|=|$)", probe.stdout))
    capture_root = target_dir.parent.resolve() / "verified-inputs"
    capture_root.mkdir(parents=True, exist_ok=True)
    report_dir = Path(tempfile.mkdtemp(prefix=f"{report_dir.name}-", dir=capture_root))
    cmd = [targo, "trust", "check", *(["--release"] if release else []), *extra,
           "--report-dir", str(report_dir)]
    if native_output:
        cmd += ["--native-bundle-dir", str(report_dir / "native-bundles")]
    (report_dir / "tool-help.txt").write_text(probe.stdout, encoding="utf-8")
    (report_dir / "request.json").write_text(json.dumps({
        "schema": "trust-ir-diagnostic-native-inputs-v1",
        "command": cmd, "cwd": str(cwd), "complete_census": False, "proof_authority": False,
        "native_bundle_export": "requested" if native_output else "not-advertised",
    }) + "\n", encoding="utf-8")
    started = time.monotonic()
    proc = subprocess.Popen(cmd, cwd=str(cwd), env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    captured: Dict[str, bytes] = {}

    def drain(key: str, stream) -> None:
        captured[key] = stream.read()
        stream.close()

    readers = [threading.Thread(target=drain, args=(k, s)) for k, s in (("out", proc.stdout), ("err", proc.stderr))]
    # The sampler only sizes later scheduling (host_scale.py); rule (a) reads
    # `rss_bound` alone, as before.
    import host_scale

    sampler = host_scale.TreeSampler(proc.pid)
    with sampler:
        for t in readers:
            t.start()
        for t in readers:
            t.join()
        rss_bound: Optional[int] = None
        cpu: Optional[float] = None
        if hasattr(os, "wait4"):
            _, status, usage = os.wait4(proc.pid, 0)
            proc.returncode = os.waitstatus_to_exitcode(status)
            rss_bound = maxrss_bytes(usage.ru_maxrss)
            cpu = usage.ru_utime + usage.ru_stime
        else:  # no process-tree reading: rule (a) reports the run NOT JUDGED
            proc.wait()
    tree_mb, procs = sampler.peak_tree_mb or None, sampler.procs_at_peak or None
    largest = sampler.largest_at_peak_mb or None
    output = (captured["out"] + captured["err"]).decode("utf-8", errors="replace")
    run = LaneRun(code=proc.returncode, output=output, rss_bound=rss_bound,
                  wall_s=time.monotonic() - started, cpu_s=cpu, tree_mb=tree_mb, procs_at_peak=procs,
                  largest_mb=largest, report_dir=str(report_dir))
    record_run(report_dir / "run", run)
    print(f"    diagnostic inputs retained: {report_dir}")
    if not native_output:
        print("    native bundle export unavailable in this toolchain; report retained, no native-input claim")
    return run


def verdict_lines(output: str) -> List[str]:
    return [line for line in output.splitlines() if VERDICT_LINE.match(line)]


def toolchain_identity(targo: str) -> str:
    """Describe only the selected Targo's sibling compiler. This diagnostic
    is not a compiler/SDK attestation or a verification verdict."""
    trustc = Path(targo).absolute().with_name("trustc")
    unavailable = f"trustc identity unavailable from {trustc}"
    try:
        if not trustc.is_file() or not os.access(trustc, os.X_OK):
            return f"({unavailable}: no executable sibling)"
        proc = subprocess.run(
            [str(trustc), "-vV"], capture_output=True, text=True, encoding="utf-8", check=False, timeout=30
        )
    except subprocess.TimeoutExpired:
        return f"({unavailable}: probe timed out)"
    except UnicodeError:
        return f"({unavailable}: probe output is not UTF-8)"
    except OSError as error:
        return f"({unavailable}: {error})"
    if proc.returncode:
        return f"({unavailable}: probe exit {proc.returncode})"
    keep = [l for l in proc.stdout.splitlines() if l.startswith(("rustc ", "commit-hash", "trust:", "host"))]
    identity = " | ".join(keep) if keep else proc.stdout.strip()[:200]
    return f"{trustc}: {identity}" if identity else f"({unavailable}: empty probe output)"


def memory_evidence(data: dict, run: LaneRun) -> str:
    """One line of what rule (a) read, echoed for every run."""
    bound = "none" if run.rss_bound is None else f"{run.rss_bound / GIB:.3f} GiB"
    record = (data.get("verification_gate") or {}).get("determinism")
    if isinstance(record, dict):
        profile = record.get("budget_profile")
        schema = profile.get("schema") if isinstance(profile, dict) else None
        return (f"memory: peak <= {bound} (wait4 over targo's process tree); resource accounting: "
                f"budget schema {schema}, determinism {record.get('outcome')}; typed stops, not an inferred RSS ceiling")
    ceiling, why = memory_ceiling(data)
    notes = sum(1 for line in run.output.splitlines() if MEMORY_MENTION.search(line))
    limit = why if ceiling is None else ("disabled" if ceiling == 0 else f"{ceiling / GIB:.3f} GiB ({ceiling} bytes)")
    return (
        f"memory: peak <= {bound} (wait4 over targo's process tree); ceiling {limit} "
        f"(report unit_rustflags); trustc memory notes: {notes or 'none (census silent below 4 GiB)'}"
    )


def sort_findings(
    findings: Sequence[Tuple[str, str]],
) -> Tuple[List[Tuple[str, str]], List[Tuple[str, str]], List[Tuple[str, str]]]:
    """(failed, not_judged, set_aside) over (run, finding) pairs. A run with
    any NOT JUDGED finding is not evidence in either direction, so its other
    findings — consequences of whatever stopped it — are set aside, never
    counted as FAIL; FAIL is reserved for a JUDGED run whose verdict is wrong."""
    unjudged = [(r, f) for r, f in findings if f.startswith(NOT_JUDGED)]
    unjudged_runs = {r for r, _ in unjudged}
    failed = [(r, f) for r, f in findings if not f.startswith(NOT_JUDGED) and r not in unjudged_runs]
    set_aside = [(r, f) for r, f in findings if not f.startswith(NOT_JUDGED) and r in unjudged_runs]
    return failed, unjudged, set_aside


def record_run(stem: Path, run: LaneRun) -> None:
    """Keep what a run showed: `<stem>.log` (the terminal output) and
    `<stem>.lane.json` (exit status and the process-tree RSS bound), so a kept
    run can be re-judged offline exactly as the gate judged it."""
    (stem.parent / f"{stem.name}.log").write_text(run.output, encoding="utf-8")
    data = {"exit": run.code, "rss_bound_bytes": run.rss_bound}
    if run.report_dir is not None:
        data["report_dir"] = run.report_dir
    (stem.parent / f"{stem.name}.lane.json").write_text(json.dumps(data) + "\n", encoding="utf-8")


def judge(label: str, run: LaneRun, data: dict, expect_refuted: Set[str]) -> List[Tuple[str, str]]:
    """Rule (a)-(c) for one run (`data` is its report.json), printed and
    returned as (run, finding)."""
    print(f"    {memory_evidence(data, run)}")
    entries = [line for found in omitted_lists(run.output) for line in found.entries]
    withheld = sum(1 for line in entries if "; proof withheld at publication]" in line)
    print(f"    omitted from the published rows: {len(entries)} request(s), {withheld} withheld at publication")
    return [(label, r) for r in not_judged(data, run, expect_refuted)]


def mutant_workers(n_mutants: int, base: LaneRun, base_data: Optional[dict]) -> Tuple[int, int, str]:
    """(parallel runs, `-j` per run, what was measured and chosen) for the
    mutant runs, sized to the host NOW (scripts/host_scale.py): each run's
    memory cap is what the base run's process tree peaked at (the mutants
    are scoped copies of it; the verification ceiling when no reading
    exists), its CPU what the base run used per second of wall time, and the
    runs admitted are the ones whose caps fit the measured room and whose CPU
    fits the cores the host's load leaves. A run is never sped up or slowed
    by its neighbours' verdicts; only the wall clock it shares changes, which
    is why the CPU bound keeps a loaded host serial (a load-induced budget
    stop is NOT JUDGED, a failure, never a pass)."""
    import host_scale as hs

    r = hs.measure()
    ceiling = memory_ceiling(base_data)[0] if base_data else None
    if base.rss_bound:
        peak_mb, cap_why = max(1, base.rss_bound >> 20), "the base run's peak process"
    elif ceiling:
        peak_mb, cap_why = max(1, ceiling >> 20), "the verification memory ceiling"
    else:
        peak_mb, cap_why = hs.SEED["verify"][1], "seed (no reading)"
    per_run_cpu = 1
    if base.cpu_s and base.wall_s:
        per_run_cpu = max(1, int(-(-base.cpu_s // base.wall_s)))
    # A parallel run builds with -j per_run_cpu, so up to that many of its
    # processes can each reach the base run's peak at once; the base run's
    # sampled tree peak (built at Targo's default -j, never fewer jobs) bounds
    # a whole slot when it is the smaller.
    cap_mb = peak_mb * per_run_cpu
    if base.tree_mb and base.tree_mb < cap_mb:
        cap_mb, cap_why = base.tree_mb, "the base run's sampled tree peak"
    others = max(0.0, (r.load1 or 0.0) - per_run_cpu)
    free_cores = max(1, int(r.cores - others))
    want = max(1, min(n_mutants, free_cores // per_run_cpu))
    plan = hs.plan_jobs(r, cap_mb, want=want)
    workers = plan.jobs if not plan.refused else 1
    # One slot is the old serial gate exactly (Targo's default -j).
    jobs = per_run_cpu if workers > 1 else 0
    line = (
        f"mutant scheduling: {hs.describe('verified-contracts', r, plan, cap_why + f' x {per_run_cpu} job(s)')}; "
        f"{per_run_cpu} core(s) per run (base cpu/wall), {free_cores} core(s) free at load1 "
        f"{r.load1 if r.load1 is not None else '?'} -> {workers} parallel run(s)"
        + (f", -j {jobs} each" if jobs else ", Targo's default -j")
        + (" (no room for a second run: serial)" if plan.refused else "")
    )
    return workers, jobs, line


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=str(Path(__file__).resolve().parents[1]))
    ap.add_argument("--out", default=None, help="work directory (default <root>/target/verified-lane)")
    ap.add_argument("--keep", action="store_true", help="keep mutant source workspaces (reports and diagnostic inputs are always retained)")
    ap.add_argument("--base-only", action="store_true", help="skip the mutation controls")
    ap.add_argument("--serial", action="store_true", help="run the mutants one at a time (no host scaling)")
    args = ap.parse_args(argv)
    root = Path(args.root).resolve()
    out = Path(args.out).resolve() if args.out else root / "target" / "verified-lane"
    out.mkdir(parents=True, exist_ok=True)
    target_dir = out / "target"

    # The pre-run rules, stated once in `holding` (gate 0 reads the same).
    held = holding(root)
    if held.errors:
        raise SystemExit("\n".join(held.errors))
    laws = list(held.laws)
    law_set = set(laws)
    # The build-script premise (THE BUILD-SCRIPT PREMISE): the committed list
    # every run's build-script executions must equal, refused before any run.
    build_scripts, errors = load_build_scripts(root)
    if errors:
        raise SystemExit("\n".join(errors))
    ws_version = workspace_version(root)
    targo = resolve_targo()
    print(f"verified lane: {targo}")
    print(f"toolchain: {toolchain_identity(targo)}")
    print(f"laws held ({len(laws)}): {', '.join(laws)}")
    print(f"build scripts held ({len(build_scripts)}, {BUILD_SCRIPTS}): {', '.join(map(str, sorted(build_scripts)))}")

    # (run, finding): a finding that begins with NOT_JUDGED is a run the lane
    # cannot stand behind; any other is a verdict that went wrong.
    findings: List[Tuple[str, str]] = []

    # --- base: the real crate, in the workspace -----------------------------
    run = run_lane(targo, root, out / "base", target_dir, ["-p", CRATE])
    record_run(out / "base", run)
    print(f"\n== base: targo trust check --release -p {CRATE}  (exit {run.code})")
    for line in verdict_lines(run.output):
        print("   ", line)
    report = retained_report_dir(run, out / "base") / "report.json"
    if not report.is_file():
        findings.append(("base", "no report.json was written"))
    else:
        data = json.loads(report.read_text(encoding="utf-8"))
        findings += judge("base", run, data, set())
        carried, premise = check_build_scripts(data, build_scripts, ws_version)
        print(f"    {build_script_line(carried)}")
        findings += [("base", f) for f in premise]
        results = parse_report_data(data)
        findings += [("base", f) for f in check_rows(results, laws, law_set, set(), run.output)]
        findings += [("base", f) for f in check_subjects(results, SUBJECTS)]
        idx = by_leaf(results)
        for name in laws:
            fr = idx.get(name)
            if fr is not None:
                rows = ", ".join(f"{o.kind}:{o.status}/{o.assurance}/{o.validation}" for o in fr.obligations)
                print(f"    {name:48s} {fr.verdict:12s} {rows}")
    if run.code != 0:
        findings.append(("base", f"strict gate exit {run.code} (every obligation of the crate must prove)"))

    # --- mutants: same lane, standalone copies ------------------------------
    # Each mutant is its own workspace, report directory and (per parallel
    # slot) target directory; they share nothing but the host. The runs are
    # launched in parallel when the host has room (mutant_workers) and judged
    # one after another in MUTANTS order, so the log reads as a serial run.
    if not args.base_only:
        base_data = json.loads(report.read_text(encoding="utf-8")) if report.is_file() else None
        if args.serial:
            workers, jobs, how = 1, 0, "mutant scheduling: serial (--serial)"
        else:
            workers, jobs, how = mutant_workers(len(MUTANTS), run, base_data)
        print(f"\n{how}")
        slots: "queue.Queue[Path]" = queue.Queue()
        extra_dirs = [out / f"target-{i}" for i in range(1, workers)]
        for d in [target_dir] + extra_dirs:
            slots.put(d)

        def launch(m: Mutant) -> LaneRun:
            dest = out / "mutants" / m.name
            write_mutant_crate(root, dest, m, laws)
            tdir = slots.get()
            try:
                return run_lane(targo, dest, out / "mutants" / f"{m.name}.report", tdir,
                                ["-p", CRATE, *(["-j", str(jobs)] if jobs else [])])
            finally:
                slots.put(tdir)

        started = time.monotonic()
        with ThreadPoolExecutor(max_workers=workers) as pool:
            futures = [pool.submit(launch, m) for m in MUTANTS]
            mutant_runs = [f.result() for f in futures]
        print(f"mutant runs: {len(MUTANTS)} in {time.monotonic() - started:.0f} s wall over {workers} slot(s)")
        for d in extra_dirs:
            shutil.rmtree(d, ignore_errors=True)  # a later run rebuilds its dependencies anyway
        for m, run in zip(MUTANTS, mutant_runs):
            label = f"mutant {m.name}"
            scope = scoped_laws(m, laws)
            flips = set(expand_flips(m, laws))
            record_run(out / "mutants" / m.name, run)
            print(
                f"\n== {label}: {m.why}  (exit {run.code}; {len(flips)} of {len(scope)} "
                f"scoped laws must flip{'; trust-ir copied' if m.mutates_trust_ir else ''}; "
                f"{run.wall_s or 0:.0f} s)"
            )
            for line in verdict_lines(run.output):
                print("   ", line)
            report = retained_report_dir(run, out / "mutants" / f"{m.name}.report") / "report.json"
            if not report.is_file():
                findings.append((label, "no report.json was written"))
                continue
            # `flips` holds globs: the judge and the row check both take the
            # EXPANDED set, so an omitted or refuted request of a flipped law
            # is explained exactly when the row check expects it to flip.
            data = json.loads(report.read_text(encoding="utf-8"))
            findings += judge(label, run, data, flips)
            carried, premise = check_build_scripts(data, build_scripts, ws_version)
            print(f"    {build_script_line(carried)}")
            findings += [(label, f) for f in premise]
            results = parse_report_data(data)
            findings += [(label, f) for f in check_rows(results, scope, set(scope) - flips, flips, run.output)]
            if run.code == 0:
                findings.append(
                    (label, f"{NOT_JUDGED} expected refutation missing: strict gate exit 0 — the mutation was not refuted")
                )
            idx = by_leaf(results)
            for name in scope:
                fr = idx.get(name)
                if fr is not None and not fr.fully_proved() and name not in flips:
                    print(f"    {name:48s} {fr.verdict:12s} (must hold)")
            flipped = sum(1 for name in flips if name in idx and not idx[name].fully_proved())
            print(f"    {flipped} of {len(flips)} flipped laws not proved (each must also be named refuted)")

    if not args.keep:
        shutil.rmtree(out / "mutants", ignore_errors=True)

    print()
    failed, unjudged, set_aside = sort_findings(findings)
    unjudged_runs = sorted({r for r, _ in unjudged})
    for r, f in failed:
        print(f"FAIL: {r}: {f}", file=sys.stderr)
    for r, f in unjudged:
        print(f"{NOT_JUDGED} {r}: {f[len(NOT_JUDGED):].strip()}", file=sys.stderr)
    for r, f in set_aside[:5]:
        print(f"set aside (run NOT JUDGED, not evidence): {r}: {f}", file=sys.stderr)
    if len(set_aside) > 5:
        print(f"set aside: {len(set_aside) - 5} more finding(s) of NOT JUDGED runs", file=sys.stderr)
    if failed:
        print(
            f"verified-contracts: FAIL ({len(failed)} finding(s) in judged runs; "
            f"{len(unjudged_runs)} run(s) NOT JUDGED)",
            file=sys.stderr,
        )
        return 1
    if unjudged:
        print(
            f"verified-contracts: NOT JUDGED ({len(unjudged)} reason(s) over {len(unjudged_runs)} run(s): "
            f"{', '.join(unjudged_runs)}) — no verdict of these runs is evidence in either direction "
            "(scripts/verified_contracts.py, THE RULE)",
            file=sys.stderr,
        )
        return 1
    print(
        f"verified-contracts: PASS — {len(laws)} laws proved (Certified, KernelRechecked) on "
        f"{CRATE}; {len(MUTANTS) if not args.base_only else 0} same-shape mutants refuted on exactly the laws they break; "
        "every run JUDGED (peak RSS below the memory ceiling, no budget stop, no unexplained published or "
        f"omitted request); every run's build-script executions equal {BUILD_SCRIPTS} "
        f"({len(build_scripts)}, run uncontained: P-CORESIDENT)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
