//! The pure decision tables of the TrustIr validator and format, with their
//! English laws stated as Trust contracts and PROVED.
//!
//! Every table is a total function over `Copy` enums and `u64` payloads whose
//! behavior the documentation used to state as an English table alone. The
//! tables stay (they are the readable form), and each row now cites the
//! contract that proves it: a wrapper in [`laws`] whose `ensures` clause is
//! discharged by `targo trust check --release` and re-checked by the Clean
//! kernel (`assurance: Certified`, `validation: KernelRechecked`,
//! `axiom_closure: Empty`). The standing gate `verified-contracts`
//! (`scripts/verified_contracts.py`, `scripts/ci_gates.sh` gate 13) runs that
//! lane, requires every law row proved, and runs same-shape mutants of each
//! table that must flip exactly the rows they falsify. Before any run it also
//! checks that every law's body is EXACTLY one call of its own table at the
//! cell its name spells (`WIRING` in the gate script): a batched mutant that
//! edits several tables at once flips a law whichever of them the law calls,
//! so the flip shows only that a law is not proved about a constant; the
//! wiring check is what ties each law to its table. It also checks that every
//! table over enum cells has a law at EVERY cell of its operand enums, read
//! from their definitions (`cell_completeness`): the "PROVED, every cell"
//! comments on the tables are held there, so a new variant lands with its
//! laws or gate 13 refuses to run. [`coverage_supports`] ranges over `u64`
//! payloads and is not enumerated; its rows are its named laws.
//!
//! # The tables
//!
//! Five live HERE (a validator rule with no home in the format crate):
//! [`coverage_supports`], [`license_admits_body`],
//! [`visibility_contradicts_linkage`], [`evidence_admits_kind`] and
//! [`proof_ref_kind_is_ambiguous`]. `trust-ir-build` calls each at its old
//! path. The rest are RESIDENT IN TRUST-IR, where the format code that reads
//! them lives, and their laws here call them across the crate boundary
//! (measured 2026-09-29: a law calling a trust-ir table proves in this lane,
//! and a mutated trust-ir copy refutes exactly the mutated rows):
//!
//! | table (trust-ir) | law family | who reads it |
//! |---|---|---|
//! | `AllocOrigin::is_reference_counted` | `rc_*` | the interpreter's `Retain`/`Release`/`IsUnique`/`Dealloc` rules |
//! | `Linkage::is_interposable` | `interposable_*` | import authentication R2/R4 (`InterposableFarSite`); the WS3.8 pointer-constant rule (`PointerConstantRefusal::InterposableLinkage`) |
//! | `Linkage::is_module_local` | `module_local_*` | `SymbolNotExported`, the linked walk's export index, [`visibility_contradicts_linkage`] |
//! | `Linkage::requires_contract_surface` | `contract_surface_linkage_*` | the binary writer's v41 selection |
//! | `ProofStatus::is_discharged_tier` | `discharged_tier_*` | import R7, the linked restatement, the `proved` rule, lineage, transforms, the evidence authority predicates, bundles, digests |
//! | `ProofStatus::is_kernel_tier` | `kernel_tier_*` | the validator's `CleanCic` rules: the certified-evidence re-check, unbound / source-unbound certificates, the `clean-kernel-tv` license evidence, the kernel-tier `ProofRef` authority set, source-to-silicon |
//! | `Ordering::is_legal_for_load` / `is_legal_for_store` | `atomic_load_*`, `atomic_store_*` | `IllegalAtomicOrdering` |
//! | `CallingConv::is_abi_surface`, `EnumTagRepr::is_abi_surface` | `cc_abi_surface_*`, `tag_abi_surface_*` | the binary writer's v45 selection |
//! | `HardwareVectorContractStatus::fail_closed` | `hv_fail_closed_*` | the x86-64 vector-compare manifest's `fail_closed` and consumer-policy rows a consumer must honor |
//! | `ExternRefSite::admits_shape` | `backed_by_*`, `inherited_*`, `call_edge_*`, `handle_declaration_*` | import R7 (`ExternRefSite::admits` delegates) |
//! | `ObligationKindShape::is_grounded_contract_kind` / `free_var_is_proved` / `is_assert_class` | `grounded_contract_kind_*`, `free_var_proved_*`, `assert_class_*` | the Clean-expr grounder; assert-class routing |
//! | `InstShape::is_terminator` | `terminator_*` | block structure (`Inst::is_terminator` delegates) |
//! | `trust_ir::value::fresh_id_has_successor` / `fresh_run_fits` / `fresh_id_below` | `fresh_successor_*`, `fresh_run_fits_*`, `fresh_below_*` | the one fresh-id rule (`FreshIds` / `IdRun`, r11 R1): exhaustion at `u32::MAX`, the all-or-nothing run, the reserved bound |
//!
//! The fresh-id tables range over `u32` PAYLOADS, as [`coverage_supports`]
//! ranges over `u64` ones, rather than enum cells: each has one law over every
//! input, stating the exact comparison the table is (`result == (id <
//! 4294967295)`), and one law per boundary row (at `u32::MAX`, below it, at 0;
//! the room filled and exceeded; the bound and the id under it). They are
//! comparisons because that is what proves. Measured 2026-10-01 on trustc
//! 321aaeda7: a law over the generic cursor
//! (`FreshIds::<ValueId>::after([..]).is_exhausted()`, `IdRun::span(0,
//! u32::MAX).is_none()`) stays UNKNOWN; a widening `as u64` is an unsupported
//! contract predicate; `u32::MAX - first` inside a table leaves its overflow
//! row UNKNOWN; a single comparison of `u32` parameters proves, and so does
//! each all-constant cell tried; a cell that fixes one argument proves case by
//! case (`fresh_run_fits(0, room)` does, `fresh_id_below(id, 0)` stays UNKNOWN
//! and is not stated). So the cursor computes the room above an id as the
//! complement `!first` and asks the table, and decides by the tables alone:
//! the value a decision licenses is computed with `wrapping_*`, which decides
//! nothing, so a cut read wraps. That it asks is code, tested
//! (`the_cursor_decides_by_the_fresh_id_tables` and
//! `fresh_ids_are_one_past_the_highest_and_never_wrap` go red when a read is
//! cut), not proved.
//!
//! A table over a DATA-CARRYING enum is stated over its `Copy` shape
//! (`InstShape`, `ObligationKindShape`, `ProofEvidenceShape`, generated by
//! trust-ir's `variant_shape!` from one variant list, so the projection is
//! exhaustive by construction — type-level, not proved), and the by-reference
//! API delegates to it.
//!
//! # What "proved" means here, exactly
//!
//! * **The verdict is about OPTIMIZED MIR** (Trust guide §9h). A law is a
//!   wrapper that calls the table; its clause is about the table only because
//!   rustc's MIR inliner puts the table's body inside the wrapper at
//!   `--release`, and for every constant-valued law the case analysis is then
//!   performed by the optimizer (the wrapper folds to `const true` / `const
//!   false`) and the kernel-rechecked row is that constant. Only the
//!   magnitude-order laws (`result == (have >= need)`) make the solver reason
//!   about a non-constant return. Without `-O` there is NO proof route:
//!   every wrapper's call is an opaque uncontracted callee and every row is
//!   UNKNOWN (measured: 8 proved / 46 unknown on the same crate).
//! * **The proofs hinge on the inliner's cost heuristic** (default hint
//!   threshold 100; the shipped `coverage_supports` clears it with a margin of
//!   at most ~20 units, measured 2026-09-24). A table one arm heavier is NOT
//!   refuted but declined by the inliner, after which every wrapper is
//!   fail-closed UNKNOWN. That is why the gate asserts each named row's status
//!   and never just the exit code, and why its mutants are SAME-SHAPE edits.
//!   Measured 2026-09-29: in this crate's verified pipeline every or-pattern
//!   alternative of a LOCAL `matches!` is its own block (about 5 units each,
//!   plus 20 for a switch of more than 3 targets), so a local table tops out
//!   near 14 alternatives; `#[inline]` and `#[inline(always)]` do not raise
//!   the threshold. A TRUST-IR table is inlined from the dependency's
//!   optimized MIR, where those blocks are merged and alternatives cost
//!   nothing — which is why the 62-way `InstShape::is_terminator` proves
//!   there, while a local copy of the shape projection left a row UNKNOWN.
//!   `ExternRefSite::admits_shape` is inlined at 95 of 100: a new ROW with its
//!   own kind list would push it over (more kinds in a row cost nothing).
//! * **Refutations are not published as `FAILED`.** The fork demotes a native
//!   CHC refutation to UNKNOWN before publication; the evidence that a mutant
//!   was distinguished is the runner's `refuted obligation` line naming the
//!   row, plus the strict gate's non-zero exit. The gate requires both.
//! * **A row counts only from a JUDGED run.** On the installed seal (trustc
//!   321aaeda7) the per-function budget is one boolean fed by steps, the clock
//!   AND peak RSS, and the phase checkpoint that discards a truncated result
//!   does not see the RSS source: `verify_budget::budget_exhausted` answers
//!   true at the memory ceiling, `verify_budget::exhausted_readonly` (what the
//!   checkpoint reads) reads only steps and the clock. One such trip made
//!   `-Ztrust-policy=strict` and `=certify` exit 0 with `proved: trivially
//!   panic-free` for the counter-program p4 (`y + 1` after `y = u32::MAX`,
//!   which panics), where the same run without the ceiling reports
//!   `[overflow:add] FAILED`. Evidence class **external** (the seal's source,
//!   and that measurement on the seal's trustc, reproduced 2026-09-29). So the
//!   gate judges a run — the base run and every mutant run — only if the peak
//!   RSS of its process tree stayed below the ceiling its report records, no
//!   row or diagnostic names a budget stop, and every compiler request is
//!   explained — a published row proved + kernel-rechecked, a request
//!   publication omitted from the report only as a favorable claim withheld
//!   at publication, or either inside an expected refutation; anything else,
//!   a missing expected refutation included, fails as `NOT JUDGED`, its proved
//!   rows included. That refusal is evidence class **test**
//!   (`scripts/tests/test_verified_contracts.py`, over real runs of this
//!   lane), not proof. The rule, its report fields and its measurements are
//!   stated once, as THE RULE in `scripts/verified_contracts.py`.
//! * **The build-script premise (P-CORESIDENT).** `targo trust check` runs
//!   the build scripts of the lane's graph outside the proof channel,
//!   uncontained, as the same uid (Trust blocker B5), so every law proved
//!   here rests on them. Which scripts they are is checked against
//!   `scripts/gates/verified-contracts-build-scripts.tsv` (evidence class
//!   **test**); the rule and its measurements are stated once, as THE
//!   BUILD-SCRIPT PREMISE in `scripts/verified_contracts.py`. That the
//!   scripts did not interfere with the run is a premise, not checked, until
//!   B5's contained, sealed build scripts land.
//! * **Spelling rules, measured 2026-09-24.** The clause grammar has NO enum
//!   vocabulary (`needs == CoverageBound::Unrecorded`, `matches!(..)`, `x is
//!   V` are each `unsupported contract predicate expression`), so a law over
//!   a VARIANT is spelled once per variant and a law over a PAYLOAD keeps the
//!   payload as a universally quantified `u64` parameter. `ensures result`
//!   proves where `ensures result == true` over a same-variable comparison
//!   does not; `ensures result == false` proves every false law. A table
//!   returning an ENUM is not provable in any spelling (`matches!` and `==`
//!   on the result, by-value or by-reference, 12/12 rows unknown), which is
//!   why [`license_admits_body`] is a `bool` projection. A table over a
//!   REFERENCE (`&ObligationKind`, `&Inst`) stays UNKNOWN — a discriminant
//!   read through a promoted reference (measured 2026-09-29) — hence the
//!   `Copy` shapes. A law per CELL is the reliable form: an enum-quantified
//!   law that makes two calls is mixed (some prove, some stay UNKNOWN), so
//!   an implication between two tables (`kernel tier => discharged tier`) is
//!   carried as the two tables' cells, and its composition is a hand step.
//!   Every law's contract is exactly one `ensures` of `ENSURES_SHAPES` in
//!   `scripts/verified_contracts.py` (`result`, `result == false`, `result ==
//!   (<relation>)`), and gate 13 refuses any other before a run: gate 0 reads
//!   a law's verdict from it (rule E5), so a cited law's verdict in the
//!   ratifications and TRUST.md is the one its `ensures` states.
//! * **Not carried, and why** (each stays an English or tested claim):
//!   L8 transitivity of [`coverage_supports`] — every spelling leaves one
//!   per-path row unknown/refuted (three inlined copies of the match do not
//!   stay related in the CHC encoding); both halves are proved (the
//!   magnitude-order laws and [`laws::u64_ge_is_transitive`]) and their
//!   composition is a hand step. The single enum-quantified statement of
//!   "`Unbounded` supplies every demand" leaves the clause-level seal marker
//!   unknown (the per-variant forms prove). The `#[non_exhaustive]`
//!   unknown-variant row of [`coverage_supports`] is about a value no crate
//!   can construct, so no wrapper can state it.
//! * **Nothing outside these tables is proved.** `HandleTy::validate`'s
//!   lexical rules and `is_admitted_obligation_namespace`'s byte-exact
//!   membership were measured in the same lane (2026-09-25) and fail to lower:
//!   `str::chars` / closures / `split` report `unsupported MIR` (`Const::
//!   Closure`, `Rvalue::PtrOffset`, `Rvalue::Cast`), and `<[&str]>::contains`
//!   produces an invalid native solve input. Their English tables stay where
//!   they are, each with a note pointing here. Measured 2026-09-29 and also
//!   NOT carried, each staying tested: `EnumTagRepr::fits` (its `i128` range
//!   laws are UNKNOWN in this lane; nearest proved contract:
//!   `EnumTagRepr::is_abi_surface`); trust-ir-build's
//!   `obligation_kind_admits_site_instruction` (WS1.8 rule (c)) — its four
//!   kind ROWS prove as trust-ir `InstShape` methods, but hosting validator
//!   rows in the format crate is an owner decision not yet taken, and its
//!   kind→row DISPATCHER is UNKNOWN in every spelling tried (nearest proved
//!   contracts: [`evidence_admits_kind`], rule (d), and
//!   `InstShape::is_terminator`); the x86 vector-compare cell reader
//!   `chc_x86_vector_icmp_cell_status` (data-driven: an iterator over a
//!   descriptor array and a string key; nearest: `hv_fail_closed_*`).
//!   Separately, trust-ir-build's `core_reflection` byte profile spells
//!   "replaceable linkage" as `{Weak, LinkOnce}` and does NOT route through
//!   `Linkage::is_interposable`, which also counts `ExternalWeak`: whether
//!   that divergence is intended is an open owner question, and the gate's
//!   `trust-ir-neighbour-spellings` mutant is exactly that spelling (it
//!   refutes `interposable_external_weak`).
//!
//! # Why a separate crate
//!
//! The verified lane must verify a SMALL unit: `targo trust check` excludes
//! every dependency unit (`dependency-policy-excluded`, measured) but verifies
//! every function of the primary package, and `trust-ir-build` has thousands.
//! A law need NOT share a compilation unit with its table — this sentence
//! used to say it must, and that was measured false on 2026-09-29: the
//! inliner reads a dependency's optimized MIR, so a law here calling a
//! trust-ir table proves, and needs no dependency cycle (trust-ir keeps its
//! tables and calls them itself). The validator-only tables live here,
//! `trust-ir-build` depends on this crate and calls or re-exports them at
//! their old paths (`trust_ir_build::coverage_supports`,
//! `trust_ir_build::UnlicensedBodyPolicy`,
//! `trust_ir_build::evidence_admits_obligation_kind`), and the lane is
//! `targo trust check --release -p trust-ir-laws` (about 55 s for the 313
//! laws, trust-ir compiled once as an excluded dependency). A gate mutant of a
//! trust-ir table builds against a mutated COPY of trust-ir.
//!
//! `laws` is compiled only under `cfg(trust_verify)`, which the Trust compiler
//! sets by itself when its verification pass is on: stock rustc never reads
//! the file (a cfg'd-out out-of-line module is never parsed — measured on
//! rustc 1.96 with the file containing `ensures`), and neither does the
//! `targo --unverified` lane every other gate runs in.

use trust_ir::proof::{CoverageBound, ObligationKindShape, ProofEvidenceShape};
use trust_ir::{BodyGate, Linkage, Visibility};

/// The contract wrappers. Compiled only by the Trust compiler with its
/// verification pass on (`cfg(trust_verify)`); see the crate docs.
#[cfg(trust_verify)]
#[rustfmt::skip]
pub mod laws;

/// Whether a far discharge's recorded coverage `far` is AT LEAST AS STRONG as
/// what a local cross-crate claim `needs` — linked rule L9's ordering.
///
/// This is the per-PAIR order. L9 applies it to the SET of bounds the far
/// module recorded and demands that EVERY one of them supply — see
/// `coverage_verdict` (private, trust-ir-build `linked.rs`) for why the
/// quantifier is `all`, not `any`.
///
/// # The pairs, exhaustively
///
/// [`CoverageBound`] has four variants and is `#[non_exhaustive]`. The
/// ordering is a PARTIAL order with two incomparable middle rungs, not a
/// number line, so every admitted pair is enumerated and everything else
/// fails closed — the discipline [`trust_ir::ExternRefSite::admits`] already
/// sets for an unknown `ObligationKind`.
///
/// | far \ needs | `Unbounded` | `UnwindBounded { depth: n }` | `ModelBounded { size: n }` | `Unrecorded` |
/// |---|---|---|---|---|
/// | `Unbounded` | yes | yes | yes | yes |
/// | `UnwindBounded { depth: d }` | **no** | `d >= n` | **no** | yes |
/// | `ModelBounded { size: s }` | **no** | **no** | `s >= n` | yes |
/// | `Unrecorded` | **no** | **no** | **no** | yes |
/// | a variant this build does not know | **no** | **no** | **no** | yes |
///
/// Reading the rows and columns — each bullet names the [`laws`] that prove
/// it (kernel-rechecked, over every `u64` payload where one appears):
///
/// * **`Unbounded` supplies everything.** "All inputs; unbounded behavior" is
///   the top of the order, so it meets any demand.
///   `coverage_unbounded_supplies_{unbounded,unwind,model,unrecorded}`.
/// * **Same axis compares by magnitude.** A 9-deep unwinding covers a
///   7-deep demand; a 7-deep unwinding does not cover a 9-deep one. Likewise
///   a size-9 finite model covers a size-4 demand.
///   `coverage_{unwind,model}_is_magnitude_order` (`result == (have >= need)`)
///   and, as its instance, `coverage_reflexive_{unbounded,unwind,model}`.
/// * **The two bounded rungs are INCOMPARABLE.** `UnwindBounded` is a
///   loop-unwinding/path depth and `ModelBounded` is a finite model instance
///   size; neither is evidence about the other's axis at any magnitude, so
///   `UnwindBounded { depth: 10_000 }` does not supply
///   `ModelBounded { size: 2 }` and vice versa. Folding them into one integer
///   would be the whole bug this rule exists to prevent.
///   `coverage_unwind_never_supplies_model`,
///   `coverage_model_never_supplies_unwind` — universally over BOTH payloads,
///   so "at every magnitude" is literal.
/// * **Neither bounded rung supplies `Unbounded`.** This is the case the
///   residual ledger named: an importer whose claim is unqualified may not
///   rest on a depth-1 bounded model check.
///   `coverage_{unwind,model}_never_supplies_unbounded`.
/// * **`Unrecorded` IS NOT A WILDCARD as a supply.** Its own rustdoc says so
///   — "NEVER equivalent to `CoverageBound::Unbounded`; an import must not
///   gain unbounded standing by omission" — so it supplies no positive grade,
///   not even `UnwindBounded { depth: 0 }`, which is still an affirmative
///   statement about what was explored.
///   `coverage_unrecorded_never_supplies_{unbounded,unwind,model}` (`n`
///   ranges over all of `u64`, so `depth: 0` is an instance).
/// * **`Unrecorded` as a DEMAND is met by anything, including itself.** A
///   local row that records no grade makes no coverage claim, so there is
///   nothing for the far side to under-support. That is the `needs` column,
///   not the `far` row; the asymmetry is the point. Note where this column is
///   CONSUMED: `check_coverage` counts a no-grade demand as NOT ESTABLISHED
///   and never reaches `coverage_verdict` with it, so the column states a
///   fact about the order and is not a route to `coverage_supported`. A site
///   admitted because it asked for nothing and a site admitted because the
///   far bound dominates are different facts, and they are tallied apart.
///   `coverage_unrecorded_demand_met_by_{unbounded,unwind,model,unrecorded}`
///   and the ONE enum-quantified law this build can prove,
///   `coverage_unrecorded_demand_met_by_any` (the first arm matches every
///   `far`, so the match folds to `true`).
/// * **An unknown variant fails closed in the `far` position** — this build
///   cannot know that a grade it does not enumerate dominates one it does,
///   and `Unbounded` is deliberately not assumed to dominate an unknown
///   DEMAND either. NOT PROVED: no crate can construct a variant this build
///   does not enumerate, so no wrapper can state the row; it remains this
///   sentence plus the `_ => false` arm.
///
/// Transitivity (a `>=` chain along one axis) is likewise NOT a proved row —
/// see the crate docs — and the mutants the gate runs are the ones that
/// distinguish this body from its neighbors: `UnwindBounded` supplying
/// `ModelBounded` (in place of the `Unbounded` arm, same tree shape) flips
/// exactly `coverage_unwind_never_supplies_model` and
/// `coverage_unbounded_supplies_model`; `have > need` on the unwind arm flips
/// exactly `coverage_reflexive_unwind` and `coverage_unwind_is_magnitude_order`.
///
/// The tested twin of this table, over every pair, is
/// `coverage_supports_is_the_ratified_partial_order_over_every_pair`
/// (trust-ir-build, `linked_import_authentication.rs`).
#[must_use]
pub fn coverage_supports(far: CoverageBound, needs: CoverageBound) -> bool {
    match (far, needs) {
        // The `needs` column for `Unrecorded`: no grade claimed, nothing to
        // under-support. Evaluated first so it also covers an unknown `far`.
        (_, CoverageBound::Unrecorded) => true,
        (CoverageBound::Unbounded, CoverageBound::Unbounded) => true,
        (CoverageBound::Unbounded, CoverageBound::UnwindBounded { .. }) => true,
        (CoverageBound::Unbounded, CoverageBound::ModelBounded { .. }) => true,
        (
            CoverageBound::UnwindBounded { depth: have },
            CoverageBound::UnwindBounded { depth: need },
        ) => have >= need,
        (
            CoverageBound::ModelBounded { size: have },
            CoverageBound::ModelBounded { size: need },
        ) => have >= need,
        // Cross-axis, `Unrecorded` as a supply, and any variant this build
        // does not enumerate on either side.
        _ => false,
    }
}

/// The SHAPE of a function's codegen license — [`BodyGate`] with its
/// `authority` string projected away, so the license decision is a table over
/// `Copy` values. `Copy`/`Eq` only: a `Debug` impl is a `Formatter::write_str`
/// call, which is an unsupported row in the verified lane and would turn this
/// crate's strict gate red for a reason that is not a law.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum GateShape {
    /// `body_gate: None` — no licensing claim, the pre-v41 grandfather state.
    Absent,
    /// `Some(BodyGate::Ungated)` — an AFFIRMATIVE "no gate was applied".
    Ungated,
    /// `Some(BodyGate::Gated { .. })` — gated by some authority; whether that
    /// authority is recognized or evidence-backed is decided AFTER admission,
    /// by the evidence rules, never by this table.
    Gated,
}

impl GateShape {
    /// The shape of a function's `body_gate`. A three-arm projection, tested
    /// (a by-reference match is not a provable wrapper in the verified lane —
    /// measured, `Option<&BodyGate>` rows stay unknown).
    #[must_use]
    pub fn of(gate: Option<&BodyGate>) -> Self {
        match gate {
            None => Self::Absent,
            Some(BodyGate::Ungated) => Self::Ungated,
            Some(BodyGate::Gated { .. }) => Self::Gated,
        }
    }

    /// The shape's name, for diagnostics (this crate carries no `Debug`
    /// impls; see the type docs).
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Absent => "Absent",
            Self::Ungated => "Ungated",
            Self::Gated => "Gated",
        }
    }
}

/// What codegen admission does with a body that makes NO licensing claim
/// (`body_gate: None`, the pre-v41 grandfather state).
///
/// No `Debug` or `Hash` derive: each is a call the verified lane cannot
/// discharge (`Formatter::write_str`, `Hasher::write`), and this crate's strict
/// gate is green as a whole because every function in it proves. Render it
/// with [`Self::name`].
#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub enum UnlicensedBodyPolicy {
    /// Refuse it as `ValidationError::UnlicensedBodyForCodegen` — the
    /// fail-closed default of `validate_module_for_codegen`.
    #[default]
    Refuse,
    /// Admit it. This is exactly the documented caller-owned filter (drop
    /// `UnlicensedBodyForCodegen`, keep `UngatedBodyForCodegen`), spelled as a
    /// policy so a grandfathering consumer need not re-implement it. An
    /// affirmative `Ungated` body is refused under either policy — a PROVED
    /// law, `laws::license_ungated_refused_under_any_policy`.
    Permit,
}

impl UnlicensedBodyPolicy {
    /// The policy's name, for diagnostics.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Refuse => "Refuse",
            Self::Permit => "Permit",
        }
    }
}

/// The codegen-license ADMISSION table: does the license layer let a body
/// WITH A BODY proceed — to the evidence and recognition rules for a gated
/// body, to codegen for an unlicensed one under [`UnlicensedBodyPolicy::Permit`]?
/// `false` is a refusal, and the shape names the refusal's error variant
/// (`Ungated` → `UngatedBodyForCodegen`, `Absent` → `UnlicensedBodyForCodegen`).
///
/// | shape     | `Refuse`                            | `Permit` |
/// |-----------|-------------------------------------|----------|
/// | `Gated`   | admit (evidence rules follow)       | admit    |
/// | `Ungated` | refuse (`UngatedBodyForCodegen`)    | refuse   |
/// | `Absent`  | refuse (`UnlicensedBodyForCodegen`) | admit    |
///
/// Proved laws ([`laws`], kernel-rechecked): `license_gated_admitted_under_any_policy`,
/// `license_ungated_refused_under_any_policy` (the "an affirmative `Ungated`
/// body is refused under either policy" sentence), `license_absent_refused_under_refuse`
/// (the fail-closed default), `license_absent_admitted_under_permit` (the
/// grandfather filter). The gate's mutants: admitting `(Absent, Refuse)` flips
/// exactly `license_absent_refused_under_refuse`; admitting `Ungated` flips
/// exactly `license_ungated_refused_under_any_policy`.
///
/// What stays TESTED, not proved: that the two refusals are DIFFERENT error
/// values (the reason the wire tag is three-valued) — an enum-valued table is
/// not provable in this lane (crate docs), so the variant choice is made by
/// the caller from the shape and pinned by `validate_module_for_codegen`'s
/// doctest and `g3_codegen_license.rs`.
#[must_use]
pub fn license_admits_body(shape: GateShape, unlicensed: UnlicensedBodyPolicy) -> bool {
    match (shape, unlicensed) {
        (GateShape::Gated, _) => true,
        (GateShape::Ungated, _) => false,
        (GateShape::Absent, UnlicensedBodyPolicy::Refuse) => false,
        (GateShape::Absent, UnlicensedBodyPolicy::Permit) => true,
    }
}

/// Whether a function's `linkage` and `visibility` CONTRADICT each other —
/// the v45 validator refusal `ContradictoryFunctionVisibility` (WS3.10).
///
/// Visibility is orthogonal to linkage (it answers "may another module SEE
/// this once linked"), except that a MODULE-LOCAL symbol
/// ([`Linkage::is_module_local`]: `Internal` / `Private`) has no linked
/// visibility to restrict, so claiming `Hidden` or `Protected` for one is a
/// contradiction a consumer cannot lower. `Default` never contradicts.
///
/// | linkage \ visibility | `Default` | `Hidden` | `Protected` |
/// |---|---|---|---|
/// | `Internal`, `Private` | no | **contradicts** | **contradicts** |
/// | every other linkage | no | no | no |
///
/// Proved laws ([`laws`], kernel-rechecked): the six module-local cells
/// `visibility_{internal,private}_{default,hidden,protected}`, and one law per
/// non-local linkage quantified over every visibility,
/// `visibility_<linkage>_never_contradicts`. The module-local column is
/// [`Linkage::is_module_local`], a trust-ir table this one calls across the
/// crate boundary, itself proved cell by cell (`module_local_*`).
#[must_use]
pub fn visibility_contradicts_linkage(linkage: Linkage, visibility: Visibility) -> bool {
    linkage.is_module_local() && matches!(visibility, Visibility::Hidden | Visibility::Protected)
}

/// The evidence→kind admission table of WS1.8 rule (d)
/// (`ValidationError::EvidenceKindMismatch`): may evidence of this shape
/// discharge an obligation of that kind?
///
/// | evidence | admitted kinds |
/// |---|---|
/// | `TranslationValidation` | `TranslationValidation` only |
/// | `GammaCrownBound` (a neural-network output bound) | `Postcondition`, `Custom` only |
/// | every other evidence shape | every kind (`CleanCic` and `InheritedFromCallee` have their own, stronger rules) |
///
/// trust-ir-build's `evidence_admits_obligation_kind(&ProofEvidence,
/// &ObligationKind)` is this table at the two shapes. Proved laws
/// ([`laws`]): `evidence_tv_<kind>` and `evidence_gamma_<kind>`, one per kind
/// shape, and `evidence_<shape>_unconstrained` for each other evidence
/// shape, quantified over every kind.
#[must_use]
pub fn evidence_admits_kind(evidence: ProofEvidenceShape, kind: ObligationKindShape) -> bool {
    match evidence {
        ProofEvidenceShape::TranslationValidation => {
            matches!(kind, ObligationKindShape::TranslationValidation)
        }
        ProofEvidenceShape::GammaCrownBound => matches!(
            kind,
            ObligationKindShape::Postcondition | ObligationKindShape::Custom
        ),
        _ => true,
    }
}

/// The category-AMBIGUOUS obligation kinds: a kind whose rows state a
/// contract, invariant, refinement, validated transform or temporal property
/// rather than one specific safety category — `Precondition`,
/// `Postcondition`, `LoopInvariant`, `TypeInvariant`, `RefinementType`,
/// `TranslationValidation`, `TemporalSafety`, `Liveness`.
///
/// The validator's `ProofRef` category rule (fast-1, tightened by WS1.1)
/// reads it through trust-ir-build's `proof_ref_kind_is_ambiguous`, which is
/// this table at the kind's shape. Proved laws ([`laws`]): `ambiguous_<kind>`,
/// one per kind shape.
#[must_use]
pub fn proof_ref_kind_is_ambiguous(kind: ObligationKindShape) -> bool {
    matches!(
        kind,
        ObligationKindShape::Precondition
            | ObligationKindShape::Postcondition
            | ObligationKindShape::LoopInvariant
            | ObligationKindShape::TypeInvariant
            | ObligationKindShape::RefinementType
            | ObligationKindShape::TranslationValidation
            | ObligationKindShape::TemporalSafety
            | ObligationKindShape::Liveness
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The tested twin of the license table, over every cell.
    #[test]
    fn license_table_every_cell() {
        use GateShape::{Absent, Gated, Ungated};
        use UnlicensedBodyPolicy::{Permit, Refuse};
        assert!(license_admits_body(Gated, Refuse));
        assert!(license_admits_body(Gated, Permit));
        assert!(!license_admits_body(Ungated, Refuse));
        assert!(!license_admits_body(Ungated, Permit));
        assert!(!license_admits_body(Absent, Refuse));
        assert!(license_admits_body(Absent, Permit));
    }

    #[test]
    fn gate_shape_projects_every_body_gate() {
        assert!(GateShape::of(None) == GateShape::Absent);
        assert!(GateShape::of(Some(&BodyGate::Ungated)) == GateShape::Ungated);
        let gated = BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: None,
        };
        assert!(GateShape::of(Some(&gated)) == GateShape::Gated);
        assert_eq!(GateShape::Gated.name(), "Gated");
        assert_eq!(UnlicensedBodyPolicy::default().name(), "Refuse");
    }
}
