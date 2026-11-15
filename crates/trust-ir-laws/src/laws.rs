//! The proved laws of this crate's decision tables and of the trust-ir tables
//! it calls — one wrapper per row of each English table, each with a Trust
//! `ensures` contract.
//!
//! Compiled only under `cfg(trust_verify)` (the Trust compiler with its
//! verification pass on); see the crate docs for what a proof here means, the
//! spelling rules, and the rows that are NOT carried. Every `pub fn` in this
//! file is a law: `scripts/verified_contracts.py` derives the list it holds the
//! lane to from this file, so nothing else may be declared `pub` here. Each
//! law's body ends at a column-0 `}` (the gate cuts a mutant's copy of this
//! file down to the mutant's law families along those lines).
//!
//! Naming: `coverage_*` are laws of [`coverage_supports`], `license_*` of
//! [`license_admits_body`], `visibility_*` of [`visibility_contradicts_linkage`],
//! `evidence_*` of [`evidence_admits_kind`], `ambiguous_*` of
//! [`proof_ref_kind_is_ambiguous`]; every other family is a law of a table
//! RESIDENT IN TRUST-IR, called across the crate boundary (its section header
//! names the table). A parameter is a payload the law ranges over (all of
//! `u64` or `u32`, or every value of a `Copy` enum passed by value); a law
//! with no parameter is one CELL of its table, and its name is
//! `<family>_<variant>` — or, for a table over `u32` payloads (the fresh-id
//! rule's `fresh_*` families), the boundary row it states.
//! A law's body is EXACTLY one call of its family's table, at the cell its
//! name spells: the gate derives each name from its body (`WIRING` in
//! `scripts/verified_contracts.py`) and refuses any other body before a run.
//! A `fresh_*` law is wired to its exact call, its own parameters or
//! constants. The `coverage_*` and `license_*` laws (named before 2026-09-29)
//! are wired by a family glob instead: their body must be one call of their
//! table, but its arguments are not bound to the law's name.
//!
//! `#[rustfmt::skip]` sits on the `mod` item so stock `rustfmt` never resolves
//! this file; it is formatted by `trustfmt` directly.

use super::*;
use trust_ir::inst::{AllocOrigin, Ordering};
use trust_ir::proof::ProofStatus;
use trust_ir::request::HardwareVectorContractStatus;
use trust_ir::ty::EnumTagRepr;
use trust_ir::value::{fresh_id_below, fresh_id_has_successor, fresh_run_fits};
use trust_ir::{CallingConv, ExternRefSite, InstShape};

// --------------------------------------------------------------------------
// coverage_supports — L1: reflexive on positive grades (`Unrecorded`'s
// self-pair is a demand-column law below)
// --------------------------------------------------------------------------

pub fn coverage_reflexive_unbounded() -> bool
    ensures result
{
    coverage_supports(CoverageBound::Unbounded, CoverageBound::Unbounded)
}

pub fn coverage_reflexive_unwind(d: u64) -> bool
    ensures result
{
    coverage_supports(
        CoverageBound::UnwindBounded { depth: d },
        CoverageBound::UnwindBounded { depth: d },
    )
}

pub fn coverage_reflexive_model(s: u64) -> bool
    ensures result
{
    coverage_supports(
        CoverageBound::ModelBounded { size: s },
        CoverageBound::ModelBounded { size: s },
    )
}

// --------------------------------------------------------------------------
// L2: `Unbounded` supplies every demand (per variant — the enum-quantified
// statement leaves the seal marker unknown, crate docs)
// --------------------------------------------------------------------------

pub fn coverage_unbounded_supplies_unbounded() -> bool
    ensures result
{
    coverage_supports(CoverageBound::Unbounded, CoverageBound::Unbounded)
}

pub fn coverage_unbounded_supplies_unwind(n: u64) -> bool
    ensures result
{
    coverage_supports(
        CoverageBound::Unbounded,
        CoverageBound::UnwindBounded { depth: n },
    )
}

pub fn coverage_unbounded_supplies_model(n: u64) -> bool
    ensures result
{
    coverage_supports(
        CoverageBound::Unbounded,
        CoverageBound::ModelBounded { size: n },
    )
}

pub fn coverage_unbounded_supplies_unrecorded() -> bool
    ensures result
{
    coverage_supports(CoverageBound::Unbounded, CoverageBound::Unrecorded)
}

// --------------------------------------------------------------------------
// L3: same axis is magnitude order — the one law whose return is not a
// constant: the solver proves `result == (have >= need)` against the
// inlined arm
// --------------------------------------------------------------------------

pub fn coverage_unwind_is_magnitude_order(have: u64, need: u64) -> bool
    ensures result == (have >= need)
{
    coverage_supports(
        CoverageBound::UnwindBounded { depth: have },
        CoverageBound::UnwindBounded { depth: need },
    )
}

pub fn coverage_model_is_magnitude_order(have: u64, need: u64) -> bool
    ensures result == (have >= need)
{
    coverage_supports(
        CoverageBound::ModelBounded { size: have },
        CoverageBound::ModelBounded { size: need },
    )
}

// --------------------------------------------------------------------------
// L4: the two bounded rungs are INCOMPARABLE at every magnitude
// --------------------------------------------------------------------------

pub fn coverage_unwind_never_supplies_model(d: u64, s: u64) -> bool
    ensures result == false
{
    coverage_supports(
        CoverageBound::UnwindBounded { depth: d },
        CoverageBound::ModelBounded { size: s },
    )
}

pub fn coverage_model_never_supplies_unwind(s: u64, d: u64) -> bool
    ensures result == false
{
    coverage_supports(
        CoverageBound::ModelBounded { size: s },
        CoverageBound::UnwindBounded { depth: d },
    )
}

// --------------------------------------------------------------------------
// L5: no bounded rung supplies `Unbounded` (the residual-ledger case)
// --------------------------------------------------------------------------

pub fn coverage_unwind_never_supplies_unbounded(d: u64) -> bool
    ensures result == false
{
    coverage_supports(
        CoverageBound::UnwindBounded { depth: d },
        CoverageBound::Unbounded,
    )
}

pub fn coverage_model_never_supplies_unbounded(s: u64) -> bool
    ensures result == false
{
    coverage_supports(
        CoverageBound::ModelBounded { size: s },
        CoverageBound::Unbounded,
    )
}

// --------------------------------------------------------------------------
// L6: `Unrecorded` as a SUPPLY supplies no positive grade (`n` ranges over
// all of `u64`, so `UnwindBounded { depth: 0 }` is covered)
// --------------------------------------------------------------------------

pub fn coverage_unrecorded_never_supplies_unbounded() -> bool
    ensures result == false
{
    coverage_supports(CoverageBound::Unrecorded, CoverageBound::Unbounded)
}

pub fn coverage_unrecorded_never_supplies_unwind(n: u64) -> bool
    ensures result == false
{
    coverage_supports(
        CoverageBound::Unrecorded,
        CoverageBound::UnwindBounded { depth: n },
    )
}

pub fn coverage_unrecorded_never_supplies_model(n: u64) -> bool
    ensures result == false
{
    coverage_supports(
        CoverageBound::Unrecorded,
        CoverageBound::ModelBounded { size: n },
    )
}

// --------------------------------------------------------------------------
// L7: `Unrecorded` as a DEMAND is met by anything, including itself
// --------------------------------------------------------------------------

pub fn coverage_unrecorded_demand_met_by_unbounded() -> bool
    ensures result
{
    coverage_supports(CoverageBound::Unbounded, CoverageBound::Unrecorded)
}

pub fn coverage_unrecorded_demand_met_by_unwind(d: u64) -> bool
    ensures result
{
    coverage_supports(
        CoverageBound::UnwindBounded { depth: d },
        CoverageBound::Unrecorded,
    )
}

pub fn coverage_unrecorded_demand_met_by_model(s: u64) -> bool
    ensures result
{
    coverage_supports(
        CoverageBound::ModelBounded { size: s },
        CoverageBound::Unrecorded,
    )
}

pub fn coverage_unrecorded_demand_met_by_unrecorded() -> bool
    ensures result
{
    coverage_supports(CoverageBound::Unrecorded, CoverageBound::Unrecorded)
}

/// The general statement over a by-value enum supply — the one
/// enum-quantified law this build proves as a single row: the table's first
/// arm matches every `far`, so the optimizer folds the whole match to `true`.
pub fn coverage_unrecorded_demand_met_by_any(far: CoverageBound) -> bool
    ensures result
{
    coverage_supports(far, CoverageBound::Unrecorded)
}

// --------------------------------------------------------------------------
// L8: transitivity. NOT a proved row over the table (crate docs); this is
// the integer half it reduces to under L3, and the composition is a hand
// step: `coverage_supports(U{a}, U{b}) == (a >= b)` (L3), so a `>=` chain
// along one axis is `>=` transitivity.
// --------------------------------------------------------------------------

pub fn u64_ge_is_transitive(a: u64, b: u64, c: u64) -> bool
    ensures result
{
    if a < b {
        return true;
    }
    if b < c {
        return true;
    }
    a >= c
}

// --------------------------------------------------------------------------
// license_admits_body — the codegen-license admission table
// --------------------------------------------------------------------------

/// A gated body is never refused by the admission table, under either policy
/// (the evidence and recognition rules decide it next). This law is what
/// makes the `GateShape::Gated` refusal arm in trust-ir-build's
/// `license_errors_against` unreachable.
pub fn license_gated_admitted_under_any_policy(unlicensed: UnlicensedBodyPolicy) -> bool
    ensures result
{
    license_admits_body(GateShape::Gated, unlicensed)
}

/// "An affirmative `Ungated` body is refused under either policy."
pub fn license_ungated_refused_under_any_policy(unlicensed: UnlicensedBodyPolicy) -> bool
    ensures result == false
{
    license_admits_body(GateShape::Ungated, unlicensed)
}

/// The fail-closed default: no licensing claim, `Refuse` policy, refused.
pub fn license_absent_refused_under_refuse() -> bool
    ensures result == false
{
    license_admits_body(GateShape::Absent, UnlicensedBodyPolicy::Refuse)
}

/// The grandfather filter: no licensing claim, `Permit` policy, admitted.
pub fn license_absent_admitted_under_permit() -> bool
    ensures result
{
    license_admits_body(GateShape::Absent, UnlicensedBodyPolicy::Permit)
}

// --------------------------------------------------------------------------
// AllocOrigin::is_reference_counted (trust-ir) — the reference-counted
// cells: where `Retain`/`Release`/`IsUnique` are defined and `Dealloc` is UB
// --------------------------------------------------------------------------

pub fn rc_rust_heap() -> bool
    ensures result == false
{
    AllocOrigin::RustHeap.is_reference_counted()
}

pub fn rc_swift_heap() -> bool
    ensures result
{
    AllocOrigin::SwiftHeap.is_reference_counted()
}

pub fn rc_c_malloc() -> bool
    ensures result == false
{
    AllocOrigin::CMalloc.is_reference_counted()
}

pub fn rc_clean_heap() -> bool
    ensures result
{
    AllocOrigin::CleanHeap.is_reference_counted()
}

// --------------------------------------------------------------------------
// Linkage::is_interposable (trust-ir) — import authentication's
// InterposableFarSite rule (WS8.14, R2/R4)
// --------------------------------------------------------------------------

pub fn interposable_external() -> bool
    ensures result == false
{
    Linkage::External.is_interposable()
}

pub fn interposable_internal() -> bool
    ensures result == false
{
    Linkage::Internal.is_interposable()
}

pub fn interposable_private() -> bool
    ensures result == false
{
    Linkage::Private.is_interposable()
}

pub fn interposable_weak() -> bool
    ensures result
{
    Linkage::Weak.is_interposable()
}

pub fn interposable_link_once() -> bool
    ensures result
{
    Linkage::LinkOnce.is_interposable()
}

pub fn interposable_available_externally() -> bool
    ensures result == false
{
    Linkage::AvailableExternally.is_interposable()
}

pub fn interposable_external_weak() -> bool
    ensures result
{
    Linkage::ExternalWeak.is_interposable()
}

pub fn interposable_weak_odr() -> bool
    ensures result == false
{
    Linkage::WeakOdr.is_interposable()
}

pub fn interposable_link_once_odr() -> bool
    ensures result == false
{
    Linkage::LinkOnceOdr.is_interposable()
}

// --------------------------------------------------------------------------
// Linkage::is_module_local (trust-ir) — not exported, not importable;
// the first conjunct of ContradictoryFunctionVisibility
// --------------------------------------------------------------------------

pub fn module_local_external() -> bool
    ensures result == false
{
    Linkage::External.is_module_local()
}

pub fn module_local_internal() -> bool
    ensures result
{
    Linkage::Internal.is_module_local()
}

pub fn module_local_private() -> bool
    ensures result
{
    Linkage::Private.is_module_local()
}

pub fn module_local_weak() -> bool
    ensures result == false
{
    Linkage::Weak.is_module_local()
}

pub fn module_local_link_once() -> bool
    ensures result == false
{
    Linkage::LinkOnce.is_module_local()
}

pub fn module_local_available_externally() -> bool
    ensures result == false
{
    Linkage::AvailableExternally.is_module_local()
}

pub fn module_local_external_weak() -> bool
    ensures result == false
{
    Linkage::ExternalWeak.is_module_local()
}

pub fn module_local_weak_odr() -> bool
    ensures result == false
{
    Linkage::WeakOdr.is_module_local()
}

pub fn module_local_link_once_odr() -> bool
    ensures result == false
{
    Linkage::LinkOnceOdr.is_module_local()
}

// --------------------------------------------------------------------------
// Linkage::requires_contract_surface (trust-ir) — the writer's v41
// selection for a linkage
// --------------------------------------------------------------------------

pub fn contract_surface_linkage_external() -> bool
    ensures result == false
{
    Linkage::External.requires_contract_surface()
}

pub fn contract_surface_linkage_internal() -> bool
    ensures result == false
{
    Linkage::Internal.requires_contract_surface()
}

pub fn contract_surface_linkage_private() -> bool
    ensures result == false
{
    Linkage::Private.requires_contract_surface()
}

pub fn contract_surface_linkage_weak() -> bool
    ensures result == false
{
    Linkage::Weak.requires_contract_surface()
}

pub fn contract_surface_linkage_link_once() -> bool
    ensures result == false
{
    Linkage::LinkOnce.requires_contract_surface()
}

pub fn contract_surface_linkage_available_externally() -> bool
    ensures result
{
    Linkage::AvailableExternally.requires_contract_surface()
}

pub fn contract_surface_linkage_external_weak() -> bool
    ensures result
{
    Linkage::ExternalWeak.requires_contract_surface()
}

pub fn contract_surface_linkage_weak_odr() -> bool
    ensures result
{
    Linkage::WeakOdr.requires_contract_surface()
}

pub fn contract_surface_linkage_link_once_odr() -> bool
    ensures result
{
    Linkage::LinkOnceOdr.requires_contract_surface()
}

// --------------------------------------------------------------------------
// ProofStatus::is_discharged_tier (trust-ir) — Discharged | Certified
// --------------------------------------------------------------------------

pub fn discharged_tier_pending() -> bool
    ensures result == false
{
    ProofStatus::Pending.is_discharged_tier()
}

pub fn discharged_tier_discharged() -> bool
    ensures result
{
    ProofStatus::Discharged.is_discharged_tier()
}

pub fn discharged_tier_failed() -> bool
    ensures result == false
{
    ProofStatus::Failed.is_discharged_tier()
}

pub fn discharged_tier_trusted() -> bool
    ensures result == false
{
    ProofStatus::Trusted.is_discharged_tier()
}

pub fn discharged_tier_certified() -> bool
    ensures result
{
    ProofStatus::Certified.is_discharged_tier()
}

// --------------------------------------------------------------------------
// ProofStatus::is_kernel_tier (trust-ir) — Certified alone
// --------------------------------------------------------------------------

pub fn kernel_tier_pending() -> bool
    ensures result == false
{
    ProofStatus::Pending.is_kernel_tier()
}

pub fn kernel_tier_discharged() -> bool
    ensures result == false
{
    ProofStatus::Discharged.is_kernel_tier()
}

pub fn kernel_tier_failed() -> bool
    ensures result == false
{
    ProofStatus::Failed.is_kernel_tier()
}

pub fn kernel_tier_trusted() -> bool
    ensures result == false
{
    ProofStatus::Trusted.is_kernel_tier()
}

pub fn kernel_tier_certified() -> bool
    ensures result
{
    ProofStatus::Certified.is_kernel_tier()
}

// --------------------------------------------------------------------------
// Ordering::is_legal_for_load (trust-ir) — IllegalAtomicOrdering; Lean
// isValidLoadOrdering
// --------------------------------------------------------------------------

pub fn atomic_load_relaxed() -> bool
    ensures result
{
    Ordering::Relaxed.is_legal_for_load()
}

pub fn atomic_load_acquire() -> bool
    ensures result
{
    Ordering::Acquire.is_legal_for_load()
}

pub fn atomic_load_release() -> bool
    ensures result == false
{
    Ordering::Release.is_legal_for_load()
}

pub fn atomic_load_acq_rel() -> bool
    ensures result == false
{
    Ordering::AcqRel.is_legal_for_load()
}

pub fn atomic_load_seq_cst() -> bool
    ensures result
{
    Ordering::SeqCst.is_legal_for_load()
}

// --------------------------------------------------------------------------
// Ordering::is_legal_for_store (trust-ir) — Lean isValidStoreOrdering
// --------------------------------------------------------------------------

pub fn atomic_store_relaxed() -> bool
    ensures result
{
    Ordering::Relaxed.is_legal_for_store()
}

pub fn atomic_store_acquire() -> bool
    ensures result == false
{
    Ordering::Acquire.is_legal_for_store()
}

pub fn atomic_store_release() -> bool
    ensures result
{
    Ordering::Release.is_legal_for_store()
}

pub fn atomic_store_acq_rel() -> bool
    ensures result == false
{
    Ordering::AcqRel.is_legal_for_store()
}

pub fn atomic_store_seq_cst() -> bool
    ensures result
{
    Ordering::SeqCst.is_legal_for_store()
}

// --------------------------------------------------------------------------
// CallingConv::is_abi_surface (trust-ir) — the writer's v45 selection
// --------------------------------------------------------------------------

pub fn cc_abi_surface_c() -> bool
    ensures result == false
{
    CallingConv::C.is_abi_surface()
}

pub fn cc_abi_surface_fast() -> bool
    ensures result == false
{
    CallingConv::Fast.is_abi_surface()
}

pub fn cc_abi_surface_cold() -> bool
    ensures result == false
{
    CallingConv::Cold.is_abi_surface()
}

pub fn cc_abi_surface_rust() -> bool
    ensures result == false
{
    CallingConv::Rust.is_abi_surface()
}

pub fn cc_abi_surface_swift() -> bool
    ensures result == false
{
    CallingConv::Swift.is_abi_surface()
}

pub fn cc_abi_surface_c_unwind() -> bool
    ensures result
{
    CallingConv::CUnwind.is_abi_surface()
}

pub fn cc_abi_surface_sys_v64() -> bool
    ensures result
{
    CallingConv::SysV64.is_abi_surface()
}

pub fn cc_abi_surface_win64() -> bool
    ensures result
{
    CallingConv::Win64.is_abi_surface()
}

pub fn cc_abi_surface_aapcs() -> bool
    ensures result
{
    CallingConv::Aapcs.is_abi_surface()
}

pub fn cc_abi_surface_efi_api() -> bool
    ensures result
{
    CallingConv::EfiApi.is_abi_surface()
}

pub fn cc_abi_surface_vector_call() -> bool
    ensures result
{
    CallingConv::VectorCall.is_abi_surface()
}

pub fn cc_abi_surface_rust_cold() -> bool
    ensures result
{
    CallingConv::RustCold.is_abi_surface()
}

// --------------------------------------------------------------------------
// EnumTagRepr::is_abi_surface (trust-ir) — the writer's v45 selection
// --------------------------------------------------------------------------

pub fn tag_abi_surface_u8() -> bool
    ensures result == false
{
    EnumTagRepr::U8.is_abi_surface()
}

pub fn tag_abi_surface_u16() -> bool
    ensures result == false
{
    EnumTagRepr::U16.is_abi_surface()
}

pub fn tag_abi_surface_u32() -> bool
    ensures result == false
{
    EnumTagRepr::U32.is_abi_surface()
}

pub fn tag_abi_surface_u64() -> bool
    ensures result == false
{
    EnumTagRepr::U64.is_abi_surface()
}

pub fn tag_abi_surface_i8() -> bool
    ensures result == false
{
    EnumTagRepr::I8.is_abi_surface()
}

pub fn tag_abi_surface_i16() -> bool
    ensures result == false
{
    EnumTagRepr::I16.is_abi_surface()
}

pub fn tag_abi_surface_i32() -> bool
    ensures result == false
{
    EnumTagRepr::I32.is_abi_surface()
}

pub fn tag_abi_surface_i64() -> bool
    ensures result == false
{
    EnumTagRepr::I64.is_abi_surface()
}

pub fn tag_abi_surface_u128() -> bool
    ensures result
{
    EnumTagRepr::U128.is_abi_surface()
}

pub fn tag_abi_surface_i128() -> bool
    ensures result
{
    EnumTagRepr::I128.is_abi_surface()
}

// --------------------------------------------------------------------------
// HardwareVectorContractStatus::fail_closed (trust-ir) — the x86-64
// consumer MUST refuse every non-Available vector-compare cell
// --------------------------------------------------------------------------

pub fn hv_fail_closed_available() -> bool
    ensures result == false
{
    HardwareVectorContractStatus::Available.fail_closed()
}

pub fn hv_fail_closed_deferred() -> bool
    ensures result
{
    HardwareVectorContractStatus::Deferred.fail_closed()
}

pub fn hv_fail_closed_unavailable() -> bool
    ensures result
{
    HardwareVectorContractStatus::Unavailable.fail_closed()
}

// --------------------------------------------------------------------------
// ExternRefSite::admits_shape (trust-ir) — import authentication R7:
// `backed_by` cites contract kinds only
// --------------------------------------------------------------------------

pub fn backed_by_precondition() -> bool
    ensures result
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::Precondition)
}

pub fn backed_by_postcondition() -> bool
    ensures result
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::Postcondition)
}

pub fn backed_by_loop_invariant() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::LoopInvariant)
}

pub fn backed_by_type_invariant() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::TypeInvariant)
}

pub fn backed_by_refinement_type() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::RefinementType)
}

pub fn backed_by_translation_validation() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::TranslationValidation)
}

pub fn backed_by_memory_safety() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::MemorySafety)
}

pub fn backed_by_panic_freedom() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::PanicFreedom)
}

pub fn backed_by_temporal_safety() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::TemporalSafety)
}

pub fn backed_by_liveness() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::Liveness)
}

pub fn backed_by_arithmetic_safety() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::ArithmeticSafety)
}

pub fn backed_by_bounds_check() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::BoundsCheck)
}

pub fn backed_by_give_back_refinement() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::GiveBackRefinement)
}

pub fn backed_by_termination() -> bool
    ensures result
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::Termination)
}

pub fn backed_by_ownership() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::Ownership)
}

pub fn backed_by_custom() -> bool
    ensures result == false
{
    ExternRefSite::SummaryBackedBy.admits_shape(ObligationKindShape::Custom)
}

// --------------------------------------------------------------------------
// ExternRefSite::admits_shape — inheritance admits every kind but `Custom`
// --------------------------------------------------------------------------

pub fn inherited_precondition() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::Precondition)
}

pub fn inherited_postcondition() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::Postcondition)
}

pub fn inherited_loop_invariant() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::LoopInvariant)
}

pub fn inherited_type_invariant() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::TypeInvariant)
}

pub fn inherited_refinement_type() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::RefinementType)
}

pub fn inherited_translation_validation() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::TranslationValidation)
}

pub fn inherited_memory_safety() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::MemorySafety)
}

pub fn inherited_panic_freedom() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::PanicFreedom)
}

pub fn inherited_temporal_safety() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::TemporalSafety)
}

pub fn inherited_liveness() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::Liveness)
}

pub fn inherited_arithmetic_safety() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::ArithmeticSafety)
}

pub fn inherited_bounds_check() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::BoundsCheck)
}

pub fn inherited_give_back_refinement() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::GiveBackRefinement)
}

pub fn inherited_termination() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::Termination)
}

pub fn inherited_ownership() -> bool
    ensures result
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::Ownership)
}

pub fn inherited_custom() -> bool
    ensures result == false
{
    ExternRefSite::InheritedFromCallee.admits_shape(ObligationKindShape::Custom)
}

// --------------------------------------------------------------------------
// ExternRefSite::admits_shape — the claim-free sites admit nothing (one
// law each, over every kind shape)
// --------------------------------------------------------------------------

pub fn call_edge_admits_nothing(kind: ObligationKindShape) -> bool
    ensures result == false
{
    ExternRefSite::CallEdge.admits_shape(kind)
}

pub fn handle_declaration_admits_nothing(kind: ObligationKindShape) -> bool
    ensures result == false
{
    ExternRefSite::HandleDeclaration.admits_shape(kind)
}

// --------------------------------------------------------------------------
// ObligationKindShape::is_grounded_contract_kind (trust-ir) — the L1
// contract kinds the Clean-expr grounder grounds; Termination/Ownership out by
// decision (WS1.9 DECIDE A)
// --------------------------------------------------------------------------

pub fn grounded_contract_kind_precondition() -> bool
    ensures result
{
    ObligationKindShape::Precondition.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_postcondition() -> bool
    ensures result
{
    ObligationKindShape::Postcondition.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_loop_invariant() -> bool
    ensures result
{
    ObligationKindShape::LoopInvariant.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_type_invariant() -> bool
    ensures result == false
{
    ObligationKindShape::TypeInvariant.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_refinement_type() -> bool
    ensures result
{
    ObligationKindShape::RefinementType.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_translation_validation() -> bool
    ensures result == false
{
    ObligationKindShape::TranslationValidation.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_memory_safety() -> bool
    ensures result == false
{
    ObligationKindShape::MemorySafety.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_panic_freedom() -> bool
    ensures result == false
{
    ObligationKindShape::PanicFreedom.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_temporal_safety() -> bool
    ensures result == false
{
    ObligationKindShape::TemporalSafety.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_liveness() -> bool
    ensures result == false
{
    ObligationKindShape::Liveness.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_arithmetic_safety() -> bool
    ensures result == false
{
    ObligationKindShape::ArithmeticSafety.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_bounds_check() -> bool
    ensures result == false
{
    ObligationKindShape::BoundsCheck.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_give_back_refinement() -> bool
    ensures result == false
{
    ObligationKindShape::GiveBackRefinement.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_termination() -> bool
    ensures result == false
{
    ObligationKindShape::Termination.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_ownership() -> bool
    ensures result == false
{
    ObligationKindShape::Ownership.is_grounded_contract_kind()
}

pub fn grounded_contract_kind_custom() -> bool
    ensures result == false
{
    ObligationKindShape::Custom.is_grounded_contract_kind()
}

// --------------------------------------------------------------------------
// ObligationKindShape::free_var_is_proved (trust-ir) — PROVED (Postcondition,
// RefinementType) vs ASSUMED; getting it backwards stamps an unproven
// postcondition Certified
// --------------------------------------------------------------------------

pub fn free_var_proved_precondition() -> bool
    ensures result == false
{
    ObligationKindShape::Precondition.free_var_is_proved()
}

pub fn free_var_proved_postcondition() -> bool
    ensures result
{
    ObligationKindShape::Postcondition.free_var_is_proved()
}

pub fn free_var_proved_loop_invariant() -> bool
    ensures result == false
{
    ObligationKindShape::LoopInvariant.free_var_is_proved()
}

pub fn free_var_proved_type_invariant() -> bool
    ensures result == false
{
    ObligationKindShape::TypeInvariant.free_var_is_proved()
}

pub fn free_var_proved_refinement_type() -> bool
    ensures result
{
    ObligationKindShape::RefinementType.free_var_is_proved()
}

pub fn free_var_proved_translation_validation() -> bool
    ensures result == false
{
    ObligationKindShape::TranslationValidation.free_var_is_proved()
}

pub fn free_var_proved_memory_safety() -> bool
    ensures result == false
{
    ObligationKindShape::MemorySafety.free_var_is_proved()
}

pub fn free_var_proved_panic_freedom() -> bool
    ensures result == false
{
    ObligationKindShape::PanicFreedom.free_var_is_proved()
}

pub fn free_var_proved_temporal_safety() -> bool
    ensures result == false
{
    ObligationKindShape::TemporalSafety.free_var_is_proved()
}

pub fn free_var_proved_liveness() -> bool
    ensures result == false
{
    ObligationKindShape::Liveness.free_var_is_proved()
}

pub fn free_var_proved_arithmetic_safety() -> bool
    ensures result == false
{
    ObligationKindShape::ArithmeticSafety.free_var_is_proved()
}

pub fn free_var_proved_bounds_check() -> bool
    ensures result == false
{
    ObligationKindShape::BoundsCheck.free_var_is_proved()
}

pub fn free_var_proved_give_back_refinement() -> bool
    ensures result == false
{
    ObligationKindShape::GiveBackRefinement.free_var_is_proved()
}

pub fn free_var_proved_termination() -> bool
    ensures result == false
{
    ObligationKindShape::Termination.free_var_is_proved()
}

pub fn free_var_proved_ownership() -> bool
    ensures result == false
{
    ObligationKindShape::Ownership.free_var_is_proved()
}

pub fn free_var_proved_custom() -> bool
    ensures result == false
{
    ObligationKindShape::Custom.free_var_is_proved()
}

// --------------------------------------------------------------------------
// ObligationKindShape::is_assert_class (trust-ir) — the only kinds a sited
// assert condition may discharge
// --------------------------------------------------------------------------

pub fn assert_class_precondition() -> bool
    ensures result == false
{
    ObligationKindShape::Precondition.is_assert_class()
}

pub fn assert_class_postcondition() -> bool
    ensures result == false
{
    ObligationKindShape::Postcondition.is_assert_class()
}

pub fn assert_class_loop_invariant() -> bool
    ensures result == false
{
    ObligationKindShape::LoopInvariant.is_assert_class()
}

pub fn assert_class_type_invariant() -> bool
    ensures result == false
{
    ObligationKindShape::TypeInvariant.is_assert_class()
}

pub fn assert_class_refinement_type() -> bool
    ensures result == false
{
    ObligationKindShape::RefinementType.is_assert_class()
}

pub fn assert_class_translation_validation() -> bool
    ensures result == false
{
    ObligationKindShape::TranslationValidation.is_assert_class()
}

pub fn assert_class_memory_safety() -> bool
    ensures result == false
{
    ObligationKindShape::MemorySafety.is_assert_class()
}

pub fn assert_class_panic_freedom() -> bool
    ensures result == false
{
    ObligationKindShape::PanicFreedom.is_assert_class()
}

pub fn assert_class_temporal_safety() -> bool
    ensures result == false
{
    ObligationKindShape::TemporalSafety.is_assert_class()
}

pub fn assert_class_liveness() -> bool
    ensures result == false
{
    ObligationKindShape::Liveness.is_assert_class()
}

pub fn assert_class_arithmetic_safety() -> bool
    ensures result
{
    ObligationKindShape::ArithmeticSafety.is_assert_class()
}

pub fn assert_class_bounds_check() -> bool
    ensures result
{
    ObligationKindShape::BoundsCheck.is_assert_class()
}

pub fn assert_class_give_back_refinement() -> bool
    ensures result == false
{
    ObligationKindShape::GiveBackRefinement.is_assert_class()
}

pub fn assert_class_termination() -> bool
    ensures result == false
{
    ObligationKindShape::Termination.is_assert_class()
}

pub fn assert_class_ownership() -> bool
    ensures result == false
{
    ObligationKindShape::Ownership.is_assert_class()
}

pub fn assert_class_custom() -> bool
    ensures result == false
{
    ObligationKindShape::Custom.is_assert_class()
}

// --------------------------------------------------------------------------
// InstShape::is_terminator (trust-ir) — the block structure; Inst::is_terminator
// delegates to it
// --------------------------------------------------------------------------

pub fn terminator_bin_op() -> bool
    ensures result == false
{
    InstShape::BinOp.is_terminator()
}

pub fn terminator_un_op() -> bool
    ensures result == false
{
    InstShape::UnOp.is_terminator()
}

pub fn terminator_overflow() -> bool
    ensures result == false
{
    InstShape::Overflow.is_terminator()
}

pub fn terminator_i_cmp() -> bool
    ensures result == false
{
    InstShape::ICmp.is_terminator()
}

pub fn terminator_f_cmp() -> bool
    ensures result == false
{
    InstShape::FCmp.is_terminator()
}

pub fn terminator_cast() -> bool
    ensures result == false
{
    InstShape::Cast.is_terminator()
}

pub fn terminator_load() -> bool
    ensures result == false
{
    InstShape::Load.is_terminator()
}

pub fn terminator_store() -> bool
    ensures result == false
{
    InstShape::Store.is_terminator()
}

pub fn terminator_alloca() -> bool
    ensures result == false
{
    InstShape::Alloca.is_terminator()
}

pub fn terminator_drop() -> bool
    ensures result == false
{
    InstShape::Drop.is_terminator()
}

pub fn terminator_heap_alloc() -> bool
    ensures result == false
{
    InstShape::HeapAlloc.is_terminator()
}

pub fn terminator_gep() -> bool
    ensures result == false
{
    InstShape::GEP.is_terminator()
}

pub fn terminator_ptr_data() -> bool
    ensures result == false
{
    InstShape::PtrData.is_terminator()
}

pub fn terminator_ptr_metadata() -> bool
    ensures result == false
{
    InstShape::PtrMetadata.is_terminator()
}

pub fn terminator_ptr_from_parts() -> bool
    ensures result == false
{
    InstShape::PtrFromParts.is_terminator()
}

pub fn terminator_atomic_load() -> bool
    ensures result == false
{
    InstShape::AtomicLoad.is_terminator()
}

pub fn terminator_atomic_store() -> bool
    ensures result == false
{
    InstShape::AtomicStore.is_terminator()
}

pub fn terminator_atomic_rmw() -> bool
    ensures result == false
{
    InstShape::AtomicRMW.is_terminator()
}

pub fn terminator_cmp_xchg() -> bool
    ensures result == false
{
    InstShape::CmpXchg.is_terminator()
}

pub fn terminator_fence() -> bool
    ensures result == false
{
    InstShape::Fence.is_terminator()
}

pub fn terminator_br() -> bool
    ensures result
{
    InstShape::Br.is_terminator()
}

pub fn terminator_cond_br() -> bool
    ensures result
{
    InstShape::CondBr.is_terminator()
}

pub fn terminator_switch() -> bool
    ensures result
{
    InstShape::Switch.is_terminator()
}

pub fn terminator_call() -> bool
    ensures result == false
{
    InstShape::Call.is_terminator()
}

pub fn terminator_call_indirect() -> bool
    ensures result == false
{
    InstShape::CallIndirect.is_terminator()
}

pub fn terminator_call_cannot_unwind() -> bool
    ensures result == false
{
    InstShape::CallCannotUnwind.is_terminator()
}

pub fn terminator_call_indirect_cannot_unwind() -> bool
    ensures result == false
{
    InstShape::CallIndirectCannotUnwind.is_terminator()
}

pub fn terminator_return() -> bool
    ensures result
{
    InstShape::Return.is_terminator()
}

pub fn terminator_extract_field() -> bool
    ensures result == false
{
    InstShape::ExtractField.is_terminator()
}

pub fn terminator_insert_field() -> bool
    ensures result == false
{
    InstShape::InsertField.is_terminator()
}

pub fn terminator_extract_element() -> bool
    ensures result == false
{
    InstShape::ExtractElement.is_terminator()
}

pub fn terminator_insert_element() -> bool
    ensures result == false
{
    InstShape::InsertElement.is_terminator()
}

pub fn terminator_const() -> bool
    ensures result == false
{
    InstShape::Const.is_terminator()
}

pub fn terminator_null_ptr() -> bool
    ensures result == false
{
    InstShape::NullPtr.is_terminator()
}

pub fn terminator_global_addr() -> bool
    ensures result == false
{
    InstShape::GlobalAddr.is_terminator()
}

pub fn terminator_undef() -> bool
    ensures result == false
{
    InstShape::Undef.is_terminator()
}

pub fn terminator_assume() -> bool
    ensures result == false
{
    InstShape::Assume.is_terminator()
}

pub fn terminator_assert() -> bool
    ensures result == false
{
    InstShape::Assert.is_terminator()
}

pub fn terminator_unreachable() -> bool
    ensures result
{
    InstShape::Unreachable.is_terminator()
}

pub fn terminator_copy() -> bool
    ensures result == false
{
    InstShape::Copy.is_terminator()
}

pub fn terminator_select() -> bool
    ensures result == false
{
    InstShape::Select.is_terminator()
}

pub fn terminator_seq_map_add_k() -> bool
    ensures result == false
{
    InstShape::SeqMapAddK.is_terminator()
}

pub fn terminator_seq_map_not() -> bool
    ensures result == false
{
    InstShape::SeqMapNot.is_terminator()
}

pub fn terminator_seq_map() -> bool
    ensures result == false
{
    InstShape::SeqMap.is_terminator()
}

pub fn terminator_borrow() -> bool
    ensures result == false
{
    InstShape::Borrow.is_terminator()
}

pub fn terminator_borrow_mut() -> bool
    ensures result == false
{
    InstShape::BorrowMut.is_terminator()
}

pub fn terminator_end_borrow() -> bool
    ensures result == false
{
    InstShape::EndBorrow.is_terminator()
}

pub fn terminator_retain() -> bool
    ensures result == false
{
    InstShape::Retain.is_terminator()
}

pub fn terminator_release() -> bool
    ensures result == false
{
    InstShape::Release.is_terminator()
}

pub fn terminator_is_unique() -> bool
    ensures result == false
{
    InstShape::IsUnique.is_terminator()
}

pub fn terminator_dealloc() -> bool
    ensures result == false
{
    InstShape::Dealloc.is_terminator()
}

pub fn terminator_mem_copy() -> bool
    ensures result == false
{
    InstShape::MemCopy.is_terminator()
}

pub fn terminator_mem_set() -> bool
    ensures result == false
{
    InstShape::MemSet.is_terminator()
}

pub fn terminator_open_frame() -> bool
    ensures result == false
{
    InstShape::OpenFrame.is_terminator()
}

pub fn terminator_bind_slot() -> bool
    ensures result == false
{
    InstShape::BindSlot.is_terminator()
}

pub fn terminator_load_slot() -> bool
    ensures result == false
{
    InstShape::LoadSlot.is_terminator()
}

pub fn terminator_close_frame() -> bool
    ensures result == false
{
    InstShape::CloseFrame.is_terminator()
}

pub fn terminator_coro_suspend() -> bool
    ensures result
{
    InstShape::CoroSuspend.is_terminator()
}

pub fn terminator_invoke() -> bool
    ensures result
{
    InstShape::Invoke.is_terminator()
}

pub fn terminator_landing_pad() -> bool
    ensures result == false
{
    InstShape::LandingPad.is_terminator()
}

pub fn terminator_resume() -> bool
    ensures result
{
    InstShape::Resume.is_terminator()
}

pub fn terminator_assert_invoke() -> bool
    ensures result
{
    InstShape::AssertInvoke.is_terminator()
}

pub fn terminator_drop_invoke() -> bool
    ensures result
{
    InstShape::DropInvoke.is_terminator()
}

pub fn terminator_invoke_indirect() -> bool
    ensures result
{
    InstShape::InvokeIndirect.is_terminator()
}

pub fn terminator_dialect_op() -> bool
    ensures result == false
{
    InstShape::DialectOp.is_terminator()
}

pub fn terminator_make_aggregate() -> bool
    ensures result == false
{
    InstShape::MakeAggregate.is_terminator()
}

pub fn terminator_array_splat() -> bool
    ensures result == false
{
    InstShape::ArraySplat.is_terminator()
}

pub fn terminator_make_closure() -> bool
    ensures result == false
{
    InstShape::MakeClosure.is_terminator()
}

pub fn terminator_tensor_contract() -> bool
    ensures result == false
{
    InstShape::TensorContract.is_terminator()
}

pub fn terminator_tensor_map() -> bool
    ensures result == false
{
    InstShape::TensorMap.is_terminator()
}

pub fn terminator_tensor_reduce() -> bool
    ensures result == false
{
    InstShape::TensorReduce.is_terminator()
}

pub fn terminator_tensor_view() -> bool
    ensures result == false
{
    InstShape::TensorView.is_terminator()
}

pub fn terminator_tensor_gather() -> bool
    ensures result == false
{
    InstShape::TensorGather.is_terminator()
}

pub fn terminator_tensor_scatter() -> bool
    ensures result == false
{
    InstShape::TensorScatter.is_terminator()
}

// --------------------------------------------------------------------------
// fresh_id_has_successor (trust-ir, value.rs) — the fresh-id rule's
// exhaustion row (r11 R1): an id has a successor exactly below u32::MAX, so
// u32::MAX, and only it, leaves a cursor exhausted — refused, never wrapped
// --------------------------------------------------------------------------

pub fn fresh_successor_iff_below_max(id: u32) -> bool
    ensures result == (id < 4294967295)
{
    fresh_id_has_successor(id)
}

pub fn fresh_successor_absent_at_max() -> bool
    ensures result == false
{
    fresh_id_has_successor(4294967295)
}

pub fn fresh_successor_present_below_max() -> bool
    ensures result
{
    fresh_id_has_successor(4294967294)
}

pub fn fresh_successor_present_at_zero() -> bool
    ensures result
{
    fresh_id_has_successor(0)
}

// --------------------------------------------------------------------------
// fresh_run_fits (trust-ir, value.rs) — the all-or-nothing run: a run ending
// `extra` ids past its first fits exactly when `extra` is at most the room
// above that first id
// --------------------------------------------------------------------------

pub fn fresh_run_fits_iff_within_room(extra: u32, room: u32) -> bool
    ensures result == (extra <= room)
{
    fresh_run_fits(extra, room)
}

pub fn fresh_run_fits_single_id_anywhere(room: u32) -> bool
    ensures result
{
    fresh_run_fits(0, room)
}

pub fn fresh_run_fits_whole_space() -> bool
    ensures result
{
    fresh_run_fits(4294967295, 4294967295)
}

pub fn fresh_run_fits_refused_past_max() -> bool
    ensures result == false
{
    fresh_run_fits(1, 0)
}

// --------------------------------------------------------------------------
// fresh_id_below (trust-ir, value.rs) — a bounded run's last id is strictly
// below the bound (0xE000_0000 is the start of the CLI's reserved block
// range), and the order `after` and `span` read
// --------------------------------------------------------------------------

pub fn fresh_below_iff_less(id: u32, end_exclusive: u32) -> bool
    ensures result == (id < end_exclusive)
{
    fresh_id_below(id, end_exclusive)
}

pub fn fresh_below_refuses_the_bound() -> bool
    ensures result == false
{
    fresh_id_below(3758096384, 3758096384)
}

pub fn fresh_below_admits_the_last_id_under_the_bound() -> bool
    ensures result
{
    fresh_id_below(3758096383, 3758096384)
}

// --------------------------------------------------------------------------
// InstShape::uses_borrow_permissions (trust-ir) — the permission machine's
// instructions; the Rust-reference rule's validator and bundle checks read it
// --------------------------------------------------------------------------

pub fn borrow_permission_bin_op() -> bool
    ensures result == false
{
    InstShape::BinOp.uses_borrow_permissions()
}

pub fn borrow_permission_un_op() -> bool
    ensures result == false
{
    InstShape::UnOp.uses_borrow_permissions()
}

pub fn borrow_permission_overflow() -> bool
    ensures result == false
{
    InstShape::Overflow.uses_borrow_permissions()
}

pub fn borrow_permission_i_cmp() -> bool
    ensures result == false
{
    InstShape::ICmp.uses_borrow_permissions()
}

pub fn borrow_permission_f_cmp() -> bool
    ensures result == false
{
    InstShape::FCmp.uses_borrow_permissions()
}

pub fn borrow_permission_cast() -> bool
    ensures result == false
{
    InstShape::Cast.uses_borrow_permissions()
}

pub fn borrow_permission_load() -> bool
    ensures result == false
{
    InstShape::Load.uses_borrow_permissions()
}

pub fn borrow_permission_store() -> bool
    ensures result == false
{
    InstShape::Store.uses_borrow_permissions()
}

pub fn borrow_permission_alloca() -> bool
    ensures result == false
{
    InstShape::Alloca.uses_borrow_permissions()
}

pub fn borrow_permission_drop() -> bool
    ensures result == false
{
    InstShape::Drop.uses_borrow_permissions()
}

pub fn borrow_permission_heap_alloc() -> bool
    ensures result == false
{
    InstShape::HeapAlloc.uses_borrow_permissions()
}

pub fn borrow_permission_gep() -> bool
    ensures result == false
{
    InstShape::GEP.uses_borrow_permissions()
}

pub fn borrow_permission_ptr_data() -> bool
    ensures result == false
{
    InstShape::PtrData.uses_borrow_permissions()
}

pub fn borrow_permission_ptr_metadata() -> bool
    ensures result == false
{
    InstShape::PtrMetadata.uses_borrow_permissions()
}

pub fn borrow_permission_ptr_from_parts() -> bool
    ensures result == false
{
    InstShape::PtrFromParts.uses_borrow_permissions()
}

pub fn borrow_permission_atomic_load() -> bool
    ensures result == false
{
    InstShape::AtomicLoad.uses_borrow_permissions()
}

pub fn borrow_permission_atomic_store() -> bool
    ensures result == false
{
    InstShape::AtomicStore.uses_borrow_permissions()
}

pub fn borrow_permission_atomic_rmw() -> bool
    ensures result == false
{
    InstShape::AtomicRMW.uses_borrow_permissions()
}

pub fn borrow_permission_cmp_xchg() -> bool
    ensures result == false
{
    InstShape::CmpXchg.uses_borrow_permissions()
}

pub fn borrow_permission_fence() -> bool
    ensures result == false
{
    InstShape::Fence.uses_borrow_permissions()
}

pub fn borrow_permission_br() -> bool
    ensures result == false
{
    InstShape::Br.uses_borrow_permissions()
}

pub fn borrow_permission_cond_br() -> bool
    ensures result == false
{
    InstShape::CondBr.uses_borrow_permissions()
}

pub fn borrow_permission_switch() -> bool
    ensures result == false
{
    InstShape::Switch.uses_borrow_permissions()
}

pub fn borrow_permission_call() -> bool
    ensures result == false
{
    InstShape::Call.uses_borrow_permissions()
}

pub fn borrow_permission_call_indirect() -> bool
    ensures result == false
{
    InstShape::CallIndirect.uses_borrow_permissions()
}

pub fn borrow_permission_call_cannot_unwind() -> bool
    ensures result == false
{
    InstShape::CallCannotUnwind.uses_borrow_permissions()
}

pub fn borrow_permission_call_indirect_cannot_unwind() -> bool
    ensures result == false
{
    InstShape::CallIndirectCannotUnwind.uses_borrow_permissions()
}

pub fn borrow_permission_return() -> bool
    ensures result == false
{
    InstShape::Return.uses_borrow_permissions()
}

pub fn borrow_permission_extract_field() -> bool
    ensures result == false
{
    InstShape::ExtractField.uses_borrow_permissions()
}

pub fn borrow_permission_insert_field() -> bool
    ensures result == false
{
    InstShape::InsertField.uses_borrow_permissions()
}

pub fn borrow_permission_extract_element() -> bool
    ensures result == false
{
    InstShape::ExtractElement.uses_borrow_permissions()
}

pub fn borrow_permission_insert_element() -> bool
    ensures result == false
{
    InstShape::InsertElement.uses_borrow_permissions()
}

pub fn borrow_permission_const() -> bool
    ensures result == false
{
    InstShape::Const.uses_borrow_permissions()
}

pub fn borrow_permission_null_ptr() -> bool
    ensures result == false
{
    InstShape::NullPtr.uses_borrow_permissions()
}

pub fn borrow_permission_global_addr() -> bool
    ensures result == false
{
    InstShape::GlobalAddr.uses_borrow_permissions()
}

pub fn borrow_permission_undef() -> bool
    ensures result == false
{
    InstShape::Undef.uses_borrow_permissions()
}

pub fn borrow_permission_assume() -> bool
    ensures result == false
{
    InstShape::Assume.uses_borrow_permissions()
}

pub fn borrow_permission_assert() -> bool
    ensures result == false
{
    InstShape::Assert.uses_borrow_permissions()
}

pub fn borrow_permission_unreachable() -> bool
    ensures result == false
{
    InstShape::Unreachable.uses_borrow_permissions()
}

pub fn borrow_permission_copy() -> bool
    ensures result == false
{
    InstShape::Copy.uses_borrow_permissions()
}

pub fn borrow_permission_select() -> bool
    ensures result == false
{
    InstShape::Select.uses_borrow_permissions()
}

pub fn borrow_permission_seq_map_add_k() -> bool
    ensures result == false
{
    InstShape::SeqMapAddK.uses_borrow_permissions()
}

pub fn borrow_permission_seq_map_not() -> bool
    ensures result == false
{
    InstShape::SeqMapNot.uses_borrow_permissions()
}

pub fn borrow_permission_seq_map() -> bool
    ensures result == false
{
    InstShape::SeqMap.uses_borrow_permissions()
}

pub fn borrow_permission_borrow() -> bool
    ensures result
{
    InstShape::Borrow.uses_borrow_permissions()
}

pub fn borrow_permission_borrow_mut() -> bool
    ensures result
{
    InstShape::BorrowMut.uses_borrow_permissions()
}

pub fn borrow_permission_end_borrow() -> bool
    ensures result
{
    InstShape::EndBorrow.uses_borrow_permissions()
}

pub fn borrow_permission_retain() -> bool
    ensures result == false
{
    InstShape::Retain.uses_borrow_permissions()
}

pub fn borrow_permission_release() -> bool
    ensures result == false
{
    InstShape::Release.uses_borrow_permissions()
}

pub fn borrow_permission_is_unique() -> bool
    ensures result == false
{
    InstShape::IsUnique.uses_borrow_permissions()
}

pub fn borrow_permission_dealloc() -> bool
    ensures result == false
{
    InstShape::Dealloc.uses_borrow_permissions()
}

pub fn borrow_permission_mem_copy() -> bool
    ensures result == false
{
    InstShape::MemCopy.uses_borrow_permissions()
}

pub fn borrow_permission_mem_set() -> bool
    ensures result == false
{
    InstShape::MemSet.uses_borrow_permissions()
}

pub fn borrow_permission_open_frame() -> bool
    ensures result == false
{
    InstShape::OpenFrame.uses_borrow_permissions()
}

pub fn borrow_permission_bind_slot() -> bool
    ensures result == false
{
    InstShape::BindSlot.uses_borrow_permissions()
}

pub fn borrow_permission_load_slot() -> bool
    ensures result == false
{
    InstShape::LoadSlot.uses_borrow_permissions()
}

pub fn borrow_permission_close_frame() -> bool
    ensures result == false
{
    InstShape::CloseFrame.uses_borrow_permissions()
}

pub fn borrow_permission_coro_suspend() -> bool
    ensures result == false
{
    InstShape::CoroSuspend.uses_borrow_permissions()
}

pub fn borrow_permission_invoke() -> bool
    ensures result == false
{
    InstShape::Invoke.uses_borrow_permissions()
}

pub fn borrow_permission_landing_pad() -> bool
    ensures result == false
{
    InstShape::LandingPad.uses_borrow_permissions()
}

pub fn borrow_permission_resume() -> bool
    ensures result == false
{
    InstShape::Resume.uses_borrow_permissions()
}

pub fn borrow_permission_assert_invoke() -> bool
    ensures result == false
{
    InstShape::AssertInvoke.uses_borrow_permissions()
}

pub fn borrow_permission_drop_invoke() -> bool
    ensures result == false
{
    InstShape::DropInvoke.uses_borrow_permissions()
}

pub fn borrow_permission_invoke_indirect() -> bool
    ensures result == false
{
    InstShape::InvokeIndirect.uses_borrow_permissions()
}

pub fn borrow_permission_dialect_op() -> bool
    ensures result == false
{
    InstShape::DialectOp.uses_borrow_permissions()
}

pub fn borrow_permission_make_aggregate() -> bool
    ensures result == false
{
    InstShape::MakeAggregate.uses_borrow_permissions()
}

pub fn borrow_permission_array_splat() -> bool
    ensures result == false
{
    InstShape::ArraySplat.uses_borrow_permissions()
}

pub fn borrow_permission_make_closure() -> bool
    ensures result == false
{
    InstShape::MakeClosure.uses_borrow_permissions()
}

pub fn borrow_permission_tensor_contract() -> bool
    ensures result == false
{
    InstShape::TensorContract.uses_borrow_permissions()
}

pub fn borrow_permission_tensor_map() -> bool
    ensures result == false
{
    InstShape::TensorMap.uses_borrow_permissions()
}

pub fn borrow_permission_tensor_reduce() -> bool
    ensures result == false
{
    InstShape::TensorReduce.uses_borrow_permissions()
}

pub fn borrow_permission_tensor_view() -> bool
    ensures result == false
{
    InstShape::TensorView.uses_borrow_permissions()
}

pub fn borrow_permission_tensor_gather() -> bool
    ensures result == false
{
    InstShape::TensorGather.uses_borrow_permissions()
}

pub fn borrow_permission_tensor_scatter() -> bool
    ensures result == false
{
    InstShape::TensorScatter.uses_borrow_permissions()
}

// --------------------------------------------------------------------------
// visibility_contradicts_linkage (this crate) — ContradictoryFunctionVisibility
// (WS3.10); calls Linkage::is_module_local across the crate boundary
// --------------------------------------------------------------------------

pub fn visibility_internal_default() -> bool
    ensures result == false
{
    visibility_contradicts_linkage(Linkage::Internal, Visibility::Default)
}

pub fn visibility_internal_hidden() -> bool
    ensures result
{
    visibility_contradicts_linkage(Linkage::Internal, Visibility::Hidden)
}

pub fn visibility_internal_protected() -> bool
    ensures result
{
    visibility_contradicts_linkage(Linkage::Internal, Visibility::Protected)
}

pub fn visibility_private_default() -> bool
    ensures result == false
{
    visibility_contradicts_linkage(Linkage::Private, Visibility::Default)
}

pub fn visibility_private_hidden() -> bool
    ensures result
{
    visibility_contradicts_linkage(Linkage::Private, Visibility::Hidden)
}

pub fn visibility_private_protected() -> bool
    ensures result
{
    visibility_contradicts_linkage(Linkage::Private, Visibility::Protected)
}

pub fn visibility_external_never_contradicts(visibility: Visibility) -> bool
    ensures result == false
{
    visibility_contradicts_linkage(Linkage::External, visibility)
}

pub fn visibility_weak_never_contradicts(visibility: Visibility) -> bool
    ensures result == false
{
    visibility_contradicts_linkage(Linkage::Weak, visibility)
}

pub fn visibility_link_once_never_contradicts(visibility: Visibility) -> bool
    ensures result == false
{
    visibility_contradicts_linkage(Linkage::LinkOnce, visibility)
}

pub fn visibility_available_externally_never_contradicts(visibility: Visibility) -> bool
    ensures result == false
{
    visibility_contradicts_linkage(Linkage::AvailableExternally, visibility)
}

pub fn visibility_external_weak_never_contradicts(visibility: Visibility) -> bool
    ensures result == false
{
    visibility_contradicts_linkage(Linkage::ExternalWeak, visibility)
}

pub fn visibility_weak_odr_never_contradicts(visibility: Visibility) -> bool
    ensures result == false
{
    visibility_contradicts_linkage(Linkage::WeakOdr, visibility)
}

pub fn visibility_link_once_odr_never_contradicts(visibility: Visibility) -> bool
    ensures result == false
{
    visibility_contradicts_linkage(Linkage::LinkOnceOdr, visibility)
}

// --------------------------------------------------------------------------
// evidence_admits_kind (this crate) — WS1.8 rule (d), EvidenceKindMismatch:
// TranslationValidation evidence discharges a TranslationValidation row only
// --------------------------------------------------------------------------

pub fn evidence_tv_precondition() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::Precondition,
    )
}

pub fn evidence_tv_postcondition() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::Postcondition,
    )
}

pub fn evidence_tv_loop_invariant() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::LoopInvariant,
    )
}

pub fn evidence_tv_type_invariant() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::TypeInvariant,
    )
}

pub fn evidence_tv_refinement_type() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::RefinementType,
    )
}

pub fn evidence_tv_translation_validation() -> bool
    ensures result
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::TranslationValidation,
    )
}

pub fn evidence_tv_memory_safety() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::MemorySafety,
    )
}

pub fn evidence_tv_panic_freedom() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::PanicFreedom,
    )
}

pub fn evidence_tv_temporal_safety() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::TemporalSafety,
    )
}

pub fn evidence_tv_liveness() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::Liveness,
    )
}

pub fn evidence_tv_arithmetic_safety() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::ArithmeticSafety,
    )
}

pub fn evidence_tv_bounds_check() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::BoundsCheck,
    )
}

pub fn evidence_tv_give_back_refinement() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::GiveBackRefinement,
    )
}

pub fn evidence_tv_termination() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::Termination,
    )
}

pub fn evidence_tv_ownership() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::Ownership,
    )
}

pub fn evidence_tv_custom() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::TranslationValidation,
        ObligationKindShape::Custom,
    )
}

// --------------------------------------------------------------------------
// evidence_admits_kind — GammaCrownBound evidence discharges a Postcondition
// or Custom row only
// --------------------------------------------------------------------------

pub fn evidence_gamma_precondition() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::Precondition,
    )
}

pub fn evidence_gamma_postcondition() -> bool
    ensures result
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::Postcondition,
    )
}

pub fn evidence_gamma_loop_invariant() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::LoopInvariant,
    )
}

pub fn evidence_gamma_type_invariant() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::TypeInvariant,
    )
}

pub fn evidence_gamma_refinement_type() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::RefinementType,
    )
}

pub fn evidence_gamma_translation_validation() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::TranslationValidation,
    )
}

pub fn evidence_gamma_memory_safety() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::MemorySafety,
    )
}

pub fn evidence_gamma_panic_freedom() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::PanicFreedom,
    )
}

pub fn evidence_gamma_temporal_safety() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::TemporalSafety,
    )
}

pub fn evidence_gamma_liveness() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::Liveness,
    )
}

pub fn evidence_gamma_arithmetic_safety() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::ArithmeticSafety,
    )
}

pub fn evidence_gamma_bounds_check() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::BoundsCheck,
    )
}

pub fn evidence_gamma_give_back_refinement() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::GiveBackRefinement,
    )
}

pub fn evidence_gamma_termination() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::Termination,
    )
}

pub fn evidence_gamma_ownership() -> bool
    ensures result == false
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::Ownership,
    )
}

pub fn evidence_gamma_custom() -> bool
    ensures result
{
    evidence_admits_kind(
        ProofEvidenceShape::GammaCrownBound,
        ObligationKindShape::Custom,
    )
}

// --------------------------------------------------------------------------
// evidence_admits_kind — every other evidence shape is unconstrained here
// (one law each, over every kind shape)
// --------------------------------------------------------------------------

pub fn evidence_smt_proof_unconstrained(kind: ObligationKindShape) -> bool
    ensures result
{
    evidence_admits_kind(ProofEvidenceShape::SmtProof, kind)
}

pub fn evidence_lean_proof_unconstrained(kind: ObligationKindShape) -> bool
    ensures result
{
    evidence_admits_kind(ProofEvidenceShape::LeanProof, kind)
}

pub fn evidence_kani_harness_unconstrained(kind: ObligationKindShape) -> bool
    ensures result
{
    evidence_admits_kind(ProofEvidenceShape::KaniHarness, kind)
}

pub fn evidence_trusted_unconstrained(kind: ObligationKindShape) -> bool
    ensures result
{
    evidence_admits_kind(ProofEvidenceShape::Trusted, kind)
}

pub fn evidence_inherited_from_callee_unconstrained(kind: ObligationKindShape) -> bool
    ensures result
{
    evidence_admits_kind(ProofEvidenceShape::InheritedFromCallee, kind)
}

pub fn evidence_clean_cic_unconstrained(kind: ObligationKindShape) -> bool
    ensures result
{
    evidence_admits_kind(ProofEvidenceShape::CleanCic, kind)
}

// --------------------------------------------------------------------------
// proof_ref_kind_is_ambiguous (this crate) — the category-ambiguous kinds of
// the validator's ProofRef rule
// --------------------------------------------------------------------------

pub fn ambiguous_precondition() -> bool
    ensures result
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::Precondition)
}

pub fn ambiguous_postcondition() -> bool
    ensures result
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::Postcondition)
}

pub fn ambiguous_loop_invariant() -> bool
    ensures result
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::LoopInvariant)
}

pub fn ambiguous_type_invariant() -> bool
    ensures result
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::TypeInvariant)
}

pub fn ambiguous_refinement_type() -> bool
    ensures result
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::RefinementType)
}

pub fn ambiguous_translation_validation() -> bool
    ensures result
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::TranslationValidation)
}

pub fn ambiguous_memory_safety() -> bool
    ensures result == false
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::MemorySafety)
}

pub fn ambiguous_panic_freedom() -> bool
    ensures result == false
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::PanicFreedom)
}

pub fn ambiguous_temporal_safety() -> bool
    ensures result
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::TemporalSafety)
}

pub fn ambiguous_liveness() -> bool
    ensures result
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::Liveness)
}

pub fn ambiguous_arithmetic_safety() -> bool
    ensures result == false
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::ArithmeticSafety)
}

pub fn ambiguous_bounds_check() -> bool
    ensures result == false
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::BoundsCheck)
}

pub fn ambiguous_give_back_refinement() -> bool
    ensures result == false
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::GiveBackRefinement)
}

pub fn ambiguous_termination() -> bool
    ensures result == false
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::Termination)
}

pub fn ambiguous_ownership() -> bool
    ensures result == false
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::Ownership)
}

pub fn ambiguous_custom() -> bool
    ensures result == false
{
    proof_ref_kind_is_ambiguous(ObligationKindShape::Custom)
}
