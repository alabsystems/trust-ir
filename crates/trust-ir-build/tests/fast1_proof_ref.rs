// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// fast-1: proof-backed annotations (`ProofAnnotation::ProofRef`).
//
// A bare annotation (e.g. NoOverflow) is an unverified claim a backend cannot
// rely on. `ProofRef(id)` ties an annotation occurrence to an obligation, but
// only an exact certificate replayed by the validator grants authority. Public
// status labels alone never make a fast path sound.
//
// fast-1 soundness (finding #91): a `ProofRef` sits in a FLAT proofs vec with no
// wire-level link to the sibling claim it backs. Without that link, a discharged
// obligation of ANY kind, for ANY function, could appear to back any co-located
// annotation. The validator re-derives the binding without a format change:
//   (a) a `ProofRef` must co-occur with a substantive claim;
//   (b) the obligation's `ObligationKind` must be compatible with at least one
//       co-located claim's category; and
//   (c) a B4-scoped obligation must be scoped to the enclosing function.

use trust_ir::Module;
use trust_ir::proof::{ObligationKind, ProofAnnotation, ProofObligation, ProofStatus};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ProofId};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{ModuleBuilder, validate_module};

/// One trivial valid function; caller adds proofs/obligations afterwards.
fn one_fn() -> Module {
    let mut mb = ModuleBuilder::new("fast1");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let z = fb.iconst(Ty::I32, 0);
    fb.ret(vec![z]);
    fb.build();
    mb.build()
}

fn with_oblig(m: &mut Module, id: u32, status: ProofStatus) {
    with_oblig_kind(m, id, ObligationKind::Postcondition, status);
}

fn with_oblig_kind(m: &mut Module, id: u32, kind: ObligationKind, status: ProofStatus) {
    m.proof_obligations
        .push(ProofObligation::new(ProofId::new(id), kind, status, "o"));
}

fn assert_unreplayed(errs: &[ValidationError]) {
    assert!(errs.iter().any(|error| matches!(
        error,
        ValidationError::ProofRefUnresolved { missing: false, .. }
    )));
}

#[test]
fn proof_ref_to_unreplayed_discharged_obligation_is_rejected() {
    let mut m = one_fn();
    with_oblig(&mut m, 0, ProofStatus::Discharged);
    // A `ProofRef` backs a co-located substantive claim; a Postcondition kind is
    // category-ambiguous and may back any claim (here NoPanic).
    m.functions[0].proofs.push(ProofAnnotation::NoPanic);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    assert_unreplayed(&validate_module(&m));
}

#[test]
fn proof_ref_to_pending_obligation_is_rejected() {
    let mut m = one_fn();
    with_oblig(&mut m, 0, ProofStatus::Pending);
    m.functions[0].proofs.push(ProofAnnotation::NoPanic);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefUnresolved { missing: false, .. }
        )),
        "proof_ref to a non-discharged obligation must be rejected: {errs:?}"
    );
}

#[test]
fn proof_ref_to_absent_obligation_is_rejected() {
    let mut m = one_fn();
    m.functions[0].proofs.push(ProofAnnotation::NoPanic);
    // No obligation #99 exists.
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(99)));
    let errs = validate_module(&m);
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::ProofRefUnresolved { missing: true, .. })),
        "proof_ref to an absent obligation must be rejected: {errs:?}"
    );
}

// --------------------------------------------------------------------------
// fast-1 soundness (finding #91): the binding checks.
// --------------------------------------------------------------------------

#[test]
fn lone_proof_ref_with_no_claim_is_rejected() {
    // (a) A `ProofRef` that is the ONLY proof backs nothing.
    let mut m = one_fn();
    with_oblig(&mut m, 0, ProofStatus::Discharged);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefWithoutClaim { obligation: 0, .. }
        )),
        "a lone proof_ref must be rejected: {errs:?}"
    );
}

#[test]
fn proof_ref_with_only_non_substantive_siblings_is_rejected() {
    // (a) `Wrapping` (a "no obligation exists" marker) and `BranchWeights` (a
    // pure codegen hint) are not substantive claims a ProofRef can back, so a
    // ProofRef alongside only those backs nothing.
    let mut m = one_fn();
    with_oblig(&mut m, 0, ProofStatus::Discharged);
    m.functions[0].proofs.push(ProofAnnotation::Wrapping);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::BranchWeights(vec![1, 1]));
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefWithoutClaim { obligation: 0, .. }
        )),
        "a proof_ref with only non-substantive siblings must be rejected: {errs:?}"
    );
}

#[test]
fn memory_safety_obligation_cannot_back_a_lone_arithmetic_claim() {
    // (b) The finding's exploit: a discharged MemorySafety obligation must NOT
    // bless a co-located NoOverflow (an arithmetic, not memory, claim).
    let mut m = one_fn();
    with_oblig_kind(
        &mut m,
        0,
        ObligationKind::MemorySafety,
        ProofStatus::Discharged,
    );
    m.functions[0].proofs.push(ProofAnnotation::NoOverflow);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefKindMismatch {
                obligation: 0,
                kind: "memory_safety",
                ..
            }
        )),
        "a MemorySafety obligation must not back a lone NoOverflow claim: {errs:?}"
    );
}

#[test]
fn compatible_memory_binding_still_requires_replayed_authority() {
    // (b) positive: MemorySafety <-> InBounds is a compatible pairing.
    let mut m = one_fn();
    with_oblig_kind(
        &mut m,
        0,
        ObligationKind::MemorySafety,
        ProofStatus::Discharged,
    );
    m.functions[0].proofs.push(ProofAnnotation::InBounds);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    assert_unreplayed(&validate_module(&m));
}

#[test]
fn compatible_panic_binding_still_requires_replayed_authority() {
    // (b) positive: PanicFreedom <-> NoOverflow is compatible (overflow panics).
    let mut m = one_fn();
    with_oblig_kind(
        &mut m,
        0,
        ObligationKind::PanicFreedom,
        ProofStatus::Discharged,
    );
    m.functions[0].proofs.push(ProofAnnotation::NoOverflow);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    assert_unreplayed(&validate_module(&m));
}

#[test]
fn panic_freedom_obligation_cannot_back_a_lone_memory_claim() {
    // (b) symmetric rejection: PanicFreedom must not bless a lone InBounds.
    let mut m = one_fn();
    with_oblig_kind(
        &mut m,
        0,
        ObligationKind::PanicFreedom,
        ProofStatus::Discharged,
    );
    m.functions[0].proofs.push(ProofAnnotation::InBounds);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefKindMismatch {
                obligation: 0,
                kind: "panic_freedom",
                ..
            }
        )),
        "a PanicFreedom obligation must not back a lone InBounds claim: {errs:?}"
    );
}

#[test]
fn matching_sibling_does_not_replace_replayed_authority() {
    // (b) accept-if-any: a MemorySafety obligation is fine as long as at least
    // ONE co-located claim is memory-category, even alongside an arithmetic one.
    let mut m = one_fn();
    with_oblig_kind(
        &mut m,
        0,
        ObligationKind::MemorySafety,
        ProofStatus::Discharged,
    );
    m.functions[0].proofs.push(ProofAnnotation::NoOverflow);
    m.functions[0].proofs.push(ProofAnnotation::NotNull);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    assert_unreplayed(&validate_module(&m));
}

#[test]
fn custom_claim_still_requires_replayed_authority() {
    // (b) Custom claims are opaque, so any kind may back them (no provable
    // mismatch). A MemorySafety obligation alongside only a Custom is accepted.
    use trust_ir::value::ProofTag;
    let mut m = one_fn();
    with_oblig_kind(
        &mut m,
        0,
        ObligationKind::MemorySafety,
        ProofStatus::Discharged,
    );
    m.functions[0]
        .proofs
        .push(ProofAnnotation::Custom(ProofTag::new(7)));
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    assert_unreplayed(&validate_module(&m));
}

#[test]
fn proof_ref_to_obligation_scoped_to_other_function_is_rejected() {
    // (c) The obligation is a B4-scoped postcondition OF fn#5, but the backref
    // sits on fn#0 — a bare ProofRef cannot import another function's proof.
    let mut m = one_fn();
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "scoped elsewhere",
        )
        .with_function(FuncId::new(5)),
    );
    m.functions[0].proofs.push(ProofAnnotation::NoPanic);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefScopeMismatch {
                function: 0,
                obligation: 0,
                owner: 5
            }
        )),
        "a proof_ref to an obligation scoped to another function must be rejected: {errs:?}"
    );
}

#[test]
fn correct_scope_does_not_replace_replayed_authority() {
    // (c) positive: the obligation is scoped to fn#0 and the backref sits on
    // fn#0 — a correctly-scoped binding.
    let mut m = one_fn();
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "scoped here",
        )
        .with_function(FuncId::new(0)),
    );
    m.functions[0].proofs.push(ProofAnnotation::NoPanic);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    assert_unreplayed(&validate_module(&m));
}

#[test]
fn unscoped_obligation_still_requires_replayed_authority() {
    // (c) back-compat: an obligation with no B4 scope (function: None) may be
    // referenced from any function.
    let mut m = one_fn();
    with_oblig(&mut m, 0, ProofStatus::Discharged); // function: None
    m.functions[0].proofs.push(ProofAnnotation::NoPanic);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    assert_unreplayed(&validate_module(&m));
}

#[test]
fn node_level_proof_ref_binding_is_enforced() {
    // The binding checks apply to instruction-node proofs too, not just
    // function-level proofs: a MemorySafety obligation cannot back a lone
    // NoOverflow on an instruction node.
    use trust_ir::inst::BinOp;
    let mut mb = ModuleBuilder::new("fast1_node");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let a = fb.iconst(Ty::I32, 1);
    let b = fb.iconst(Ty::I32, 2);
    let sum = fb.binop_proven(
        BinOp::Add,
        Ty::I32,
        a,
        b,
        vec![
            ProofAnnotation::NoOverflow,
            ProofAnnotation::ProofRef(ProofId::new(0)),
        ],
    );
    fb.ret(vec![sum]);
    fb.build();
    let mut m = mb.build();
    with_oblig_kind(
        &mut m,
        0,
        ObligationKind::MemorySafety,
        ProofStatus::Discharged,
    );

    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefKindMismatch {
                kind: "memory_safety",
                ..
            }
        )),
        "node-level proof_ref binding must be enforced: {errs:?}"
    );
}
