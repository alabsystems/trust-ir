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
//       co-located claim's category — a safety-class claim only by its own
//       kind, a category-ambiguous kind (Pre/Post/...) only at function level
//       and never for a safety-class claim (WS1.1);
//   (c) a B4-scoped obligation must be scoped to the enclosing function; and
//   (d) a node-level backref must cite a row sited on that very node (WS1.1).

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
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A kind-matched row for the `NoPanic` claim these fixtures carry. (They used
/// a `Postcondition`, which WS1.1 no longer lets back a safety-class claim.)
fn with_oblig(m: &mut Module, id: u32, status: ProofStatus) {
    with_oblig_kind(m, id, ObligationKind::PanicFreedom, status);
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
    // A `ProofRef` backs a co-located substantive claim of its own kind.
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
    // (c) The obligation is a B4-scoped panic-freedom row OF fn#5, but the
    // backref sits on fn#0 — a bare ProofRef cannot import another function's
    // proof.
    let mut m = one_fn();
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::PanicFreedom,
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
            ObligationKind::PanicFreedom,
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
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
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

// --------------------------------------------------------------------------
// WS1.1: the category link, not only the position.
// --------------------------------------------------------------------------

#[test]
fn ambiguous_kind_cannot_back_a_safety_claim() {
    // A Postcondition used to back ANY claim. Nothing checks that a contract
    // entails a safety claim, so it now backs none — at either level.
    let mut m = one_fn();
    with_oblig_kind(
        &mut m,
        0,
        ObligationKind::Postcondition,
        ProofStatus::Discharged,
    );
    m.functions[0].proofs.push(ProofAnnotation::NoPanic);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefKindMismatch {
                obligation: 0,
                kind: "postcondition",
                ..
            }
        )),
        "a Postcondition must not back NoPanic: {errs:?}"
    );
    // The neighbouring legal shape: a function-level claim with no obligation
    // kind (attribution, not entailment) is still structurally accepted.
    let mut pure = one_fn();
    with_oblig_kind(
        &mut pure,
        0,
        ObligationKind::Postcondition,
        ProofStatus::Discharged,
    );
    pure.functions[0].proofs.push(ProofAnnotation::Pure);
    pure.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    let errs = validate_module(&pure);
    assert!(
        !errs.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefKindMismatch { .. }
                | ValidationError::ProofRefSiteMismatch { .. }
        )),
        "function-level Pure backed by a Postcondition stays structurally legal: {errs:?}"
    );
    assert_unreplayed(&errs);
}

#[test]
fn node_level_proof_ref_requires_the_exact_site() {
    // A kind-matched but UNSITED row cannot back a node-level claim.
    use trust_ir::inst::BinOp;
    use trust_ir::proof::ObligationSite;
    use trust_ir::value::BlockId;
    let mut mb = ModuleBuilder::new("fast1_site");
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
    let base = mb.build().expect("ModuleBuilder::build: test fixture");
    let add_index = base.functions[0].blocks[0]
        .body
        .iter()
        .position(|node| !node.proofs.is_empty())
        .expect("the add node") as u32;
    let row = |site: Option<ObligationSite>| {
        let mut o = ProofObligation::new(
            ProofId::new(0),
            ObligationKind::ArithmeticSafety,
            ProofStatus::Discharged,
            "add does not overflow",
        )
        .with_function(FuncId::new(0));
        o.site = site;
        o
    };
    let site_mismatch = |m: &Module| {
        validate_module(m).iter().any(|e| {
            matches!(
                e,
                ValidationError::ProofRefSiteMismatch {
                    function: 0,
                    obligation: 0
                }
            )
        })
    };
    let mut unsited = base.clone();
    unsited.proof_obligations.push(row(None));
    assert!(
        site_mismatch(&unsited),
        "an unsited row backs no node-level claim"
    );
    let mut elsewhere = base.clone();
    elsewhere
        .proof_obligations
        .push(row(Some(ObligationSite::new(
            FuncId::new(0),
            BlockId::new(0),
            add_index + 1,
        ))));
    assert!(
        site_mismatch(&elsewhere),
        "a row sited on another node backs nothing here"
    );
    let mut exact = base.clone();
    exact.proof_obligations.push(row(Some(ObligationSite::new(
        FuncId::new(0),
        BlockId::new(0),
        add_index,
    ))));
    assert!(!site_mismatch(&exact), "the exact site binds");
}

// --------------------------------------------------------------------------
// WS1.9: the v41 specific kinds `Termination` and `Ownership` in the table.
// --------------------------------------------------------------------------

/// Positive: an `Ownership` row backs a `DataRaceFree` `ProofRef` (the pairing
/// is structurally legal; authority still has to be replayed), and a
/// `Termination` row backs `Terminates`.
#[test]
fn ws1_9_ownership_backs_data_race_free_and_termination_backs_terminates() {
    for (kind, claim) in [
        (ObligationKind::Ownership, ProofAnnotation::DataRaceFree),
        (ObligationKind::Ownership, ProofAnnotation::ValidBorrow),
        (ObligationKind::Termination, ProofAnnotation::Terminates),
    ] {
        let mut m = one_fn();
        with_oblig_kind(&mut m, 0, kind.clone(), ProofStatus::Discharged);
        m.functions[0].proofs.push(claim.clone());
        m.functions[0]
            .proofs
            .push(ProofAnnotation::ProofRef(ProofId::new(0)));
        let errs = validate_module(&m);
        assert!(
            !errs
                .iter()
                .any(|e| matches!(e, ValidationError::ProofRefKindMismatch { .. })),
            "{kind:?} must back {claim:?}: {errs:?}"
        );
        assert_unreplayed(&errs);
    }
}

/// Negative twin: a `MemorySafety` row still cannot back `DataRaceFree` (its
/// category is borrow-check, not concurrency), and an `Ownership` row cannot
/// back a value-validity claim (`NotNull`) — each refused as
/// `ProofRefKindMismatch` naming the row's kind.
#[test]
fn ws1_9_memory_safety_still_cannot_back_data_race_free() {
    for (kind, kind_name, claim) in [
        (
            ObligationKind::MemorySafety,
            "memory_safety",
            ProofAnnotation::DataRaceFree,
        ),
        (
            ObligationKind::Ownership,
            "ownership",
            ProofAnnotation::NotNull,
        ),
        (
            ObligationKind::Termination,
            "termination",
            ProofAnnotation::DataRaceFree,
        ),
    ] {
        let mut m = one_fn();
        with_oblig_kind(&mut m, 0, kind, ProofStatus::Discharged);
        m.functions[0].proofs.push(claim.clone());
        m.functions[0]
            .proofs
            .push(ProofAnnotation::ProofRef(ProofId::new(0)));
        let errs = validate_module(&m);
        assert!(
            errs.iter().any(|e| matches!(
                e,
                ValidationError::ProofRefKindMismatch {
                    obligation: 0,
                    kind,
                    ..
                } if *kind == kind_name
            )),
            "{kind_name} must not back {claim:?}: {errs:?}"
        );
    }
}

// --------------------------------------------------------------------------
// WS1.9 review: adversarial backers the increment did not write.
// --------------------------------------------------------------------------

/// A `Custom { trust.facet, .. }` row is ADMITTED (the namespace is pinned)
/// but ENTAILS nothing: `total` does not back `Terminates`, `pure` backs
/// neither the kind-less `Pure` claim nor an opaque `Custom` claim, at either
/// level. The only error each fixture adds is the kind mismatch naming
/// `custom` — the row itself validates.
#[test]
fn ws1_9_review_a_facet_row_backs_no_claim() {
    let facet = |name: &str| ObligationKind::Custom {
        namespace: "trust.facet".to_string(),
        name: name.to_string(),
    };
    for (kind, claim) in [
        (facet("total"), ProofAnnotation::Terminates),
        (facet("pure"), ProofAnnotation::Pure),
        (facet("deterministic"), ProofAnnotation::Deterministic),
        (facet("nopanic"), ProofAnnotation::NoPanic),
        (
            facet("pure"),
            ProofAnnotation::Custom(trust_ir::ProofTag::new(7)),
        ),
    ] {
        let mut m = one_fn();
        with_oblig_kind(&mut m, 0, kind, ProofStatus::Discharged);
        let errs = validate_module(&m);
        assert!(
            !errs
                .iter()
                .any(|e| matches!(e, ValidationError::UnpinnedCustomObligationNamespace { .. })),
            "trust.facet is pinned: {errs:?}"
        );
        m.functions[0].proofs.push(claim.clone());
        m.functions[0]
            .proofs
            .push(ProofAnnotation::ProofRef(ProofId::new(0)));
        let errs = validate_module(&m);
        assert!(
            errs.iter().any(|e| matches!(
                e,
                ValidationError::ProofRefKindMismatch {
                    obligation: 0,
                    kind,
                    ..
                } if *kind == "custom"
            )),
            "a trust.facet row must not back {claim:?}: {errs:?}"
        );
    }
}

/// An `Ownership` row backs a NODE-level borrow claim only when sited on that
/// very node (the WS1.1 site rule applies to the v41 kinds unchanged): an
/// unsited function-scoped row is `ProofRefSiteMismatch`; the exactly sited
/// row binds; and a sited `Termination` row on the same node is still a kind
/// mismatch, so the site never substitutes for the category.
#[test]
fn ws1_9_review_ownership_backs_a_node_claim_only_at_its_site() {
    use trust_ir::proof::ObligationSite;
    use trust_ir::value::BlockId;
    let mut mb = ModuleBuilder::new("fast1_ownership_site");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let slot = fb.alloca(Ty::I32);
    let one = fb.iconst(Ty::I32, 1);
    fb.store(Ty::I32, slot, one);
    let loaded = fb.load_proven(
        Ty::I32,
        slot,
        vec![
            ProofAnnotation::ValidBorrow,
            ProofAnnotation::ProofRef(ProofId::new(0)),
        ],
    );
    fb.ret(vec![loaded]);
    fb.build();
    let base = mb.build().expect("ModuleBuilder::build: test fixture");
    let load_index = base.functions[0].blocks[0]
        .body
        .iter()
        .position(|node| !node.proofs.is_empty())
        .expect("the load node") as u32;
    let row = |kind: ObligationKind, site: Option<ObligationSite>| {
        let mut o = ProofObligation::new(
            ProofId::new(0),
            kind,
            ProofStatus::Discharged,
            "the borrow is valid",
        )
        .with_function(FuncId::new(0));
        o.site = site;
        o
    };
    let exact = ObligationSite::new(FuncId::new(0), BlockId::new(0), load_index);
    let has =
        |errs: &[ValidationError], pred: &dyn Fn(&ValidationError) -> bool| errs.iter().any(pred);
    let site_mismatch = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::ProofRefSiteMismatch {
                function: 0,
                obligation: 0
            }
        )
    };
    let kind_mismatch = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::ProofRefKindMismatch { obligation: 0, .. }
        )
    };

    let mut unsited = base.clone();
    unsited
        .proof_obligations
        .push(row(ObligationKind::Ownership, None));
    let errs = validate_module(&unsited);
    assert!(
        has(&errs, &site_mismatch),
        "an unsited Ownership row backs no node-level claim: {errs:?}"
    );

    let mut sited = base.clone();
    sited
        .proof_obligations
        .push(row(ObligationKind::Ownership, Some(exact)));
    let errs = validate_module(&sited);
    assert!(
        !has(&errs, &site_mismatch) && !has(&errs, &kind_mismatch),
        "the exactly sited Ownership row binds the node claim: {errs:?}"
    );
    assert_unreplayed(&errs);

    let mut wrong_kind = base.clone();
    wrong_kind
        .proof_obligations
        .push(row(ObligationKind::Termination, Some(exact)));
    let errs = validate_module(&wrong_kind);
    assert!(
        has(&errs, &kind_mismatch),
        "a sited Termination row still does not back ValidBorrow: {errs:?}"
    );
}
