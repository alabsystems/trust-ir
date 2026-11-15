// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS5.4 — close the discharge loop: a sited `Inst::Assert` is a recognised
// assert shape (roadmap docs/roadmap/two-language-completion-roadmap.md,
// "WS5.4"; findings F-091, F-022).
//
// Before WS5.4 every obligation the direct lane births — sited on an
// `Inst::Assert` — died on "the instruction at this obligation's site is
// Assert, not a CondBr", so 0 of 10 real obligations could be discharged
// through the trust-ir handoff. These tests pin the new behaviour and its
// guards, each against the real pinned ay solver:
//
// * POSITIVE — a range-guarded (`and x, 0xff`) `u64` checked add, spelled
//   exactly as the direct lane spells it (`add.overflow` + `select %o, false,
//   true` + `assert`), discharges on the bit-blast route and is accepted by
//   `BvBlastAuthority`; the SMT sited VC backs it too.
// * NEGATIVE TWIN — the same assert without the guard stays Pending with the
//   named reason "not provable locally"; `Failed` is never minted.
// * MUTATION — the polarity is load-bearing (the inverted goal has no
//   refutation, and a certificate for the wrong polarity is refused at replay);
//   an assert on a value defined in another block is Unsupported.
// * KIND GATE (1a) — a Pending LoopInvariant and a Pending Postcondition sited
//   on a provable Assert stay Pending on BOTH routes.
// * FORMULA (1b) — a row whose producer formula states `a + b` while its site
//   checks `a - b` is not discharged and its formula is left byte-identical;
//   only the formula's ONE SMT-LIB text is matched, so an opaque payload
//   beside the goal's rendering is not discharged either.
// * crit.unex01 — the critic's real-module probe, ported over the real
//   modules the from-source compiler emitted (vendored under tests/fixtures).

#![allow(clippy::disallowed_methods)] // a test drives ay directly; a panic here is a test failure (r11 item 5, crates/trust-ir-ay/clippy.toml)

use std::collections::HashMap;

use trust_ir::Module;
use trust_ir::inst::{BinOp, ICmpOp, OverflowOp};
use trust_ir::proof::{
    BvGoal, BvTerm, ClauseSort, GoalDeriveError, ObligationKind, ObligationSite,
    PRODUCER_FORMULA_DISAGREES, ProofCertificate, ProofEvidence, ProofObligation, ProofStatus,
    bvblast_goal_formula, bvgoal_formula, bvgoal_smtlib, derive_site_goal, formula_matches_goal,
};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ProofId, ValueId};
use trust_ir_ay::bvblast::{
    BVBLAST_PROVER, BvBlastAuthority, BvBlastCertPayload, ProveError, attach_bvblast_evidence,
    prove,
};
use trust_ir_ay::vc::{
    AY_REV, VcObligationOutcome, VcSource, VcVerdict, apply_vc_outcomes, verify_function,
};
use trust_ir_build::{ModuleBuilder, validate_module, validate_module_report_with_authority};

// ============================================================================
// Fixtures
// ============================================================================

/// How the checked-arithmetic block sits in its function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    /// One block: the whole-function walk encodes it.
    SingleBlock,
    /// Entry branches to the checking block, which takes the operands as its
    /// own parameters: the SITED VC path.
    AfterBranch,
    /// One block that opens with a `call`: the whole-function walk refuses the
    /// call and the body falls back to the sited VC (WS5.4 (2)).
    WithCall,
}

struct Fixture {
    module: Module,
    func: FuncId,
    site: ObligationSite,
}

/// `fn f(a: T, b: T) -> T { let (r, o) = (a [& g]) OP (b [& g]); assert(!o); r }`
/// in the direct lane's exact spelling: `select %o, false, true` + `assert`.
fn checked(op: OverflowOp, ty: Ty, guard: Option<i128>, shape: Shape) -> Fixture {
    let mut mb = ModuleBuilder::new("ws5_4");
    let callee = if shape == Shape::WithCall {
        let callee_ft = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("callee", callee_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        fb.ret(vec![zero]);
        Some(fb.build())
    } else {
        None
    };
    let ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let func = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut fb = mb.function("checked", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, ty.clone());
    let b = fb.add_block_param(entry, ty.clone());
    fb.switch_to_block(entry);
    let (x, y) = if shape == Shape::AfterBranch {
        let body = fb.create_block();
        let x = fb.add_block_param(body, ty.clone());
        let y = fb.add_block_param(body, ty.clone());
        fb.br(body, vec![a, b]);
        fb.switch_to_block(body);
        (x, y)
    } else {
        (a, b)
    };
    if let Some(callee) = callee {
        let _ = fb.call(callee, vec![]);
    }
    let (x, y) = match guard {
        Some(mask) => {
            let m = fb.iconst(ty.clone(), mask);
            let gx = fb.binop(BinOp::And, ty.clone(), x, m);
            let gy = fb.binop(BinOp::And, ty.clone(), y, m);
            (gx, gy)
        }
        None => (x, y),
    };
    let (r, o) = fb.overflow(op, ty.clone(), x, y);
    let f = fb.bool_const(false);
    let t = fb.bool_const(true);
    let c = fb.select(Ty::Bool, o, f, t);
    fb.assert(c);
    let (block, index) = fb.last_emitted_position().expect("assert was emitted");
    fb.ret(vec![r]);
    fb.build();
    Fixture {
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        func,
        site: ObligationSite::new(func, block, index),
    }
}

/// Push a Pending row of `kind` sited on the fixture's assert.
fn sited_row(fixture: &mut Fixture, kind: ObligationKind) -> ProofId {
    let id = ProofId::new(u32::try_from(fixture.module.proof_obligations.len()).unwrap());
    fixture.module.proof_obligations.push(
        ProofObligation::new(id, kind, ProofStatus::Pending, "sited checked arithmetic")
            .with_function(fixture.func)
            .with_site(fixture.site),
    );
    id
}

fn row(module: &Module, id: ProofId) -> &ProofObligation {
    module
        .proof_obligations
        .iter()
        .find(|o| o.id == id)
        .expect("row exists")
}

fn smt_outcome(module: &Module, func: FuncId, id: ProofId) -> VcObligationOutcome {
    let vc = verify_function(module, func).expect("a VC (whole or sited) is always generated");
    vc.obligations
        .into_iter()
        .find(|(oid, _)| *oid == id)
        .map(|(_, outcome)| outcome)
        .expect("the row is function-scoped, so it has an outcome")
}

fn authority_accepts(module: &Module) -> Result<(), String> {
    let authority = BvBlastAuthority::new();
    let report = validate_module_report_with_authority(module, &authority);
    if report.errors().is_empty() {
        Ok(())
    } else {
        Err(format!("{:?}", report.errors()))
    }
}

fn explain(module: &Module, id: ProofId) -> Result<(), String> {
    let certificate = module
        .proof_certificates
        .iter()
        .find(|c| c.obligation == id)
        .expect("a certificate for the row");
    BvBlastAuthority::new().explain(module, row(module, id), certificate)
}

// ============================================================================
// Positive: the direct lane's checked add discharges when range-guarded
// ============================================================================

#[test]
fn positive_guarded_u64_add_assert_discharges_on_the_bvblast_route() {
    let mut fixture = checked(
        OverflowOp::AddOverflow,
        Ty::U64,
        Some(0xff),
        Shape::SingleBlock,
    );
    let id = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
    assert!(validate_module(&fixture.module).is_empty());

    let outcomes = attach_bvblast_evidence(&mut fixture.module);
    assert_eq!(outcomes.len(), 1, "{outcomes:?}");
    assert!(outcomes[0].discharged, "{outcomes:?}");
    assert_eq!(row(&fixture.module, id).status, ProofStatus::Discharged);
    assert_eq!(fixture.module.proof_certificates[0].prover, BVBLAST_PROVER);

    // Authority only under the replaying capability; the structural validator
    // still refuses a Discharged row it cannot replay.
    authority_accepts(&fixture.module).unwrap();
    assert!(
        validate_module(&fixture.module)
            .iter()
            .any(|e| format!("{e:?}").contains("DischargedWithoutCertificate"))
    );
}

#[test]
fn positive_every_checked_add_sub_spelling_discharges_when_guarded() {
    for (op, ty) in [
        (OverflowOp::AddOverflow, Ty::U64),
        (OverflowOp::SubOverflow, Ty::I64),
        (OverflowOp::AddOverflow, Ty::I64),
        (OverflowOp::AddOverflow, Ty::U32),
    ] {
        for shape in [Shape::SingleBlock, Shape::AfterBranch, Shape::WithCall] {
            let mut fixture = checked(op, ty.clone(), Some(0xff), shape);
            let id = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
            let outcomes = attach_bvblast_evidence(&mut fixture.module);
            assert!(
                outcomes.len() == 1 && outcomes[0].discharged,
                "{op:?} {ty} {shape:?}: {outcomes:?}"
            );
            authority_accepts(&fixture.module)
                .unwrap_or_else(|e| panic!("{op:?} {ty} {shape:?}: {e}"));
            assert_eq!(row(&fixture.module, id).status, ProofStatus::Discharged);
        }
    }
}

#[test]
fn positive_the_smt_route_backs_the_same_assert_on_every_path() {
    for shape in [Shape::SingleBlock, Shape::AfterBranch, Shape::WithCall] {
        let mut fixture = checked(OverflowOp::AddOverflow, Ty::U64, Some(0xff), shape);
        let id = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
        let vc = verify_function(&fixture.module, fixture.func).unwrap();
        assert_eq!(
            vc.obligations,
            vec![(id, VcObligationOutcome::ProvedByVc)],
            "{shape:?}: {:?}",
            vc.conditions
        );
        match shape {
            Shape::SingleBlock => {
                assert!(vc.whole_function_fallback.is_none());
                assert!(vc.conditions.iter().any(|c| c.source == VcSource::Assert));
            }
            Shape::AfterBranch => {
                assert!(vc.whole_function_fallback.is_none());
                assert!(matches!(
                    vc.conditions[0].source,
                    VcSource::LoweredAssert { obligation, expected: true } if obligation == id
                ));
            }
            Shape::WithCall => {
                // WS5.4 (2): the walk refused the call; the refusal is kept.
                let refusal = vc.whole_function_fallback.as_ref().unwrap().to_string();
                assert!(refusal.contains("Call"), "{refusal}");
                assert!(matches!(
                    vc.conditions[0].source,
                    VcSource::LoweredAssert { .. }
                ));
            }
        }
        // The SMT route records evidence but never mints a status.
        let transitions = apply_vc_outcomes(&mut fixture.module, &vc).unwrap();
        assert!(transitions.is_empty());
        assert_eq!(row(&fixture.module, id).status, ProofStatus::Pending);
    }
}

// ============================================================================
// Negative twin: no guard, so not provable locally — and never Failed
// ============================================================================

#[test]
fn negative_twin_unguarded_assert_stays_pending_not_provable_locally() {
    let mut fixture = checked(OverflowOp::AddOverflow, Ty::U64, None, Shape::SingleBlock);
    let id = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
    let outcomes = attach_bvblast_evidence(&mut fixture.module);
    assert_eq!(outcomes.len(), 1);
    assert!(!outcomes[0].discharged);
    assert!(
        outcomes[0].detail.contains("not provable locally"),
        "{}",
        outcomes[0].detail
    );
    assert!(fixture.module.proof_certificates.is_empty());
    assert_eq!(row(&fixture.module, id).status, ProofStatus::Pending);
    assert!(validate_module(&fixture.module).is_empty());

    // The SMT sited route: NotDischarged with the same named reason, and
    // `apply_vc_outcomes` mints nothing — the sited VC supplies no refutation.
    for shape in [Shape::AfterBranch, Shape::WithCall] {
        let mut fixture = checked(OverflowOp::AddOverflow, Ty::U64, None, shape);
        let id = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
        let vc = verify_function(&fixture.module, fixture.func).unwrap();
        let [(oid, VcObligationOutcome::NotDischarged { reason })] = vc.obligations.as_slice()
        else {
            panic!(
                "{shape:?}: expected NotDischarged, got {:?}",
                vc.obligations
            );
        };
        assert_eq!(*oid, id);
        assert!(reason.contains("not provable locally"), "{reason}");
        assert!(matches!(
            vc.conditions[0].verdict,
            VcVerdict::Refuted { .. }
        ));
        let transitions = apply_vc_outcomes(&mut fixture.module, &vc).unwrap();
        assert!(
            transitions.is_empty(),
            "{shape:?}: Failed must never be minted"
        );
        assert_eq!(row(&fixture.module, id).status, ProofStatus::Pending);
    }
}

// ============================================================================
// Mutation controls
// ============================================================================

/// If `lowered_assert_condition` returned `(cond, false)` for an Assert, the
/// derived goal would be the NEGATED condition. That goal has no refutation, so
/// the positive control would stop discharging: the polarity is load-bearing.
#[test]
fn mutation_the_inverted_polarity_goal_does_not_discharge() {
    let mut fixture = checked(
        OverflowOp::AddOverflow,
        Ty::U64,
        Some(0xff),
        Shape::SingleBlock,
    );
    let id = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
    let goal = derive_site_goal(&fixture.module, row(&fixture.module, id)).unwrap();
    assert!(prove(&goal).is_ok(), "the true polarity proves");
    let inverted = BvGoal::predicate(BvTerm::Not(Box::new(goal.lhs.clone())));
    assert_eq!(prove(&inverted).unwrap_err(), ProveError::NoRefutation);
}

/// A certificate proving the WRONG polarity — `assert o` where the guard makes
/// `o` always false, so `!o` is the provable fact — is refused at replay, both
/// when the row's claim names the wrong goal and when it names the right goal
/// but carries the wrong payload.
#[test]
fn mutation_a_wrong_polarity_certificate_is_refused_by_the_authority() {
    // Build `assert o` (the flag itself): FALSE under the guard.
    let mut mb = ModuleBuilder::new("wrong_polarity");
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let func = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut fb = mb.function("wrong_polarity", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let m = fb.iconst(Ty::U64, 0xff);
    let x = fb.binop(BinOp::And, Ty::U64, a, m);
    let y = fb.binop(BinOp::And, Ty::U64, b, m);
    let (r, o) = fb.overflow(OverflowOp::AddOverflow, Ty::U64, x, y);
    fb.assert(o);
    let (block, index) = fb.last_emitted_position().unwrap();
    fb.ret(vec![r]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let site = ObligationSite::new(func, block, index);
    let id = ProofId::new(0);
    module.proof_obligations.push(
        ProofObligation::new(
            id,
            ObligationKind::ArithmeticSafety,
            ProofStatus::Pending,
            "o",
        )
        .with_function(func)
        .with_site(site),
    );

    // The honest route refuses: the goal is false.
    let mut honest = module.clone();
    let outcomes = attach_bvblast_evidence(&mut honest);
    assert!(!outcomes[0].discharged, "{outcomes:?}");

    // Forge: prove the INVERTED goal and stamp it as the row's discharge.
    let true_goal = derive_site_goal(&module, &module.proof_obligations[0]).unwrap();
    let wrong = BvGoal::predicate(BvTerm::Not(Box::new(true_goal.lhs.clone())));
    let proof = prove(&wrong).expect("the wrong polarity is the provable one");
    let payload = BvBlastCertPayload::new(&wrong, proof);
    let certificate = ProofCertificate {
        obligation: id,
        prover: BVBLAST_PROVER.to_string(),
        evidence: ProofEvidence::SmtProof(payload.to_bytes().unwrap()),
        assurance: None,
    };
    for claim_goal in [&wrong, &true_goal] {
        let mut forged = module.clone();
        forged.proof_obligations[0].status = ProofStatus::Discharged;
        forged.proof_obligations[0].formula =
            bvblast_goal_formula(&site, &ObligationKind::ArithmeticSafety, claim_goal);
        forged.proof_certificates.push(certificate.clone());
        let err = explain(&forged, id).unwrap_err();
        assert!(
            err.contains("BINDING FAILURE") || err.contains("payload claims goal"),
            "{err}"
        );
        assert!(authority_accepts(&forged).is_err());
    }
}

/// An assert whose condition is defined in another block is Unsupported on the
/// SMT route and not derivable on the bit-blast route: the sited VC is
/// block-local, and a cross-block value is never assumed.
#[test]
fn mutation_an_assert_on_a_value_from_another_block_is_unsupported() {
    let mut mb = ModuleBuilder::new("cross_block_assert");
    let ft = mb.add_func_type(vec![Ty::U64], vec![]);
    let func = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut fb = mb.function("cross_block_assert", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    let check = fb.create_block();
    fb.switch_to_block(entry);
    let m = fb.iconst(Ty::U64, 0xf);
    let masked = fb.binop(BinOp::And, Ty::U64, x, m);
    let bound = fb.iconst(Ty::U64, 16);
    let cond = fb.icmp(ICmpOp::Ult, Ty::U64, masked, bound);
    fb.br(check, vec![]);
    fb.switch_to_block(check);
    fb.assert(cond); // `cond` is defined in `entry`
    let (block, index) = fb.last_emitted_position().unwrap();
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let id = ProofId::new(0);
    module.proof_obligations.push(
        ProofObligation::new(id, ObligationKind::BoundsCheck, ProofStatus::Pending, "x")
            .with_function(func)
            .with_site(ObligationSite::new(func, block, index)),
    );

    let VcObligationOutcome::Unsupported { reason } = smt_outcome(&module, func, id) else {
        panic!("expected Unsupported");
    };
    assert!(
        reason.contains("not derivable from this block's pure prefix"),
        "{reason}"
    );
    assert!(matches!(
        derive_site_goal(&module, &module.proof_obligations[0]),
        Err(GoalDeriveError::ConditionNotPure { .. })
    ));
    let outcomes = attach_bvblast_evidence(&mut module);
    assert!(!outcomes[0].discharged);
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Pending);
}

// ============================================================================
// Kind gate (1a)
// ============================================================================

#[test]
fn kind_gate_loop_invariant_and_postcondition_stay_pending_on_both_routes() {
    for shape in [Shape::SingleBlock, Shape::AfterBranch] {
        let mut fixture = checked(OverflowOp::AddOverflow, Ty::U64, Some(0xff), shape);
        // The control: an assert-class row at the same (provable) site.
        let control = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
        let invariant = sited_row(&mut fixture, ObligationKind::LoopInvariant);
        let post = sited_row(&mut fixture, ObligationKind::Postcondition);

        // SMT route: the control is backed; neither intruder is.
        let vc = verify_function(&fixture.module, fixture.func).unwrap();
        for (id, outcome) in &vc.obligations {
            if *id == control {
                assert_eq!(*outcome, VcObligationOutcome::ProvedByVc, "{shape:?}");
            } else {
                let VcObligationOutcome::Unsupported { reason } = outcome else {
                    panic!("{shape:?}: row {id:?} was backed by the assert: {outcome:?}");
                };
                assert!(
                    reason.contains("is not an assert-class obligation"),
                    "{reason}"
                );
            }
        }
        assert_eq!(vc.obligations.len(), 3);

        // Bit-blast route: only the control discharges.
        let outcomes = attach_bvblast_evidence(&mut fixture.module);
        assert_eq!(outcomes.len(), 1, "{outcomes:?}");
        assert_eq!(
            row(&fixture.module, control).status,
            ProofStatus::Discharged
        );
        for id in [invariant, post] {
            assert_eq!(row(&fixture.module, id).status, ProofStatus::Pending);
            assert!(
                matches!(
                    derive_site_goal(&fixture.module, row(&fixture.module, id)),
                    Err(GoalDeriveError::KindNotAssertClass { .. })
                ),
                "derive_site_goal must refuse the kind before reading the site"
            );
        }
        authority_accepts(&fixture.module).unwrap();

        // And the authority refuses a forged discharge of the Postcondition
        // carrying a copy of the control's genuine certificate.
        let mut forged = fixture.module.clone();
        let mut copy = forged
            .proof_certificates
            .iter()
            .find(|c| c.obligation == control)
            .unwrap()
            .clone();
        copy.obligation = post;
        forged.proof_certificates.push(copy);
        let control_formula = row(&forged, control).formula.clone();
        let target = forged
            .proof_obligations
            .iter_mut()
            .find(|o| o.id == post)
            .unwrap();
        target.status = ProofStatus::Discharged;
        target.formula = control_formula;
        assert!(authority_accepts(&forged).is_err(), "{shape:?}");
    }
}

// ============================================================================
// Formula admission (1b)
// ============================================================================

/// The goal a `a + b` checked add states, at the same value ids the sub
/// fixture uses (the two fixtures differ only in the operator).
fn add_goal_for_sub_fixture() -> BvGoal {
    let mut add = checked(
        OverflowOp::AddOverflow,
        Ty::U64,
        Some(0xff),
        Shape::SingleBlock,
    );
    let id = sited_row(&mut add, ObligationKind::ArithmeticSafety);
    derive_site_goal(&add.module, row(&add.module, id)).unwrap()
}

#[test]
fn formula_control_a_producer_formula_for_add_on_a_sub_site_is_not_discharged() {
    let add_goal = add_goal_for_sub_fixture();
    let add_formula = bvgoal_formula(&add_goal).unwrap();

    let mut fixture = checked(
        OverflowOp::SubOverflow,
        Ty::U64,
        Some(0xff),
        Shape::SingleBlock,
    );
    let id = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
    // The two sites state different goals; the refusal below comes from the
    // formula comparison, before any solving.
    let sub_goal = derive_site_goal(&fixture.module, row(&fixture.module, id)).unwrap();
    assert_ne!(bvgoal_smtlib(&sub_goal), bvgoal_smtlib(&add_goal));
    fixture
        .module
        .proof_obligations
        .iter_mut()
        .find(|o| o.id == id)
        .unwrap()
        .formula = Some(add_formula.clone());
    let before = fixture.module.stable_digest();

    let outcomes = attach_bvblast_evidence(&mut fixture.module);
    assert_eq!(outcomes.len(), 1);
    assert!(!outcomes[0].discharged);
    assert!(
        outcomes[0].detail.contains(PRODUCER_FORMULA_DISAGREES),
        "{}",
        outcomes[0].detail
    );
    assert!(fixture.module.proof_certificates.is_empty());
    assert_eq!(row(&fixture.module, id).status, ProofStatus::Pending);
    // The producer's formula is left byte-identical in the output artifact.
    assert_eq!(
        row(&fixture.module, id).formula.as_ref(),
        Some(&add_formula)
    );
    let after = fixture.module.stable_digest();
    assert_eq!(before, after, "the whole artifact is unchanged");

    // The SMT route refuses the same row by the same name.
    let VcObligationOutcome::Unsupported { reason } =
        smt_outcome(&fixture.module, fixture.func, id)
    else {
        panic!("expected Unsupported");
    };
    assert!(reason.contains(PRODUCER_FORMULA_DISAGREES), "{reason}");
}

/// The positive twin of the formula control: a producer formula that DOES
/// state the site goal is kept (never replaced by the bit-blast claim) and the
/// row discharges under the authority.
#[test]
fn formula_control_a_matching_producer_formula_is_kept_and_discharges() {
    let mut fixture = checked(
        OverflowOp::AddOverflow,
        Ty::U64,
        Some(0xff),
        Shape::SingleBlock,
    );
    let id = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
    let goal = derive_site_goal(&fixture.module, row(&fixture.module, id)).unwrap();
    let formula = bvgoal_formula(&goal).unwrap();
    assert!(formula_matches_goal(&formula, &goal));
    fixture
        .module
        .proof_obligations
        .iter_mut()
        .find(|o| o.id == id)
        .unwrap()
        .formula = Some(formula.clone());

    let outcomes = attach_bvblast_evidence(&mut fixture.module);
    assert!(outcomes[0].discharged, "{outcomes:?}");
    assert_eq!(row(&fixture.module, id).formula.as_ref(), Some(&formula));
    authority_accepts(&fixture.module).unwrap();
    assert_eq!(
        smt_outcome(
            &{
                let mut pending = fixture.module.clone();
                pending.proof_obligations[0].status = ProofStatus::Pending;
                pending.proof_certificates.clear();
                pending
            },
            fixture.func,
            id
        ),
        VcObligationOutcome::ProvedByVc
    );

    // Mutations of the formula that must each break the match, at replay too.
    type Mutation = fn(&mut trust_ir::proof::ProofFormula);
    let mutations: [(&str, Mutation); 5] = [
        ("drop-bindings", |f| f.bindings.clear()),
        ("wrong-sort", |f| {
            f.bindings[0].1.sort = ClauseSort::BitVec(32)
        }),
        ("extra-binding", |f| {
            let extra = f.bindings[0].clone();
            f.bindings.push(("v999".to_string(), extra.1));
        }),
        ("payload-drift", |f| f.payload.push(' ')),
        ("sort-not-bool", |f| {
            f.sort = Some("(_ BitVec 1)".to_string())
        }),
    ];
    for (name, mutate) in mutations {
        let mut mutated = formula.clone();
        mutate(&mut mutated);
        assert!(!formula_matches_goal(&mutated, &goal), "{name}");
        let mut tampered = fixture.module.clone();
        tampered.proof_obligations[0].formula = Some(mutated);
        let err = explain(&tampered, id).unwrap_err();
        assert!(err.contains(PRODUCER_FORMULA_DISAGREES), "{name}: {err}");
    }
}

// ============================================================================
// The Overflow / Select lowering is faithful (exhaustive at width 8)
// ============================================================================

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Reference evaluator for the fragment: `(value, width)`.
fn eval(term: &BvTerm, env: &HashMap<String, u128>) -> (u128, u32) {
    let bin = |a: &BvTerm, b: &BvTerm| (eval(a, env), eval(b, env));
    match term {
        BvTerm::Leaf { name, width } => (env[name] & mask(*width), *width),
        BvTerm::Const { value, width } => (*value, *width),
        BvTerm::Add(a, b) => {
            let ((x, w), (y, _)) = bin(a, b);
            (x.wrapping_add(y) & mask(w), w)
        }
        BvTerm::Sub(a, b) => {
            let ((x, w), (y, _)) = bin(a, b);
            (x.wrapping_sub(y) & mask(w), w)
        }
        BvTerm::And(a, b) => {
            let ((x, w), (y, _)) = bin(a, b);
            (x & y, w)
        }
        BvTerm::Or(a, b) => {
            let ((x, w), (y, _)) = bin(a, b);
            (x | y, w)
        }
        BvTerm::Xor(a, b) => {
            let ((x, w), (y, _)) = bin(a, b);
            (x ^ y, w)
        }
        BvTerm::Shl(a, b) => {
            let ((x, w), (y, _)) = bin(a, b);
            (
                if y >= u128::from(w) {
                    0
                } else {
                    (x << y) & mask(w)
                },
                w,
            )
        }
        BvTerm::Lshr(a, b) => {
            let ((x, w), (y, _)) = bin(a, b);
            (if y >= u128::from(w) { 0 } else { x >> y }, w)
        }
        BvTerm::Ashr(..) => unimplemented!("not produced by the lowerings under test"),
        BvTerm::Not(a) => {
            let (x, w) = eval(a, env);
            (!x & mask(w), w)
        }
        BvTerm::ZeroExt(a, k) => {
            let (x, w) = eval(a, env);
            (x, w + k)
        }
        BvTerm::SignExt(a, k) => {
            let (x, w) = eval(a, env);
            let neg = (x >> (w - 1)) & 1 == 1;
            let wide = w + k;
            (if neg { x | (mask(wide) & !mask(w)) } else { x }, wide)
        }
        BvTerm::Extract { inner, high, low } => {
            let (x, _) = eval(inner, env);
            ((x >> low) & mask(high - low + 1), high - low + 1)
        }
        BvTerm::Eq(a, b) => {
            let ((x, _), (y, _)) = bin(a, b);
            (u128::from(x == y), 1)
        }
        BvTerm::CarryOut { lhs, rhs, is_sub } => {
            let ((x, w), (y, _)) = bin(lhs, rhs);
            let carry = if *is_sub {
                x >= y
            } else {
                ((x + y) >> w) & 1 == 1
            };
            (u128::from(carry), 1)
        }
    }
}

/// `fn(a: T, b: T, want: T/Bool)`: assert `flag == want` (or `value == want`).
fn overflow_probe(op: OverflowOp, ty: Ty, read_flag: bool) -> (Module, ProofObligation) {
    let mut mb = ModuleBuilder::new("probe");
    let want_ty = if read_flag { Ty::Bool } else { ty.clone() };
    let ft = mb.add_func_type(vec![ty.clone(), ty.clone(), want_ty.clone()], vec![]);
    let func = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut fb = mb.function("probe", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, ty.clone());
    let b = fb.add_block_param(entry, ty.clone());
    let want = fb.add_block_param(entry, want_ty.clone());
    fb.switch_to_block(entry);
    let (r, o) = fb.overflow(op, ty.clone(), a, b);
    let read = if read_flag { o } else { r };
    let c = fb.icmp(ICmpOp::Eq, want_ty, read, want);
    fb.assert(c);
    let (block, index) = fb.last_emitted_position().unwrap();
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::ArithmeticSafety,
        ProofStatus::Pending,
        "probe",
    )
    .with_function(func)
    .with_site(ObligationSite::new(func, block, index));
    (module, obligation)
}

#[test]
fn the_overflow_lowering_matches_rust_semantics_exhaustively_at_width_8() {
    for op in [OverflowOp::AddOverflow, OverflowOp::SubOverflow] {
        for ty in [Ty::U8, Ty::I8] {
            for read_flag in [false, true] {
                let (module, obligation) = overflow_probe(op, ty.clone(), read_flag);
                let goal = derive_site_goal(&module, &obligation).unwrap();
                let params = &module.functions[0].blocks[0].params;
                let (va, vb, vw) = (params[0].0, params[1].0, params[2].0);
                let name = |v: ValueId| format!("v{}", v.index());
                for x in 0u8..=255 {
                    for y in 0u8..=255 {
                        let (value, flag) = match (op, ty.is_signed()) {
                            (OverflowOp::AddOverflow, false) => x.overflowing_add(y),
                            (OverflowOp::SubOverflow, false) => x.overflowing_sub(y),
                            (OverflowOp::AddOverflow, true) => {
                                let (v, f) = (x as i8).overflowing_add(y as i8);
                                (v as u8, f)
                            }
                            (_, true) => {
                                let (v, f) = (x as i8).overflowing_sub(y as i8);
                                (v as u8, f)
                            }
                            _ => unreachable!(),
                        };
                        let expected = if read_flag {
                            u128::from(flag)
                        } else {
                            u128::from(value)
                        };
                        let mut env = HashMap::new();
                        env.insert(name(va), u128::from(x));
                        env.insert(name(vb), u128::from(y));
                        env.insert(name(vw), expected);
                        assert_eq!(
                            eval(&goal.lhs, &env).0,
                            1,
                            "{op:?} {ty} flag={read_flag} x={x} y={y}"
                        );
                        // And the goal is not vacuously true: a wrong `want` fails.
                        env.insert(name(vw), expected ^ 1);
                        assert_eq!(eval(&goal.lhs, &env).0, 0);
                    }
                }
            }
        }
    }
}

#[test]
fn the_select_lowering_matches_its_semantics_exhaustively() {
    for ty in [Ty::Bool, Ty::U8] {
        let mut mb = ModuleBuilder::new("select_probe");
        let ft = mb.add_func_type(vec![Ty::Bool, ty.clone(), ty.clone(), ty.clone()], vec![]);
        let func = mb
            .peek_next_func_id()
            .expect("peek_next_func_id: test fixture");
        let mut fb = mb.function("select_probe", ft);
        let entry = fb.create_block();
        let c = fb.add_block_param(entry, Ty::Bool);
        let t = fb.add_block_param(entry, ty.clone());
        let e = fb.add_block_param(entry, ty.clone());
        let want = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let s = fb.select(ty.clone(), c, t, e);
        let eq = fb.icmp(ICmpOp::Eq, ty.clone(), s, want);
        fb.assert(eq);
        let (block, index) = fb.last_emitted_position().unwrap();
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let obligation = ProofObligation::new(
            ProofId::new(0),
            ObligationKind::BoundsCheck,
            ProofStatus::Pending,
            "select",
        )
        .with_function(func)
        .with_site(ObligationSite::new(func, block, index));
        let goal = derive_site_goal(&module, &obligation).unwrap();
        let top: u128 = if ty == Ty::Bool { 1 } else { 255 };
        let name = |v: ValueId| format!("v{}", v.index());
        for cv in 0..=1u128 {
            for tv in 0..=top {
                for ev in [0, 1, top / 2, top] {
                    let expected = if cv == 1 { tv } else { ev };
                    let mut env = HashMap::new();
                    env.insert(name(c), cv);
                    env.insert(name(t), tv);
                    env.insert(name(e), ev);
                    env.insert(name(want), expected);
                    assert_eq!(eval(&goal.lhs, &env).0, 1, "{ty} c={cv} t={tv} e={ev}");
                    env.insert(name(want), expected ^ 1);
                    assert_eq!(eval(&goal.lhs, &env).0, 0);
                }
            }
        }
    }
}

#[test]
fn mul_overflow_stays_outside_the_bitblast_fragment() {
    let (module, obligation) = overflow_probe(OverflowOp::MulOverflow, Ty::U8, true);
    let err = derive_site_goal(&module, &obligation).unwrap_err();
    assert!(
        matches!(&err, GoalDeriveError::Unsupported { detail } if detail.contains("MulOverflow")),
        "{err:?}"
    );
}

// ============================================================================
// crit.unex01 — the critic's real-module probe, ported
// ============================================================================

/// The real modules the from-source compiler emitted (trustc 5b45b83b8,
/// archived proof program 2026-09-17, Part A units p01/p04/p05), vendored as
/// text with the absolute source path replaced by the file name.
const REAL_MODULES: [(&str, &str); 3] = [
    (
        "p01_rust_contracts",
        include_str!("fixtures/p01_rust_contracts.trust-ir.txt"),
    ),
    (
        "p04_rust_slice_index",
        include_str!("fixtures/p04_rust_slice_index.trust-ir.txt"),
    ),
    (
        "p05_rust_checked_arith",
        include_str!("fixtures/p05_rust_checked_arith.trust-ir.txt"),
    ),
];

/// crit.unex01 (F-091). GAP was: every real obligation died on "the
/// instruction at this obligation's site is Assert, not a CondBr", and
/// `verify_function` errored on every body holding a `Call` or a fat slice
/// parameter. PASS now: every real row reaches a REAL verdict on both routes
/// — none of them the shape refusal — and every body gets a VC.
///
/// The honest count is recorded, not inflated: 0 of these 8 rows discharge,
/// because each needs a hypothesis the block-local, hypothesis-free goal does
/// not have (a caller precondition, a dominating branch, or a callee result).
/// The `>0` flip of `a.discharge.real_obligations` is the ~/trust Part A row
/// (WS5.1 lane), measured on the producer's corpus.
#[test]
fn crit_unex01_real_module_asserts_reach_real_verdicts() {
    let mut rows = 0usize;
    let mut discharged = 0usize;
    for (name, text) in REAL_MODULES {
        let mut module = trust_ir::parser::parse_module(text)
            .unwrap_or_else(|e| panic!("{name}: vendored module parses: {e}"));
        for function in module.functions.iter().filter(|f| !f.is_declaration()) {
            let vc = verify_function(&module, function.id)
                .unwrap_or_else(|e| panic!("{name}::{}: no VC: {e}", function.name));
            for (_, outcome) in &vc.obligations {
                let reason = match outcome {
                    VcObligationOutcome::ProvedByVc => String::new(),
                    VcObligationOutcome::NotDischarged { reason }
                    | VcObligationOutcome::Unsupported { reason } => reason.clone(),
                };
                assert!(
                    !reason.contains("not a CondBr"),
                    "{name}::{}: {reason}",
                    function.name
                );
            }
        }
        let outcomes = attach_bvblast_evidence(&mut module);
        for outcome in &outcomes {
            rows += 1;
            discharged += usize::from(outcome.discharged);
            assert!(
                !outcome.detail.contains("not a CondBr"),
                "{name}: {}",
                outcome.detail
            );
            assert!(
                outcome.detail.contains("not provable locally")
                    || outcome
                        .detail
                        .contains("not derivable from this block's pure prefix")
                    || outcome
                        .detail
                        .contains("MulOverflow is refused structurally"),
                "{name}: an unnamed verdict: {}",
                outcome.detail
            );
        }
        assert!(
            module
                .proof_obligations
                .iter()
                .all(|o| o.status == ProofStatus::Pending),
            "{name}: no status is ever minted without a proof"
        );
    }
    assert_eq!((rows, discharged), (8, 0), "the recorded real-module count");
}

/// The discharged artifact's provenance stamps are this build's pinned ay
/// revision (the trust-ir half of the WS5.4 (6) provenance control).
#[test]
fn provenance_the_certificate_names_the_pinned_ay_revision() {
    let mut fixture = checked(
        OverflowOp::AddOverflow,
        Ty::U64,
        Some(0xff),
        Shape::SingleBlock,
    );
    sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
    attach_bvblast_evidence(&mut fixture.module);
    let certificate = &fixture.module.proof_certificates[0];
    assert_eq!(certificate.prover, format!("trust-ir-ay/bvblast@{AY_REV}"));
    let ProofEvidence::SmtProof(bytes) = &certificate.evidence else {
        panic!("SmtProof evidence");
    };
    assert_eq!(
        BvBlastCertPayload::from_bytes(bytes).unwrap().ay_rev,
        AY_REV
    );
    let lock = include_str!("../../../Cargo.lock");
    assert!(
        lock.contains(&format!(
            "git+https://github.com/alabsystems/ay.git?rev={AY_REV}#{AY_REV}"
        )),
        "AY_REV must be the ay revision the root Cargo.lock resolves"
    );
}

// ============================================================================
// Adversarial review (WS5.4 review pass)
// ============================================================================

/// `fn f(a: T, b: T) -> T { let (r, o) = ga(a) OP gb(b); assert(!o); r }` where
/// each guard is `x <and|or> k`, so the operand ranges can be placed on either
/// side of the overflow boundary.
fn guarded_checked(
    op: OverflowOp,
    ty: Ty,
    guard_a: (BinOp, i128),
    guard_b: (BinOp, i128),
    shape: Shape,
) -> Fixture {
    let mut mb = ModuleBuilder::new("ws5_4_sharp");
    let ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let func = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut fb = mb.function("sharp", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, ty.clone());
    let b = fb.add_block_param(entry, ty.clone());
    fb.switch_to_block(entry);
    let (a, b) = if shape == Shape::AfterBranch {
        let body = fb.create_block();
        let x = fb.add_block_param(body, ty.clone());
        let y = fb.add_block_param(body, ty.clone());
        fb.br(body, vec![a, b]);
        fb.switch_to_block(body);
        (x, y)
    } else {
        (a, b)
    };
    let ka = fb.iconst(ty.clone(), guard_a.1);
    let x = fb.binop(guard_a.0, ty.clone(), a, ka);
    let kb = fb.iconst(ty.clone(), guard_b.1);
    let y = fb.binop(guard_b.0, ty.clone(), b, kb);
    let (r, o) = fb.overflow(op, ty.clone(), x, y);
    let f = fb.bool_const(false);
    let t = fb.bool_const(true);
    let c = fb.select(Ty::Bool, o, f, t);
    fb.assert(c);
    let (block, index) = fb.last_emitted_position().unwrap();
    fb.ret(vec![r]);
    fb.build();
    Fixture {
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        func,
        site: ObligationSite::new(func, block, index),
    }
}

/// `(op, ty, guard a, guard b, provable)`.
type SharpCase = (OverflowOp, Ty, (BinOp, i128), (BinOp, i128), bool);

/// ADVERSARIAL (review): the Overflow lowering, driven through the REAL solver
/// on BOTH routes, at the exact overflow boundary for every signedness and
/// operator. The implementer's exhaustive check compares the lowering with a
/// test-side evaluator; this one compares the bit-blast verdict and the SMT
/// verdict with the ground truth (computed by hand from the operand ranges) and
/// with each other. A signed flag lowered as an unsigned carry, a borrow read
/// with the wrong polarity, or an operand swap flips at least one row here —
/// and a flip in the "false" direction would be a FALSE discharge.
#[test]
fn adversarial_overflow_flags_are_sharp_at_the_boundary_on_both_routes() {
    use BinOp::{And, Or};
    // (op, ty, guard a, guard b, provable) — ranges in the comments.
    let cases: [SharpCase; 16] = [
        // u8 add: [0,127] + [0,128] ≤ 255 holds; [0,128] + [0,128] reaches 256.
        (
            OverflowOp::AddOverflow,
            Ty::U8,
            (And, 0x7f),
            (And, 0x80),
            true,
        ),
        (
            OverflowOp::AddOverflow,
            Ty::U8,
            (And, 0x80),
            (And, 0x80),
            false,
        ),
        (
            OverflowOp::AddOverflow,
            Ty::U8,
            (And, 0x7f),
            (And, 0x7f),
            true,
        ),
        (
            OverflowOp::AddOverflow,
            Ty::U8,
            (Or, 0x80),
            (And, 0x7f),
            false,
        ),
        // u8 sub: {127,255} - [0,127] never borrows; {126,..} - 127 does.
        (
            OverflowOp::SubOverflow,
            Ty::U8,
            (Or, 0x7f),
            (And, 0x7f),
            true,
        ),
        (
            OverflowOp::SubOverflow,
            Ty::U8,
            (Or, 0x7e),
            (And, 0x7f),
            false,
        ),
        (
            OverflowOp::SubOverflow,
            Ty::U8,
            (Or, 0x80),
            (And, 0x7f),
            true,
        ),
        (
            OverflowOp::SubOverflow,
            Ty::U8,
            (And, 0x7f),
            (Or, 0x80),
            false,
        ),
        // i8 add: [0,63]+[0,63]; [0,127]+[0,127] reaches 254 > 127;
        // [-64,-1]+[-64,-1] ≥ -128; [-128,-1]+[-64,-1] reaches -192.
        (
            OverflowOp::AddOverflow,
            Ty::I8,
            (And, 0x3f),
            (And, 0x3f),
            true,
        ),
        (
            OverflowOp::AddOverflow,
            Ty::I8,
            (And, 0x7f),
            (And, 0x7f),
            false,
        ),
        (OverflowOp::AddOverflow, Ty::I8, (Or, -64), (Or, -64), true),
        (
            OverflowOp::AddOverflow,
            Ty::I8,
            (Or, -128),
            (Or, -64),
            false,
        ),
        // i8 sub: [-64,-1]-[0,63] ≥ -127; [-64,-1]-[0,127] reaches -191;
        // [0,63]-[-64,-1] ≤ 127; [0,127]-[-64,-1] reaches 191.
        (
            OverflowOp::SubOverflow,
            Ty::I8,
            (Or, -64),
            (And, 0x3f),
            true,
        ),
        (
            OverflowOp::SubOverflow,
            Ty::I8,
            (Or, -64),
            (And, 0x7f),
            false,
        ),
        (
            OverflowOp::SubOverflow,
            Ty::I8,
            (And, 0x3f),
            (Or, -64),
            true,
        ),
        (
            OverflowOp::SubOverflow,
            Ty::I8,
            (And, 0x7f),
            (Or, -64),
            false,
        ),
    ];
    for (op, ty, ga, gb, provable) in cases {
        for shape in [Shape::SingleBlock, Shape::AfterBranch] {
            let label = format!("{op:?} {ty} {ga:?} {gb:?} {shape:?}");
            let mut fixture = guarded_checked(op, ty.clone(), ga, gb, shape);
            let id = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
            assert!(validate_module(&fixture.module).is_empty(), "{label}");

            let smt = smt_outcome(&fixture.module, fixture.func, id);
            assert_eq!(
                smt == VcObligationOutcome::ProvedByVc,
                provable,
                "SMT route disagrees with the ground truth: {label}: {smt:?}"
            );

            let outcomes = attach_bvblast_evidence(&mut fixture.module);
            assert_eq!(outcomes.len(), 1, "{label}");
            assert_eq!(
                outcomes[0].discharged, provable,
                "bit-blast route disagrees with the ground truth: {label}: {}",
                outcomes[0].detail
            );
            if provable {
                authority_accepts(&fixture.module).unwrap_or_else(|e| panic!("{label}: {e}"));
            } else {
                assert!(
                    outcomes[0].detail.contains("not provable locally"),
                    "{label}: {}",
                    outcomes[0].detail
                );
                assert_eq!(row(&fixture.module, id).status, ProofStatus::Pending);
            }
        }
    }
}

/// ADVERSARIAL (review): result 0 of an `Overflow` node (the WRAPPED value) is
/// read by position, not confused with the flag. `(a & 0x7f) + (b & 0x7f)` at
/// `u8` is at most 254: `r <u 255` holds and `r <u 254` does not.
#[test]
fn adversarial_the_wrapped_value_result_is_read_by_position_and_is_sharp() {
    for (bound, provable) in [(255, true), (254, false)] {
        let mut mb = ModuleBuilder::new("wrapped_value");
        let ft = mb.add_func_type(vec![Ty::U8, Ty::U8], vec![]);
        let func = mb
            .peek_next_func_id()
            .expect("peek_next_func_id: test fixture");
        let mut fb = mb.function("wrapped_value", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U8);
        let b = fb.add_block_param(entry, Ty::U8);
        fb.switch_to_block(entry);
        let m = fb.iconst(Ty::U8, 0x7f);
        let x = fb.binop(BinOp::And, Ty::U8, a, m);
        let y = fb.binop(BinOp::And, Ty::U8, b, m);
        let (r, _o) = fb.overflow(OverflowOp::AddOverflow, Ty::U8, x, y);
        let k = fb.iconst(Ty::U8, bound);
        let c = fb.icmp(ICmpOp::Ult, Ty::U8, r, k);
        fb.assert(c);
        let (block, index) = fb.last_emitted_position().unwrap();
        fb.ret(vec![]);
        fb.build();
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        let id = ProofId::new(0);
        module.proof_obligations.push(
            ProofObligation::new(id, ObligationKind::BoundsCheck, ProofStatus::Pending, "r")
                .with_function(func)
                .with_site(ObligationSite::new(func, block, index)),
        );
        let outcomes = attach_bvblast_evidence(&mut module);
        assert_eq!(
            outcomes[0].discharged, provable,
            "bound {bound}: {outcomes:?}"
        );
        if provable {
            authority_accepts(&module).unwrap();
        }
    }
}

/// ADVERSARIAL (review) — a refusal must not become a vacuous pass. Before
/// WS5.4 a single-block body the whole-function walk cannot encode was an
/// `Err`. The fallback now returns the SITED VC, whose condition list omits
/// every unsited `Assert` and annotation. `all_proved()` over that list is
/// vacuously `true` — for a body whose only assert is plainly false. It must
/// answer `false` whenever the walk refused.
#[test]
fn adversarial_a_fallback_vc_never_reports_all_proved() {
    let mut mb = ModuleBuilder::new("fallback_vacuity");
    let callee_ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("callee", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    let callee = fb.build();
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    let func = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut fb = mb.function("asserts_its_argument", ft);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    let _ = fb.call(callee, vec![]);
    fb.assert(p); // unsited, and false for p = false
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    let vc = verify_function(&module, func).unwrap();
    assert!(
        vc.whole_function_fallback.is_some(),
        "the walk refuses the call"
    );
    assert!(
        vc.conditions.is_empty(),
        "the unsited assert is not a condition"
    );
    assert!(
        !vc.all_proved(),
        "a sited fallback must never read as a whole-function pass"
    );
}

/// ADVERSARIAL (review): a row carrying a bit-blast goal CLAIM stamped for a
/// DIFFERENT kind at the same site (here the ArithmeticSafety row's claim,
/// copied onto a BoundsCheck row) does not bind: the claim names its kind, and
/// every route checks it — attach, the SMT route, and the authority.
#[test]
fn adversarial_a_claim_stamped_for_another_kind_does_not_bind() {
    let mut fixture = checked(
        OverflowOp::AddOverflow,
        Ty::U64,
        Some(0xff),
        Shape::SingleBlock,
    );
    let control = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
    let mut stamped = fixture.module.clone();
    attach_bvblast_evidence(&mut stamped);
    let claim = row(&stamped, control)
        .formula
        .clone()
        .expect("stamped claim");

    let intruder = sited_row(&mut fixture, ObligationKind::BoundsCheck);
    fixture
        .module
        .proof_obligations
        .iter_mut()
        .find(|o| o.id == intruder)
        .unwrap()
        .formula = Some(claim.clone());

    let VcObligationOutcome::Unsupported { reason } =
        smt_outcome(&fixture.module, fixture.func, intruder)
    else {
        panic!("the SMT route must refuse the mis-kinded claim");
    };
    assert!(reason.contains(PRODUCER_FORMULA_DISAGREES), "{reason}");

    let outcomes = attach_bvblast_evidence(&mut fixture.module);
    let intruder_outcome = outcomes
        .iter()
        .find(|o| o.obligation == intruder.index())
        .unwrap();
    assert!(!intruder_outcome.discharged);
    assert!(
        intruder_outcome.detail.contains(PRODUCER_FORMULA_DISAGREES),
        "{}",
        intruder_outcome.detail
    );
    assert_eq!(row(&fixture.module, intruder).status, ProofStatus::Pending);
    assert_eq!(
        row(&fixture.module, intruder).formula.as_ref(),
        Some(&claim)
    );
    assert_eq!(
        row(&fixture.module, control).status,
        ProofStatus::Discharged
    );

    // Forge the discharge with the control's genuine certificate: refused.
    let mut forged = fixture.module.clone();
    let mut copy = forged
        .proof_certificates
        .iter()
        .find(|c| c.obligation == control)
        .unwrap()
        .clone();
    copy.obligation = intruder;
    forged.proof_certificates.push(copy);
    forged
        .proof_obligations
        .iter_mut()
        .find(|o| o.id == intruder)
        .unwrap()
        .status = ProofStatus::Discharged;
    assert!(explain(&forged, intruder).is_err());
    assert!(authority_accepts(&forged).is_err());
}

/// ADVERSARIAL (review): a producer formula whose bindings have the RIGHT
/// COUNT but bind one leaf twice and the other not at all is refused — the
/// count check alone would be fooled.
#[test]
fn adversarial_a_count_preserving_duplicate_binding_is_refused() {
    let mut fixture = checked(
        OverflowOp::AddOverflow,
        Ty::U64,
        Some(0xff),
        Shape::SingleBlock,
    );
    let id = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
    let goal = derive_site_goal(&fixture.module, row(&fixture.module, id)).unwrap();
    let mut formula = bvgoal_formula(&goal).unwrap();
    assert_eq!(formula.bindings.len(), 2, "two free leaves: a and b");
    formula.bindings[1] = formula.bindings[0].clone();
    assert!(!formula_matches_goal(&formula, &goal));
    fixture.module.proof_obligations[0].formula = Some(formula);
    let outcomes = attach_bvblast_evidence(&mut fixture.module);
    assert!(!outcomes[0].discharged);
    assert!(outcomes[0].detail.contains(PRODUCER_FORMULA_DISAGREES));
    assert!(fixture.module.proof_certificates.is_empty());
}

/// ONE FORMULA on the bit-blast route (the R10 verifier's residual on
/// 794601e2). `formula_matches_goal` accepted any non-`smtlib2` schema on its
/// `smtlib` rendering alone, so an ArithmeticSafety row whose OPAQUE payload
/// says "the checked add overflows" beside the goal's canonical rendering was
/// matched, Discharged by `attach_bvblast_evidence` and accepted by
/// `BvBlastAuthority`: what was proved is the goal re-derived from the IR,
/// never the row's own claim. Only the formula's one SMT-LIB text
/// (`ProofFormula::smtlib_text`) is matched now, at attach and at replay:
/// an opaque payload stays Pending with the disagreement, and a certificate
/// replayed against it is refused. Control: an `smtlib2` payload that IS the
/// goal, with no rendering, states the same one text and discharges.
#[test]
fn only_the_one_formula_text_is_matched_to_the_site_goal() {
    let fixture = || {
        let mut fixture = checked(
            OverflowOp::AddOverflow,
            Ty::U64,
            Some(0xff),
            Shape::SingleBlock,
        );
        let id = sited_row(&mut fixture, ObligationKind::ArithmeticSafety);
        (fixture, id)
    };
    let (honest, id) = fixture();
    let goal = derive_site_goal(&honest.module, row(&honest.module, id)).unwrap();
    let canonical = bvgoal_formula(&goal).unwrap();
    let mut opaque_claim = canonical.clone();
    opaque_claim.schema = "trust-types.Formula@1".to_string();
    opaque_claim.payload = "{\"claim\":\"the checked add overflows\"}".to_string();
    let mut opaque_text = canonical.clone();
    opaque_text.schema = "trust-types.Formula@1".to_string();
    let mut payload_only = canonical.clone();
    payload_only.smtlib = None;
    // The honest row discharged, for the replay half: its certificate is then
    // replayed against each case's formula.
    let (mut discharged, _) = fixture();
    discharged
        .module
        .proof_obligations
        .iter_mut()
        .find(|o| o.id == id)
        .unwrap()
        .formula = Some(canonical);
    assert!(attach_bvblast_evidence(&mut discharged.module)[0].discharged);

    let mut wrong = Vec::new();
    for (case, formula, matches) in [
        (
            "opaque payload stating another claim, goal rendering",
            opaque_claim,
            false,
        ),
        (
            "opaque payload spelling the goal, goal rendering",
            opaque_text,
            false,
        ),
        (
            "control: smtlib2 payload IS the goal, no rendering",
            payload_only,
            true,
        ),
    ] {
        let matched = formula_matches_goal(&formula, &goal);
        let (mut attached, _) = fixture();
        attached
            .module
            .proof_obligations
            .iter_mut()
            .find(|o| o.id == id)
            .unwrap()
            .formula = Some(formula.clone());
        let outcome = attach_bvblast_evidence(&mut attached.module).remove(0);
        let mut replayed = discharged.module.clone();
        replayed
            .proof_obligations
            .iter_mut()
            .find(|o| o.id == id)
            .unwrap()
            .formula = Some(formula.clone());
        let explained = explain(&replayed, id);
        let accepted = authority_accepts(&replayed);
        let right = if matches {
            matched && outcome.discharged && explained.is_ok() && accepted.is_ok()
        } else {
            !matched
                && !outcome.discharged
                && outcome.detail.contains(PRODUCER_FORMULA_DISAGREES)
                && row(&attached.module, id).formula.as_ref() == Some(&formula)
                && explained
                    .as_ref()
                    .is_err_and(|e| e.contains(PRODUCER_FORMULA_DISAGREES))
                && accepted.is_err()
        };
        if !right {
            wrong.push(format!(
                "{case}: matches {matched}, attach {outcome:?}, replay {explained:?}, \
                 authority {accepted:?}"
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "a formula text the row does not state:\n{}",
        wrong.join("\n")
    );
}
