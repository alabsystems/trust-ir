// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Roadmap WS1.8 — authority hygiene: certificate / status / scope
//! consistency and claim-style lints (findings F-018, F-022; F-021's validator
//! half landed upstream as `FuncAttrClaimViolated`, F-024's as the CLI census
//! `--forbid-prose-only`).
//!
//! Every rule is measured as a triple on ONE baseline (`checked_add`, a
//! function that overflow-checks `a + b`, asserts the flag is clear and
//! returns the sum): the positive fixture, the negative twin refused by the
//! SPECIFIC named variant, and a mutation control showing the rule refuses
//! the mutation and not the shape around it.
//!
//! * (a) `GroundCertificateStatusInconsistent`, revived narrowly: a
//!   non-inherited certificate on a `Failed` row. A `Pending` row with a
//!   certificate stays legal (the evidence-awaiting-replay carrier).
//! * (c) `ObligationSiteKindMismatch`: the kind→site-instruction table.
//! * (d) `EvidenceKindMismatch`: `TranslationValidation` evidence only on a
//!   TV row; `GammaCrownBound` only on `Postcondition` / `Custom`.
//! * (f) `UnbackedClaimOnCheck`: under
//!   `CodegenAdmission::with_refuse_unbacked_claims_on_checks(true)`, a
//!   safety-class claim on the `Assert` that IS the check needs a `ProofRef`
//!   to a kind-matched row sited on that node.
//! * DECIDE 1A `TrustedWithoutJustification`: a `Trusted` row carries a
//!   `ProofEvidence::Trusted(non-blank)` certificate.
//!
//! The proof-program rows this increment flips are ported by name at the end,
//! followed by the review pass's adversarial shapes: rule (f) on a `CondBr`
//! (its other check shape, on a second baseline `guarded`), a function-level
//! `ProofRef` that must not back a node claim, a `Trusted` justification
//! recorded for ANOTHER row, and the bound on rule (a)'s inheritance
//! exemption.

use trust_ir::constant::Constant;
use trust_ir::inst::{BinOp, OverflowOp, UnOp};
use trust_ir::proof::{
    ObligationKind, ObligationSite, ProofAnnotation, ProofCertificate, ProofEvidence,
    ProofObligation, ProofStatus,
};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, ProofId};
use trust_ir::{BodyGate, Inst, Module};
use trust_ir_build::validate::{
    CodegenAdmission, ValidationError, evidence_admits_obligation_kind,
    obligation_kind_admits_site_instruction, unbacked_claim_on_check_errors,
};
use trust_ir_build::{
    ModuleBuilder, validate_module, validate_module_for_codegen, validate_module_for_codegen_with,
};

/// The node positions of the baseline body, by role.
struct Sites {
    overflow: ObligationSite,
    assert: ObligationSite,
    ret: ObligationSite,
}

/// `fn checked_add(a: i32, b: i32) -> i32 { let (r, o) = a.overflowing_add(b);
/// assert!(!o); r }` with `claims` stamped on the `assert` node. No proof
/// tables: the caller adds rows.
fn checked_add(claims: &[ProofAnnotation]) -> (Module, FuncId, Sites) {
    let mut mb = ModuleBuilder::new("ws1_8");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("checked_add", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let (r, o) = fb.overflow(OverflowOp::AddOverflow, Ty::I32, a, b);
    // `!o` as the boolean connective `o XOR true`, the one spelling of scalar
    // Bool negation (SPEC_RATIFICATIONS §3.2): `UnOp::Not` is the BITWISE
    // complement, so a scalar `not : bool` is `UnOpNotOnScalarBool` (WS2.21).
    let t = fb.const_value(Ty::Bool, Constant::Bool(true));
    let ok = fb.binop(BinOp::BXor, Ty::Bool, o, t);
    fb.assert(ok);
    for claim in claims {
        fb.annotate_last(claim.clone())
            .expect("assert was just emitted");
    }
    fb.ret(vec![r]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    // The codegen lane's license interlock (WS1.5) is not what rule (f)
    // measures, so the baseline carries an affirmative, non-evidence-bound
    // gate: without it every `_for_codegen` assertion below would read
    // `UnlicensedBodyForCodegen` instead of the claim rule.
    m.functions[0].body_gate = Some(BodyGate::Gated {
        authority: "ws1.8-test-lane".to_string(),
        evidence: None,
    });
    let body = &m.functions[0].blocks[0].body;
    let position = |pred: fn(&Inst) -> bool| {
        body.iter()
            .position(|node| pred(&node.inst))
            .expect("the baseline body carries the node") as u32
    };
    let site = |index| ObligationSite::new(f, BlockId::new(0), index);
    let sites = Sites {
        overflow: site(position(|i| matches!(i, Inst::Overflow { .. }))),
        assert: site(position(|i| matches!(i, Inst::Assert { .. }))),
        ret: site(position(|i| matches!(i, Inst::Return { .. }))),
    };
    (m, f, sites)
}

fn row(id: u32, kind: ObligationKind, status: ProofStatus, f: FuncId) -> ProofObligation {
    ProofObligation::new(ProofId::new(id), kind, status, "ws1.8 row").with_function(f)
}

fn cert(id: u32, evidence: ProofEvidence) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(id),
        prover: "ws1.8".to_string(),
        evidence,
        assurance: None,
    }
}

fn smt() -> ProofEvidence {
    ProofEvidence::SmtProof(b"(proof unsat)".to_vec())
}

fn tv_evidence() -> ProofEvidence {
    ProofEvidence::TranslationValidation {
        rule_name: "ws1.8".to_string(),
        smt_hash: [7; 32],
    }
}

fn gamma() -> ProofEvidence {
    ProofEvidence::GammaCrownBound {
        epsilon: 0.01,
        verified_layers: 3,
    }
}

// ===========================================================================
// (a) a discharging certificate on a Failed row
// ===========================================================================

#[test]
fn a_failed_row_with_a_discharging_certificate_is_refused() {
    let (mut m, f, sites) = checked_add(&[]);
    m.proof_obligations.push(
        row(0, ObligationKind::ArithmeticSafety, ProofStatus::Failed, f).with_site(sites.assert),
    );
    assert_eq!(validate_module(&m), vec![], "a Failed row alone is honest");
    m.proof_certificates.push(cert(0, smt()));
    assert_eq!(
        validate_module(&m),
        vec![ValidationError::GroundCertificateStatusInconsistent {
            obligation: 0,
            status: "Failed",
        }]
    );
}

#[test]
fn a_control_pending_row_with_a_certificate_stays_legal() {
    // The honest "evidence awaiting replay" carrier: the same certificate on a
    // Pending row adds no error (the rule is Failed-only by design).
    let (mut m, f, sites) = checked_add(&[]);
    m.proof_obligations.push(
        row(0, ObligationKind::ArithmeticSafety, ProofStatus::Pending, f).with_site(sites.assert),
    );
    m.proof_certificates.push(cert(
        0,
        ProofEvidence::LeanProof("theorem t : True := trivial".into()),
    ));
    assert_eq!(validate_module(&m), vec![]);
}

#[test]
fn a_control_inherited_certificate_on_a_failed_row_is_not_this_rule() {
    // An inheritance edge is refused on its own terms (the callee must be a
    // kernel-grounded row, which #1 is not), never as a status inconsistency.
    let (mut m, f, sites) = checked_add(&[]);
    m.proof_obligations.push(
        row(0, ObligationKind::ArithmeticSafety, ProofStatus::Failed, f).with_site(sites.assert),
    );
    m.proof_obligations.push(
        row(1, ObligationKind::ArithmeticSafety, ProofStatus::Pending, f).with_site(sites.overflow),
    );
    m.proof_certificates.push(cert(
        0,
        ProofEvidence::InheritedFromCallee {
            callee: f,
            obligation: ProofId::new(1),
            external: None,
        },
    ));
    let errors = validate_module(&m);
    assert!(
        !errors.iter().any(|e| matches!(
            e,
            ValidationError::GroundCertificateStatusInconsistent { .. }
        )),
        "{errors:?}"
    );
}

// ===========================================================================
// (c) kind ↔ site instruction
// ===========================================================================

#[test]
fn c_bounds_check_sited_on_a_return_is_refused_and_on_an_assert_passes() {
    let (mut m, f, sites) = checked_add(&[]);
    m.proof_obligations
        .push(row(0, ObligationKind::BoundsCheck, ProofStatus::Pending, f).with_site(sites.assert));
    assert_eq!(
        validate_module(&m),
        vec![],
        "sited at the assert: the positive"
    );

    m.proof_obligations[0].site = Some(sites.ret);
    assert_eq!(
        validate_module(&m),
        vec![ValidationError::ObligationSiteKindMismatch {
            obligation: 0,
            kind: "bounds_check",
            op: "return",
        }]
    );
}

#[test]
fn c_control_an_unconstrained_kind_sits_anywhere_and_an_unsited_row_is_not_checked() {
    let (mut m, f, sites) = checked_add(&[]);
    // Postcondition is not in the table: the `ret` site is admitted.
    m.proof_obligations
        .push(row(0, ObligationKind::Postcondition, ProofStatus::Pending, f).with_site(sites.ret));
    // A BoundsCheck with NO site binds to nothing and is not this rule's.
    m.proof_obligations
        .push(row(1, ObligationKind::BoundsCheck, ProofStatus::Pending, f));
    assert_eq!(validate_module(&m), vec![]);
}

#[test]
fn c_the_table_is_exactly_the_roadmap_table() {
    use ObligationKind as K;
    let (m, _, sites) = checked_add(&[]);
    let body = &m.functions[0].blocks[0].body;
    let overflow = &body[sites.overflow.inst_index as usize].inst;
    let assert = &body[sites.assert.inst_index as usize].inst;
    let ret = &body[sites.ret.inst_index as usize].inst;
    let bxor = &body[sites.assert.inst_index as usize - 1].inst;
    assert!(matches!(bxor, Inst::BinOp { .. }));
    // A standalone `neg` node: the table is a predicate over an `Inst`, and
    // the baseline body carries no UnOp of its own.
    let unop = Inst::UnOp {
        op: UnOp::Neg,
        ty: Ty::I32,
        operand: trust_ir::value::ValueId::new(0),
    };
    let unop = &unop;
    // ArithmeticSafety: BinOp/UnOp/Overflow/Cast/Assert/CondBr.
    assert!(obligation_kind_admits_site_instruction(
        &K::ArithmeticSafety,
        bxor
    ));
    assert!(obligation_kind_admits_site_instruction(
        &K::ArithmeticSafety,
        overflow
    ));
    assert!(obligation_kind_admits_site_instruction(
        &K::ArithmeticSafety,
        unop
    ));
    assert!(obligation_kind_admits_site_instruction(
        &K::ArithmeticSafety,
        assert
    ));
    assert!(!obligation_kind_admits_site_instruction(
        &K::ArithmeticSafety,
        ret
    ));
    // BoundsCheck: not an Overflow, not a UnOp, not the boolean connective.
    assert!(obligation_kind_admits_site_instruction(
        &K::BoundsCheck,
        assert
    ));
    assert!(!obligation_kind_admits_site_instruction(
        &K::BoundsCheck,
        overflow
    ));
    assert!(!obligation_kind_admits_site_instruction(
        &K::BoundsCheck,
        unop
    ));
    assert!(!obligation_kind_admits_site_instruction(
        &K::BoundsCheck,
        bxor
    ));
    // MemorySafety: none of these three arithmetic nodes.
    assert!(!obligation_kind_admits_site_instruction(
        &K::MemorySafety,
        assert
    ));
    assert!(!obligation_kind_admits_site_instruction(
        &K::MemorySafety,
        overflow
    ));
    // PanicFreedom: Assert yes, Overflow no, UnOp no, Return YES (the
    // folded-in function-exit shape the b2 fixture carries: "returns without
    // panicking" sited at the `ret` the VC reaches).
    assert!(obligation_kind_admits_site_instruction(
        &K::PanicFreedom,
        assert
    ));
    assert!(!obligation_kind_admits_site_instruction(
        &K::PanicFreedom,
        overflow
    ));
    assert!(!obligation_kind_admits_site_instruction(
        &K::PanicFreedom,
        unop
    ));
    assert!(!obligation_kind_admits_site_instruction(
        &K::PanicFreedom,
        bxor
    ));
    assert!(obligation_kind_admits_site_instruction(
        &K::PanicFreedom,
        ret
    ));
    // Unconstrained kinds.
    for kind in [
        K::Precondition,
        K::Postcondition,
        K::LoopInvariant,
        K::TypeInvariant,
        K::RefinementType,
        K::TranslationValidation,
        K::TemporalSafety,
        K::Liveness,
        K::GiveBackRefinement,
        K::Termination,
        K::Ownership,
        K::Custom {
            namespace: "trust.protocol".into(),
            name: "x".into(),
        },
    ] {
        assert!(
            obligation_kind_admits_site_instruction(&kind, ret),
            "{kind}"
        );
    }
}

/// `fn bulk(dst: *mut u8, src: *const u8, n: u64) { copy(src, dst, n);
/// write_bytes(dst, 0, n) }` — WS3.20's bulk-memory pair, which postdates the
/// roadmap table. Body positions: `memcopy` 0, the fill-byte `const` 1,
/// `memset` 2, `ret` 3.
fn bulk() -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("ws1_8_bulk");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64], vec![]);
    let mut fb = mb.function("bulk", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let dst = fb.add_block_param(entry, Ty::Ptr);
    let src = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    fb.memcopy(dst, src, n, false);
    let zero = fb.const_value(Ty::U8, Constant::Int(0));
    fb.memset(dst, zero, n);
    fb.ret(vec![]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

/// The `MemCopy`/`MemSet` fold into the `MemorySafety` row. Positive: a
/// `MemorySafety` row sited on either bulk op validates (the shape WS3.20's
/// `InBounds` binding in `bulk_memory_ops.rs` needs). Twins: the other three
/// constrained kinds sited on a bulk op are each refused by name — the fold
/// admits a memory-access row there, never an arithmetic, bounds or panic
/// one. Control: the same `MemorySafety` row sited on the neighbouring
/// `const` is refused, so the fold admits the bulk ops and not the body
/// around them.
#[test]
fn c_memory_safety_admits_the_bulk_memory_ops_and_nothing_else_does() {
    let (base, f) = bulk();
    assert_eq!(validate_module(&base), vec![], "the clean baseline");
    let body = &base.functions[0].blocks[0].body;
    assert!(matches!(body[0].inst, Inst::MemCopy { .. }));
    assert!(matches!(body[1].inst, Inst::Const { .. }));
    assert!(matches!(body[2].inst, Inst::MemSet { .. }));
    let sited = |kind: ObligationKind, index: u32| {
        let mut m = base.clone();
        m.proof_obligations.push(
            row(0, kind, ProofStatus::Pending, f).with_site(ObligationSite::new(
                f,
                BlockId::new(0),
                index,
            )),
        );
        validate_module(&m)
    };
    for (index, op) in [(0, "memcopy"), (2, "memset")] {
        assert_eq!(
            sited(ObligationKind::MemorySafety, index),
            vec![],
            "a MemorySafety row sited on the {op}: the positive"
        );
        for (kind, name) in [
            (ObligationKind::BoundsCheck, "bounds_check"),
            (ObligationKind::ArithmeticSafety, "arithmetic_safety"),
            (ObligationKind::PanicFreedom, "panic_freedom"),
        ] {
            assert_eq!(
                sited(kind, index),
                vec![ValidationError::ObligationSiteKindMismatch {
                    obligation: 0,
                    kind: name,
                    op,
                }],
                "a {name} row sited on the {op}: the twin"
            );
        }
    }
    assert_eq!(
        sited(ObligationKind::MemorySafety, 1),
        vec![ValidationError::ObligationSiteKindMismatch {
            obligation: 0,
            kind: "memory_safety",
            op: "const",
        }],
        "the control: the neighbouring const is still refused"
    );
}

// ===========================================================================
// (d) evidence ↔ kind
// ===========================================================================

#[test]
fn d_translation_validation_evidence_on_a_postcondition_row_is_refused() {
    let (mut m, f, _) = checked_add(&[]);
    m.proof_obligations.push(row(
        0,
        ObligationKind::Postcondition,
        ProofStatus::Pending,
        f,
    ));
    m.proof_certificates.push(cert(0, tv_evidence()));
    assert_eq!(
        validate_module(&m),
        vec![ValidationError::EvidenceKindMismatch {
            obligation: 0,
            kind: "postcondition",
            evidence: "TranslationValidation",
        }]
    );
}

#[test]
fn d_control_the_same_evidence_on_a_translation_validation_row_passes() {
    let (mut m, f, _) = checked_add(&[]);
    m.proof_obligations.push(row(
        0,
        ObligationKind::TranslationValidation,
        ProofStatus::Pending,
        f,
    ));
    m.proof_certificates.push(cert(0, tv_evidence()));
    assert_eq!(validate_module(&m), vec![]);
}

#[test]
fn d_gamma_crown_bound_only_on_postcondition_or_custom() {
    let (mut m, f, sites) = checked_add(&[]);
    m.proof_obligations.push(
        row(0, ObligationKind::ArithmeticSafety, ProofStatus::Pending, f).with_site(sites.assert),
    );
    m.proof_certificates.push(cert(0, gamma()));
    assert_eq!(
        validate_module(&m),
        vec![ValidationError::EvidenceKindMismatch {
            obligation: 0,
            kind: "arithmetic_safety",
            evidence: "GammaCrownBound",
        }]
    );
    m.proof_obligations[0].kind = ObligationKind::Postcondition;
    m.proof_obligations[0].site = None;
    assert_eq!(validate_module(&m), vec![]);
    m.proof_obligations[0].kind = ObligationKind::Custom {
        namespace: "trust.protocol".into(),
        name: "bound".into(),
    };
    assert_eq!(validate_module(&m), vec![]);
    // The table itself: every other evidence variant is unconstrained here.
    for evidence in [
        smt(),
        ProofEvidence::LeanProof("t".into()),
        ProofEvidence::KaniHarness("h".into()),
        ProofEvidence::Trusted("j".into()),
    ] {
        assert!(evidence_admits_obligation_kind(
            &evidence,
            &ObligationKind::Liveness
        ));
    }
    assert!(!evidence_admits_obligation_kind(
        &tv_evidence(),
        &ObligationKind::Precondition
    ));
    assert!(!evidence_admits_obligation_kind(
        &gamma(),
        &ObligationKind::Precondition
    ));
}

// ===========================================================================
// DECIDE 1A: Trusted must be attributed
// ===========================================================================

#[test]
fn decide_1a_trusted_without_a_justifying_certificate_is_refused() {
    let (mut m, f, _) = checked_add(&[]);
    m.proof_obligations.push(row(
        0,
        ObligationKind::PanicFreedom,
        ProofStatus::Trusted,
        f,
    ));
    assert_eq!(
        validate_module(&m),
        vec![ValidationError::TrustedWithoutJustification { obligation: 0 }]
    );
    // A blank justification is no attribution.
    m.proof_certificates
        .push(cert(0, ProofEvidence::Trusted("   ".into())));
    assert_eq!(
        validate_module(&m),
        vec![ValidationError::TrustedWithoutJustification { obligation: 0 }]
    );
    // A non-Trusted certificate does not attribute faith either.
    m.proof_certificates = vec![cert(0, smt())];
    assert_eq!(
        validate_module(&m),
        vec![ValidationError::TrustedWithoutJustification { obligation: 0 }]
    );
    // The positive: attributed faith validates (and stays census-visible).
    m.proof_certificates = vec![cert(
        0,
        ProofEvidence::Trusted("hand-audited by reviewer 2026-09-20".into()),
    )];
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(m.trusted_evidence_census().len(), 1);
}

// ===========================================================================
// (f) a claim on the check itself, under the codegen policy
// ===========================================================================

fn unbacked(errors: &[ValidationError]) -> Vec<&ValidationError> {
    errors
        .iter()
        .filter(|e| matches!(e, ValidationError::UnbackedClaimOnCheck { .. }))
        .collect()
}

#[test]
fn f_no_overflow_on_an_assert_without_a_proof_ref_is_refused_under_the_flag_only() {
    let (m, _, sites) = checked_add(&[ProofAnnotation::NoOverflow]);
    // Structural tier and the default codegen lane: accepted (the producer
    // fix is WS5; the shape is what both compilers emit today, A.uf12).
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(validate_module_for_codegen(&m), vec![]);
    let off = validate_module_for_codegen_with(&m, &CodegenAdmission::pinned());
    assert_eq!(off, vec![]);
    // Flag on: refused by name, at the assert node.
    let on = validate_module_for_codegen_with(
        &m,
        &CodegenAdmission::pinned().with_refuse_unbacked_claims_on_checks(true),
    );
    assert_eq!(
        on,
        vec![ValidationError::UnbackedClaimOnCheck {
            function: "checked_add".to_string(),
            block: 0,
            inst_index: sites.assert.inst_index,
            claim: "NoOverflow",
        }]
    );
}

#[test]
fn f_a_sited_kind_matched_proof_ref_binds_the_claim() {
    // The positive: `[NoOverflow, ProofRef(#0)]` where #0 is an
    // ArithmeticSafety row sited on the assert. The rule (f) layer is clean.
    // Whether the ProofRef RESOLVES is the pre-existing kernel-tier rule
    // (`ProofRefUnresolved { missing: false }`), reported by the structural
    // pass the composed lane runs first — measured separately so the two
    // refusals cannot be confused.
    let (mut m, f, sites) = checked_add(&[
        ProofAnnotation::NoOverflow,
        ProofAnnotation::ProofRef(ProofId::new(0)),
    ]);
    m.proof_obligations.push(
        row(0, ObligationKind::ArithmeticSafety, ProofStatus::Pending, f).with_site(sites.assert),
    );
    assert_eq!(unbacked_claim_on_check_errors(&m), vec![]);
    let on = validate_module_for_codegen_with(
        &m,
        &CodegenAdmission::pinned().with_refuse_unbacked_claims_on_checks(true),
    );
    assert!(unbacked(&on).is_empty(), "{on:?}");
    assert!(
        on.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefUnresolved {
                obligation: 0,
                missing: false,
                ..
            }
        )),
        "the only refusal left is the tier rule: {on:?}"
    );

    // Twin 1: the row is sited on the OVERFLOW node, not the assert — the
    // claim on the check is unbound.
    m.proof_obligations[0].site = Some(sites.overflow);
    let twin = unbacked_claim_on_check_errors(&m);
    assert_eq!(twin.len(), 1, "{twin:?}");
    // Twin 2: right node, wrong kind (Postcondition cannot be about a check).
    m.proof_obligations[0].site = Some(sites.assert);
    m.proof_obligations[0].kind = ObligationKind::Postcondition;
    let twin = unbacked_claim_on_check_errors(&m);
    assert_eq!(twin.len(), 1, "{twin:?}");
}

#[test]
fn f_control_a_claim_on_a_non_check_node_is_not_this_rule() {
    // NoOverflow on the OVERFLOW node (not the check) is outside rule (f):
    // it is the ordinary claim the pre-existing ProofRef rules govern.
    let (mut m, _, sites) = checked_add(&[]);
    m.functions[0].blocks[0].body[sites.overflow.inst_index as usize]
        .proofs
        .push(ProofAnnotation::NoOverflow);
    assert_eq!(unbacked_claim_on_check_errors(&m), vec![]);
    // And a non-safety claim on the assert (`NoPanic`) is not one of the
    // five claims the rule names.
    let (m, _, _) = checked_add(&[ProofAnnotation::NoPanic]);
    assert_eq!(unbacked_claim_on_check_errors(&m), vec![]);
}

// ===========================================================================
// Proof-program rows flipped by this increment (roadmap §2.4), by name.
// ===========================================================================

/// `b2.gap.certificate_on_pending_or_failed_obligation_accepted` — Failed
/// half: an SmtProof certificate on a Failed row is refused by exactly
/// `GroundCertificateStatusInconsistent`; the Pending half stays accepted by
/// design (the evidence-awaiting-replay carrier).
#[test]
fn ratchet_b2_gap_certificate_on_pending_or_failed_obligation_accepted() {
    let (mut m, f, sites) = checked_add(&[]);
    m.proof_obligations.push(
        row(5, ObligationKind::ArithmeticSafety, ProofStatus::Pending, f).with_site(sites.overflow),
    );
    m.proof_obligations.push(
        row(13, ObligationKind::PanicFreedom, ProofStatus::Failed, f).with_site(sites.assert),
    );
    for id in [5, 13] {
        m.proof_certificates.push(cert(id, smt()));
    }
    assert_eq!(
        validate_module(&m),
        vec![ValidationError::GroundCertificateStatusInconsistent {
            obligation: 13,
            status: "Failed",
        }]
    );
}

/// `b2.gap.site_not_related_to_obligation_kind` — a BoundsCheck re-sited onto
/// the function's `ret` is refused by exactly `ObligationSiteKindMismatch`.
#[test]
fn ratchet_b2_gap_site_not_related_to_obligation_kind() {
    let (mut m, f, sites) = checked_add(&[]);
    m.proof_obligations.push(
        row(15, ObligationKind::BoundsCheck, ProofStatus::Pending, f).with_site(sites.assert),
    );
    assert_eq!(validate_module(&m), vec![]);
    m.proof_obligations[0].site = Some(sites.ret);
    assert_eq!(
        validate_module(&m),
        vec![ValidationError::ObligationSiteKindMismatch {
            obligation: 15,
            kind: "bounds_check",
            op: "return",
        }]
    );
}

/// `b2.gap.trusted_status_needs_no_certificate` — DECIDE 1A: a Trusted row
/// whose only (Trusted-evidence) certificate is removed is refused by exactly
/// `TrustedWithoutJustification`.
#[test]
fn ratchet_b2_gap_trusted_status_needs_no_certificate() {
    let (mut m, f, _) = checked_add(&[]);
    m.proof_obligations.push(row(
        7,
        ObligationKind::LoopInvariant,
        ProofStatus::Trusted,
        f,
    ));
    m.proof_certificates.push(cert(
        7,
        ProofEvidence::Trusted("accepted on faith by the audit".into()),
    ));
    assert_eq!(validate_module(&m), vec![]);
    m.proof_certificates
        .retain(|c| c.obligation != ProofId::new(7));
    assert_eq!(
        validate_module(&m),
        vec![ValidationError::TrustedWithoutJustification { obligation: 7 }]
    );
}

// ===========================================================================
// Adversarial review (WS1.8 review pass): shapes the increment's own tests do
// not reach. Each one is a claim that could be believed for the wrong reason.
// ===========================================================================

/// `fn guarded(c: bool, a: i32) -> i32 { if c { a } else { a } }` with
/// `claims` stamped on the `condbr` node — rule (f)'s OTHER check shape. The
/// returned site is that `condbr`.
fn guarded(claims: &[ProofAnnotation]) -> (Module, FuncId, ObligationSite) {
    let mut mb = ModuleBuilder::new("ws1_8_condbr");
    let ft = mb.add_func_type(vec![Ty::Bool, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("guarded", ft);
    let entry = fb.create_block();
    let then_block = fb.create_block();
    let else_block = fb.create_block();
    let c = fb.add_block_param(entry, Ty::Bool);
    let a = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.condbr(c, then_block, vec![], else_block, vec![]);
    for claim in claims {
        fb.annotate_last(claim.clone())
            .expect("condbr was just emitted");
    }
    fb.switch_to_block(then_block);
    fb.ret(vec![a]);
    fb.switch_to_block(else_block);
    fb.ret(vec![a]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.functions[0].body_gate = Some(BodyGate::Gated {
        authority: "ws1.8-test-lane".to_string(),
        evidence: None,
    });
    let site = ObligationSite::new(f, entry, 0);
    (m, f, site)
}

/// Rule (f) names TWO check shapes and the increment measured only `Assert`.
/// A `CondBr` is the shape a producer emits for a branch-form check, so the
/// rule has to hold there identically — and the composed lane's kind table
/// (rule (c)) has to admit the row that backs it.
#[test]
fn f_a_claim_on_a_cond_br_is_the_same_rule_as_on_an_assert() {
    // Twin: a bare `InBounds` on the branch that IS the check. The structural
    // tier never runs rule (f) (it is a codegen policy), and the flag lane
    // reports it exactly once, naming the node.
    let (m, _, site) = guarded(&[ProofAnnotation::InBounds]);
    let structural = validate_module(&m);
    assert!(
        !structural
            .iter()
            .any(|e| matches!(e, ValidationError::UnbackedClaimOnCheck { .. })),
        "the structural tier never runs rule (f): {structural:?}"
    );
    let on = validate_module_for_codegen_with(
        &m,
        &CodegenAdmission::pinned().with_refuse_unbacked_claims_on_checks(true),
    );
    let expected = ValidationError::UnbackedClaimOnCheck {
        function: "guarded".to_string(),
        block: site.block.index(),
        inst_index: 0,
        claim: "InBounds",
    };
    assert_eq!(unbacked(&on), vec![&expected], "{on:?}");

    // Positive: bound to a `BoundsCheck` row sited on that very `condbr`.
    // `BoundsCheck` is the only kind BOTH rules admit here — rule (f) accepts
    // `MemorySafety` for an `InBounds` claim, but rule (c) forbids a
    // `MemorySafety` row at an `Assert`/`CondBr` site, so that arm of (f) is
    // unreachable in the composed validator (measured by the twin below).
    let (mut m, f, site) = guarded(&[
        ProofAnnotation::InBounds,
        ProofAnnotation::ProofRef(ProofId::new(0)),
    ]);
    m.proof_obligations
        .push(row(0, ObligationKind::BoundsCheck, ProofStatus::Pending, f).with_site(site));
    assert_eq!(unbacked_claim_on_check_errors(&m), vec![]);
    let errors = validate_module(&m);
    assert!(
        !errors
            .iter()
            .any(|e| matches!(e, ValidationError::ObligationSiteKindMismatch { .. })),
        "rule (c) admits a BoundsCheck at a condbr: {errors:?}"
    );

    // Twin 2: the same row as `MemorySafety`. Rule (f) alone calls the claim
    // backed; the module validator refuses the SITE, so nothing is licensed.
    m.proof_obligations[0].kind = ObligationKind::MemorySafety;
    assert_eq!(unbacked_claim_on_check_errors(&m), vec![]);
    let errors = validate_module(&m);
    assert!(
        errors.contains(&ValidationError::ObligationSiteKindMismatch {
            obligation: 0,
            kind: "memory_safety",
            op: "condbr",
        }),
        "rule (c) refuses a MemorySafety row at a check node: {errors:?}"
    );
}

/// A `ProofRef` on the FUNCTION is a legitimate backref shape elsewhere
/// (`validate_proof_refs_with_authority` checks function-level refs too), so a
/// producer could reasonably expect it to back a claim on a node. It must not:
/// rule (f) is about the ONE node that is the runtime check, and a
/// function-level backref names no node.
#[test]
fn f_a_function_level_proof_ref_does_not_back_a_claim_on_the_check() {
    let (mut m, f, sites) = checked_add(&[ProofAnnotation::NoOverflow]);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    m.proof_obligations.push(
        row(0, ObligationKind::ArithmeticSafety, ProofStatus::Pending, f).with_site(sites.assert),
    );
    let errors = unbacked_claim_on_check_errors(&m);
    assert_eq!(
        errors,
        vec![ValidationError::UnbackedClaimOnCheck {
            function: "checked_add".to_string(),
            block: 0,
            inst_index: sites.assert.inst_index,
            claim: "NoOverflow",
        }],
        "a function-level ProofRef names no node and backs no check"
    );
    // The control: moving the SAME backref onto the check node binds it.
    m.functions[0].proofs.clear();
    m.functions[0].blocks[0].body[sites.assert.inst_index as usize]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    assert_eq!(unbacked_claim_on_check_errors(&m), vec![]);
}

/// DECIDE 1A attributes faith PER ROW. A `ProofEvidence::Trusted` certificate
/// that names a DIFFERENT obligation attributes nothing here — otherwise one
/// justification anywhere in the module would launder every Trusted row.
#[test]
fn decide_1a_a_trusted_certificate_for_another_row_does_not_attribute_this_one() {
    let (mut m, f, _) = checked_add(&[]);
    m.proof_obligations.push(row(
        0,
        ObligationKind::PanicFreedom,
        ProofStatus::Trusted,
        f,
    ));
    m.proof_obligations.push(row(
        1,
        ObligationKind::PanicFreedom,
        ProofStatus::Trusted,
        f,
    ));
    // The justification is real and well-formed, but it is row #1's.
    m.proof_certificates.push(cert(
        1,
        ProofEvidence::Trusted("hand-audited by reviewer 2026-09-22".into()),
    ));
    assert_eq!(
        validate_module(&m),
        vec![ValidationError::TrustedWithoutJustification { obligation: 0 }]
    );
    // The control: the same justification recorded for row #0 attributes it.
    m.proof_certificates.push(cert(
        0,
        ProofEvidence::Trusted("hand-audited by reviewer 2026-09-22".into()),
    ));
    assert_eq!(validate_module(&m), vec![]);
}

/// The BOUNDARY of rule (a)'s `InheritedFromCallee` exemption, pinned.
///
/// The exemption is not "an inheritance edge on a refuted row is harmless
/// because the inheritance rules refuse it" — they refuse it only while the
/// cited callee row is not kernel-ground. What actually bounds it is
/// `admit_local_inheritance`, which routes a same-module inheritance into the
/// `Discharged` authority tier ONLY from a row whose own status is
/// `Discharged`. So a `Failed` row can never be authority however it is
/// certified, and a `ProofRef` to one stays `ProofRefUnresolved`. This test
/// pins both halves; the residual — a grounded inheritance edge recorded
/// beside a refutation validates silently — is reported as a review finding,
/// not widened here, because the roadmap scopes rule (a) to non-inherited
/// certificates deliberately.
#[test]
fn a_an_inherited_certificate_on_a_failed_row_is_never_authority() {
    let (mut m, f, sites) = checked_add(&[ProofAnnotation::NoOverflow]);
    m.proof_obligations.push(
        row(0, ObligationKind::ArithmeticSafety, ProofStatus::Failed, f).with_site(sites.assert),
    );
    m.proof_obligations.push(
        row(1, ObligationKind::ArithmeticSafety, ProofStatus::Pending, f).with_site(sites.overflow),
    );
    m.proof_certificates.push(cert(
        0,
        ProofEvidence::InheritedFromCallee {
            callee: f,
            obligation: ProofId::new(1),
            external: None,
        },
    ));
    m.functions[0].blocks[0].body[sites.assert.inst_index as usize]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    let errors = validate_module(&m);
    assert!(
        !errors.iter().any(|e| matches!(
            e,
            ValidationError::GroundCertificateStatusInconsistent { .. }
        )),
        "rule (a) is scoped to non-inherited certificates: {errors:?}"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefUnresolved {
                obligation: 0,
                missing: false,
                ..
            }
        )),
        "the refuted row is not authority for the claim on the check: {errors:?}"
    );
}
