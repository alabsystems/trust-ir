// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// The bit-blast proof route, end to end, against the pinned ay solver.
//
// Every verdict below is a real solver verdict and every rejection is a real
// rejection: the tests mint genuine certificates, tamper with them, and assert
// that `validate_module_report_with_authority` refuses the tampered ones. The
// central claim under test is the BINDING — that a proof which validates
// perfectly is still refused when it is not a proof of THIS obligation's
// re-derived goal.

#![allow(clippy::disallowed_methods)] // a test drives ay directly; a panic here is a test failure (r11 item 5, crates/trust-ir-ay/clippy.toml)

use trust_ir::Module;
use trust_ir::inst::{BinOp, ICmpOp};
use trust_ir::proof::{
    BvGoal, BvTerm, GoalDeriveError, ObligationKind, ObligationSite, ProofCertificate,
    ProofEvidence, ProofObligation, ProofStatus, RejectingModuleProofAuthority,
    bvblast_goal_formula, bvgoal_digest_hex, derive_site_goal,
};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, ProofId};
use trust_ir_ay::bvblast::{
    BVBLAST_PROVER, BvBlastAuthority, BvBlastCertPayload, ProveError, attach_bvblast_evidence,
    prove,
};
use trust_ir_build::{ModuleBuilder, validate_module, validate_module_report_with_authority};

// ============================================================================
// Module fixtures
//
// `mask_bound(x: u64, mask, bound)` is the shape the corpus actually proves:
// `(x & mask) <u bound` guarding an indexing operation, with the failure arm
// diverging. It is TRUE iff `bound > mask`, which is what makes the sharp
// boundary testable.
// ============================================================================

struct Fixture {
    module: Module,
    obligation: ProofId,
}

fn build_mask_bound(mask: i128, bound: i128, kind: ObligationKind) -> Fixture {
    let mut mb = ModuleBuilder::new("mask_bound");
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("mask_bound", ft);

    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    let ok = fb.create_block();
    let panic = fb.create_block();

    fb.switch_to_block(entry);
    let mask_c = fb.iconst(Ty::U64, mask);
    let masked = fb.binop(BinOp::And, Ty::U64, x, mask_c);
    let bound_c = fb.iconst(Ty::U64, bound);
    let cond = fb.icmp(ICmpOp::Ult, Ty::U64, masked, bound_c);
    // The producer convention: `condbr assert_cond, <success>, <panic>`.
    fb.condbr(cond, ok, vec![], panic, vec![]);
    // entry body: 0 iconst mask, 1 and, 2 iconst bound, 3 icmp, 4 condbr
    let site_index = 4u32;

    fb.switch_to_block(ok);
    fb.ret(vec![masked]);

    fb.switch_to_block(panic);
    fb.unreachable();

    let func = fb.build();
    let obligation = mb
        .add_proof_obligation(|id| {
            ProofObligation::new(id, kind, ProofStatus::Pending, "masked index in bounds")
                .with_site(ObligationSite::new(func, entry, site_index))
        })
        .expect("a fresh obligation id");
    Fixture {
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        obligation,
    }
}

/// The proved corpus shape verbatim: `zext_64(x:u32 >>u k & 0xF) <u 16`.
fn build_escape_unicode_shape(shift: i128, bound: i128) -> Fixture {
    let mut mb = ModuleBuilder::new("escape_shape");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U64]);
    let mut fb = mb.function("escape_shape", ft);

    let entry = fb.create_block();
    let c = fb.add_block_param(entry, Ty::U32);
    let ok = fb.create_block();
    let panic = fb.create_block();

    fb.switch_to_block(entry);
    let k = fb.iconst(Ty::U32, shift);
    let shifted = fb.binop(BinOp::LShr, Ty::U32, c, k);
    let nibble_mask = fb.iconst(Ty::U32, 0xF);
    let nibble = fb.binop(BinOp::And, Ty::U32, shifted, nibble_mask);
    let widened = fb.zext(Ty::U32, Ty::U64, nibble);
    let bound_c = fb.iconst(Ty::U64, bound);
    let cond = fb.icmp(ICmpOp::Ult, Ty::U64, widened, bound_c);
    fb.condbr(cond, ok, vec![], panic, vec![]);
    // entry body: 0 iconst k, 1 lshr, 2 iconst mask, 3 and, 4 zext,
    // 5 iconst bound, 6 icmp, 7 condbr
    let site_index = 7u32;

    fb.switch_to_block(ok);
    fb.ret(vec![widened]);
    fb.switch_to_block(panic);
    fb.unreachable();

    let func = fb.build();
    let obligation = mb
        .add_proof_obligation(|id| {
            ProofObligation::new(
                id,
                ObligationKind::BoundsCheck,
                ProofStatus::Pending,
                "nibble indexes the 16-entry hex table",
            )
            .with_site(ObligationSite::new(func, entry, site_index))
        })
        .expect("a fresh obligation id");
    Fixture {
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        obligation,
    }
}

fn discharge(fixture: &mut Fixture) -> ProofCertificate {
    let outcomes = attach_bvblast_evidence(&mut fixture.module);
    assert_eq!(outcomes.len(), 1, "one in-scope obligation: {outcomes:?}");
    assert!(outcomes[0].discharged, "expected discharge: {outcomes:?}");
    fixture
        .module
        .proof_certificates
        .iter()
        .find(|c| c.obligation == fixture.obligation)
        .expect("certificate attached")
        .clone()
}

fn payload_of(certificate: &ProofCertificate) -> BvBlastCertPayload {
    let ProofEvidence::SmtProof(bytes) = &certificate.evidence else {
        panic!("expected SmtProof evidence");
    };
    BvBlastCertPayload::from_bytes(bytes).expect("decodes")
}

fn restamp(module: &mut Module, obligation: ProofId, payload: &BvBlastCertPayload) {
    let bytes = payload.to_bytes().expect("re-encodes");
    for certificate in &mut module.proof_certificates {
        if certificate.obligation == obligation {
            certificate.evidence = ProofEvidence::SmtProof(bytes.clone());
        }
    }
}

/// Is the module valid when the bv-blast replay capability is supplied?
fn accepts(module: &Module) -> bool {
    let authority = BvBlastAuthority::new();
    validate_module_report_with_authority(module, &authority)
        .errors()
        .is_empty()
}

fn rejection(module: &Module) -> String {
    let authority = BvBlastAuthority::new();
    let report = validate_module_report_with_authority(module, &authority);
    format!("{:?}", report.errors())
}

// ============================================================================
// The route works at all
// ============================================================================

#[test]
fn a_true_masked_bound_discharges_under_the_capability() {
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    let certificate = discharge(&mut fixture);
    assert_eq!(certificate.prover, BVBLAST_PROVER);

    let row = fixture
        .module
        .proof_obligations
        .iter()
        .find(|o| o.id == fixture.obligation)
        .unwrap();
    assert_eq!(row.status, ProofStatus::Discharged);
    assert!(row.formula.is_some(), "the binding claim must be stamped");

    assert!(accepts(&fixture.module), "{}", rejection(&fixture.module));
}

#[test]
fn the_corpus_shape_discharges() {
    // `zext_64((c >>u 12) & 0xF) <u 16` — one of the nine real corpus proofs.
    let mut fixture = build_escape_unicode_shape(12, 16);
    discharge(&mut fixture);
    assert!(accepts(&fixture.module), "{}", rejection(&fixture.module));
}

// ============================================================================
// (b) THE TESTS THAT FAIL WITHOUT THE BINDING
// ============================================================================

#[test]
fn a_certificate_minted_for_a_different_obligation_is_refused() {
    // THE FORGERY TEST. Both fixtures are the same KIND at the same width and
    // both certificates validate perfectly on their own. What separates them is
    // only the goal: `(x & 15) <u 16` vs `(x & 127) <u 128`. Moving one proof
    // onto the other obligation must be caught by the re-derived goal digest.
    let mut donor = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    let donor_cert = discharge(&mut donor);
    let donor_payload = payload_of(&donor_cert);

    let mut target = build_mask_bound(127, 128, ObligationKind::BoundsCheck);
    let target_cert = discharge(&mut target);

    // Sanity: both are genuine, self-validating refutations.
    assert!(donor_payload.proof.validate().is_ok());
    assert!(payload_of(&target_cert).proof.validate().is_ok());
    assert!(accepts(&target.module), "baseline must be valid");

    // Now swap the donor's proof onto the target's obligation, leaving the
    // target's own formula (and therefore its own goal claim) in place.
    restamp(&mut target.module, target.obligation, &donor_payload);
    assert!(
        !accepts(&target.module),
        "a validating proof of a DIFFERENT goal was accepted"
    );

    let authority = BvBlastAuthority::new();
    let obligation = target
        .module
        .proof_obligations
        .iter()
        .find(|o| o.id == target.obligation)
        .unwrap();
    let certificate = target
        .module
        .proof_certificates
        .iter()
        .find(|c| c.obligation == target.obligation)
        .unwrap();
    let err = authority
        .explain(&target.module, obligation, certificate)
        .unwrap_err();
    assert!(
        err.contains("payload claims goal") || err.contains("BINDING FAILURE"),
        "unexpected rejection reason: {err}"
    );
}

#[test]
fn a_payload_relabelled_with_the_right_digest_still_fails_the_cnf_check() {
    // The mirror case: fix up the payload's self-reported digest so gate (8)
    // passes, and let gate (10) — "the payload's CNF IS the re-derived CNF" —
    // do the work. AY authenticates the payload's internal graph, but only this
    // consumer-side comparison binds that graph to the live TrustIR goal.
    let mut donor = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    let donor_cert = discharge(&mut donor);
    let mut donor_payload = payload_of(&donor_cert);

    let mut target = build_mask_bound(127, 128, ObligationKind::BoundsCheck);
    discharge(&mut target);

    let target_obligation = target
        .module
        .proof_obligations
        .iter()
        .find(|o| o.id == target.obligation)
        .unwrap()
        .clone();
    let target_goal = derive_site_goal(&target.module, &target_obligation).unwrap();
    donor_payload.goal_digest = bvgoal_digest_hex(&target_goal);
    assert!(
        donor_payload.proof.validate().is_ok(),
        "the relabelled payload still validates on its own — that is the point"
    );

    restamp(&mut target.module, target.obligation, &donor_payload);
    assert!(!accepts(&target.module));

    let authority = BvBlastAuthority::new();
    let certificate = target
        .module
        .proof_certificates
        .iter()
        .find(|c| c.obligation == target.obligation)
        .unwrap();
    let err = authority
        .explain(&target.module, &target_obligation, certificate)
        .unwrap_err();
    assert!(
        err.contains("re-derived"),
        "gate (10) should have rejected this, got: {err}"
    );
}

#[test]
fn a_certificate_whose_goal_digest_is_not_a_digest_is_refused_not_a_panic() {
    // The payload's `goal_digest` is untrusted bytes. Before the decode check,
    // a spelling whose byte 16 falls inside a UTF-8 character reached gate
    // (8)'s refusal message, and slicing it there PANICKED the validator
    // instead of refusing the certificate. 21 three-byte euro signs and a `0`
    // are 64 bytes, the length of a real digest.
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    let certificate = discharge(&mut fixture);
    assert!(accepts(&fixture.module), "baseline must be valid");

    let mut payload = payload_of(&certificate);
    payload.goal_digest = format!("{}0", "\u{20ac}".repeat(21));
    assert_eq!(payload.goal_digest.len(), 64);
    assert!(!payload.goal_digest.is_char_boundary(16));
    restamp(&mut fixture.module, fixture.obligation, &payload);

    assert!(
        !accepts(&fixture.module),
        "a certificate with a non-digest goal_digest was accepted"
    );
    let obligation = fixture
        .module
        .proof_obligations
        .iter()
        .find(|o| o.id == fixture.obligation)
        .unwrap();
    let certificate = fixture
        .module
        .proof_certificates
        .iter()
        .find(|c| c.obligation == fixture.obligation)
        .unwrap();
    let err = BvBlastAuthority::new()
        .explain(&fixture.module, obligation, certificate)
        .unwrap_err();
    assert!(
        err.contains("payload goal_digest is not a goal digest (64 bytes"),
        "unexpected rejection reason: {err}"
    );
    assert!(
        !err.contains('\u{20ac}'),
        "the untrusted spelling must not be echoed: {err}"
    );
}

/// The former universal-certificate forgery: an object built from nothing that
/// older AY revisions accepted.
///
/// Current AY requires an inhabitable graph and exactly one disequality over all
/// `BitEq` outputs, so these contradictory junk units must fail native replay.
/// Keep the adversarial constructor as a cross-repository regression: TrustIR's
/// independent re-derived-CNF gate must also reject it, even if AY regresses.
fn universal_forgery() -> ay_proof::BvBlastProof {
    use ay_proof::{
        BvBlastProof, BvOp, Clause, ClauseProvenance, Lit, OperandRef, Refutation, ResRule,
        ResolutionStep, SliceObligation, VarRole, VarTable,
    };
    BvBlastProof {
        format_version: ay_proof::BV_BLAST_FORMAT_VERSION,
        obligation: SliceObligation {
            width: 64,
            op: BvOp::Add,
            lhs_args: [OperandRef::A, OperandRef::B],
            rhs_args: [OperandRef::A, OperandRef::B],
        },
        asserted_smt: "(not (= <lhs-expr> <rhs-expr>))".to_string(),
        vars: VarTable {
            roles: vec![VarRole::Aux { bit: 0 }],
        },
        bit_lemmas: Vec::new(),
        clauses: vec![
            Clause {
                id: 0,
                lits: vec![Lit::pos(0)],
                provenance: ClauseProvenance::Disequality,
            },
            Clause {
                id: 1,
                lits: vec![Lit::neg(0)],
                provenance: ClauseProvenance::Disequality,
            },
        ],
        refutation: Refutation {
            steps: vec![ResolutionStep {
                id: 2,
                clause: Vec::new(),
                rule: ResRule::Resolution,
                premises: [0, 1],
                pivot: 0,
            }],
        },
    }
}

#[test]
fn the_legacy_universal_forgery_is_rejected_by_ay_and_here() {
    // FIRST, native AY replay closes the historical arbitrary-axiom hole.
    let forgery = universal_forgery();
    assert!(
        forgery.validate().is_err(),
        "AY accepted contradictory junk Disequality axioms without an inhabitable BitEq graph"
    );
    let bytes = serde_json::to_vec(&forgery).unwrap();
    assert!(
        bytes.len() < 1000,
        "the forgery is tiny ({} bytes) — that is the point",
        bytes.len()
    );

    // SECOND, the TrustIR capability independently refuses it. Gate (9a) runs
    // AY's native replay before the more expensive source re-derivation, so the
    // strengthened checker rejects this malformed graph immediately. The later
    // re-derived-CNF gate remains independently covered by the relabelled-payload
    // tests above.
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    discharge(&mut fixture);
    let mut payload = payload_of(
        fixture
            .module
            .proof_certificates
            .iter()
            .find(|c| c.obligation == fixture.obligation)
            .unwrap(),
    );
    payload.proof = forgery;
    restamp(&mut fixture.module, fixture.obligation, &payload);
    assert!(
        !accepts(&fixture.module),
        "the legacy universal certificate was accepted as proof authority"
    );

    let authority = BvBlastAuthority::new();
    let obligation = fixture
        .module
        .proof_obligations
        .iter()
        .find(|o| o.id == fixture.obligation)
        .unwrap();
    let certificate = fixture
        .module
        .proof_certificates
        .iter()
        .find(|c| c.obligation == fixture.obligation)
        .unwrap();
    let err = authority
        .explain(&fixture.module, obligation, certificate)
        .unwrap_err();
    assert!(
        err.contains("stored refutation does not replay") && err.contains("MissingGateDefinition"),
        "gate (9a) must reject the malformed proof graph, got: {err}"
    );
}

#[test]
fn a_forged_proof_of_a_false_neighbour_is_refused() {
    // The decision-relevant forgery. `(x & 127) <u 127` is FALSE and the honest
    // exporter refuses it. Take the real proof of the neighbouring TRUE goal
    // `(x & 127) <u 128`, append junk Disequality units, and repoint the
    // refutation at them. Current AY must reject this malformed graph before it
    // can purport to prove the false goal.
    let mut donor = build_mask_bound(127, 128, ObligationKind::BoundsCheck);
    discharge(&mut donor);
    let mut payload = payload_of(
        donor
            .module
            .proof_certificates
            .iter()
            .find(|c| c.obligation == donor.obligation)
            .unwrap(),
    );

    let junk_a = payload.proof.clauses.len() as u32;
    let junk_b = junk_a + 1;
    let aux = payload.proof.vars.roles.len() as u32;
    payload
        .proof
        .vars
        .roles
        .push(ay_proof::VarRole::Aux { bit: 0 });
    payload.proof.clauses.push(ay_proof::Clause {
        id: junk_a,
        lits: vec![ay_proof::Lit::pos(aux)],
        provenance: ay_proof::ClauseProvenance::Disequality,
    });
    payload.proof.clauses.push(ay_proof::Clause {
        id: junk_b,
        lits: vec![ay_proof::Lit::neg(aux)],
        provenance: ay_proof::ClauseProvenance::Disequality,
    });
    payload.proof.refutation = ay_proof::Refutation {
        steps: vec![ay_proof::ResolutionStep {
            id: junk_b + 1,
            clause: Vec::new(),
            rule: ay_proof::ResRule::Resolution,
            premises: [junk_a, junk_b],
            pivot: aux,
        }],
    };
    assert!(
        payload.proof.validate().is_err(),
        "AY accepted a spliced refutation over contradictory junk axioms"
    );

    // Attach it to a FALSE obligation: `(x & 127) <u 127`.
    let mut target = build_mask_bound(127, 127, ObligationKind::BoundsCheck);
    let outcomes = attach_bvblast_evidence(&mut target.module);
    assert!(
        !outcomes[0].discharged,
        "the false goal must not self-prove"
    );

    // Hand-force the Discharged row the honest producer refused to mint, and
    // stamp the formula that a forger would compute from the false goal itself.
    let obligation = target
        .module
        .proof_obligations
        .iter()
        .find(|o| o.id == target.obligation)
        .unwrap()
        .clone();
    assert!(
        derive_site_goal(&target.module, &obligation).is_ok(),
        "the false goal is still DERIVABLE — it is simply not provable"
    );
    let false_goal = derive_site_goal(&target.module, &obligation).unwrap();
    payload.goal_digest = bvgoal_digest_hex(&false_goal);
    for row in &mut target.module.proof_obligations {
        if row.id == target.obligation {
            row.status = ProofStatus::Discharged;
            row.formula = bvblast_goal_formula(
                row.site.as_ref().unwrap(),
                &ObligationKind::BoundsCheck,
                &false_goal,
            );
        }
    }
    target.module.proof_certificates.push(ProofCertificate {
        obligation: target.obligation,
        prover: BVBLAST_PROVER.to_string(),
        evidence: ProofEvidence::SmtProof(payload.to_bytes().unwrap()),
        assurance: None,
    });

    assert!(
        !accepts(&target.module),
        "a FALSE obligation was discharged by a spliced proof"
    );
    // And it dies for the right reason: strengthened AY replay rejects the
    // malformed splice at gate (9a), before the more expensive source
    // re-derivation. A well-formed proof relabelled onto a different goal reaches
    // the independent binding gates, as covered by the tests above.
    let authority = BvBlastAuthority::new();
    let obligation = target
        .module
        .proof_obligations
        .iter()
        .find(|o| o.id == target.obligation)
        .unwrap();
    let certificate = target
        .module
        .proof_certificates
        .iter()
        .find(|c| c.obligation == target.obligation)
        .unwrap();
    let err = authority
        .explain(&target.module, obligation, certificate)
        .unwrap_err();
    assert!(
        err.contains("stored refutation does not replay") && err.contains("MissingGateDefinition"),
        "gate (9a) must reject the malformed proof splice, got: {err}"
    );
}

#[test]
fn a_tampered_refutation_is_refused() {
    // Three measured tamper modes, each of which ay's own `validate()` catches.
    // Asserted here because the capability must run that replay, not skip it.
    for tamper in ["drop-last-step", "flip-clause-literal", "swap-lemma-kind"] {
        let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
        discharge(&mut fixture);
        let certificate = fixture
            .module
            .proof_certificates
            .iter()
            .find(|c| c.obligation == fixture.obligation)
            .unwrap();
        let mut payload = payload_of(certificate);

        match tamper {
            "drop-last-step" => {
                payload.proof.refutation.steps.pop();
            }
            "flip-clause-literal" => {
                let clause = payload
                    .proof
                    .clauses
                    .iter_mut()
                    .find(|c| !c.lits.is_empty())
                    .unwrap();
                clause.lits[0].neg = !clause.lits[0].neg;
            }
            _ => {
                let lemma = &mut payload.proof.bit_lemmas[0];
                lemma.kind = ay_proof::BitLemmaKind::Xor3;
            }
        }
        restamp(&mut fixture.module, fixture.obligation, &payload);
        assert!(
            !accepts(&fixture.module),
            "tamper {tamper:?} was accepted as evidence"
        );
    }
}

#[test]
fn a_false_obligation_never_discharges() {
    // `(x & 15) <u 15` is FALSE (x = 15 falsifies it). The exporter must return
    // NoRefutation and no evidence may be attached.
    let mut fixture = build_mask_bound(15, 15, ObligationKind::BoundsCheck);
    let outcomes = attach_bvblast_evidence(&mut fixture.module);
    assert_eq!(outcomes.len(), 1);
    assert!(!outcomes[0].discharged, "{outcomes:?}");
    assert!(
        outcomes[0].detail.contains("SATISFIABLE"),
        "the refusal must say the obligation is false, got: {}",
        outcomes[0].detail
    );
    assert!(fixture.module.proof_certificates.is_empty());
    assert_eq!(
        fixture
            .module
            .proof_obligations
            .iter()
            .find(|o| o.id == fixture.obligation)
            .unwrap()
            .status,
        ProofStatus::Pending,
        "a false obligation must stay Pending"
    );
    assert!(validate_module(&fixture.module).is_empty());
}

// ============================================================================
// (a) Capability-absent: the SAME module is invalid structurally
// ============================================================================

#[test]
fn without_the_capability_the_discharged_row_is_invalid() {
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    discharge(&mut fixture);
    assert!(accepts(&fixture.module));

    // Plain `validate_module` supplies the rejecting default.
    let errors = validate_module(&fixture.module);
    assert!(
        errors
            .iter()
            .any(|e| format!("{e:?}").contains("DischargedWithoutCertificate")),
        "a structural validator must never admit a Discharged row: {errors:?}"
    );

    // And an explicitly rejecting capability behaves identically.
    let rejecting =
        validate_module_report_with_authority(&fixture.module, &RejectingModuleProofAuthority);
    assert!(!rejecting.errors().is_empty());
}

#[test]
fn the_default_entry_points_are_unchanged_by_the_new_seam() {
    // `validate_module_report` and `validate_module_report_with_authority(
    // &RejectingModuleProofAuthority)` must agree exactly.
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    discharge(&mut fixture);
    let plain = format!("{:?}", validate_module(&fixture.module));
    let rejecting = format!(
        "{:?}",
        validate_module_report_with_authority(&fixture.module, &RejectingModuleProofAuthority)
            .into_errors()
    );
    assert_eq!(plain, rejecting);
}

// ============================================================================
// Certificate-shape gates
// ============================================================================

#[test]
fn a_wrong_prover_string_is_refused() {
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    discharge(&mut fixture);
    for certificate in &mut fixture.module.proof_certificates {
        certificate.prover = "trust-ir-ay/bvblast@0000000000000000000000000000000000000000".into();
    }
    assert!(!accepts(&fixture.module));
}

#[test]
fn a_foreign_ay_rev_in_the_payload_is_refused() {
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    discharge(&mut fixture);
    let mut payload = payload_of(
        fixture
            .module
            .proof_certificates
            .iter()
            .find(|c| c.obligation == fixture.obligation)
            .unwrap(),
    );
    payload.ay_rev = "0000000000000000000000000000000000000000".into();
    restamp(&mut fixture.module, fixture.obligation, &payload);
    assert!(!accepts(&fixture.module));
}

#[test]
fn a_missing_or_malformed_formula_is_refused() {
    for mutate in ["drop", "wrong-schema", "wrong-site", "wrong-digest"] {
        let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
        discharge(&mut fixture);
        let row = fixture
            .module
            .proof_obligations
            .iter_mut()
            .find(|o| o.id == fixture.obligation)
            .unwrap();
        match mutate {
            "drop" => row.formula = None,
            "wrong-schema" => {
                let mut formula = row.formula.clone().unwrap();
                formula.schema = "smtlib2".into();
                row.formula = Some(formula);
            }
            "wrong-site" => {
                let mut formula = row.formula.clone().unwrap();
                formula.payload = formula.payload.replacen("site=0:0:4", "site=0:0:9", 1);
                row.formula = Some(formula);
            }
            _ => {
                let mut formula = row.formula.clone().unwrap();
                let digest_line = formula
                    .payload
                    .lines()
                    .find(|l| l.starts_with("goal="))
                    .unwrap()
                    .to_string();
                formula.payload = formula
                    .payload
                    .replace(&digest_line, &format!("goal={}", "a".repeat(64)));
                row.formula = Some(formula);
            }
        }
        assert!(
            !accepts(&fixture.module),
            "formula mutation {mutate:?} was accepted"
        );
    }
}

// ============================================================================
// Anti-vacuity and the fragment's fail-closed edges
// ============================================================================

#[test]
fn a_ground_goal_is_refused_before_it_reaches_the_solver() {
    // The corpus has 44 of these: `icmp eq u64 1, 0` on a monomorphised
    // `size_of::<T>()`. Structurally provable, informative about nothing.
    let mut mb = ModuleBuilder::new("ground");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("ground", ft);
    let entry = fb.create_block();
    let ok = fb.create_block();
    let panic = fb.create_block();
    fb.switch_to_block(entry);
    let one = fb.iconst(Ty::U64, 1);
    let zero = fb.iconst(Ty::U64, 0);
    let eq = fb.icmp(ICmpOp::Eq, Ty::U64, one, zero);
    let f = fb.iconst(Ty::Bool, 0);
    let cond = fb.icmp(ICmpOp::Eq, Ty::Bool, eq, f);
    fb.condbr(cond, ok, vec![], panic, vec![]);
    fb.switch_to_block(ok);
    fb.ret(vec![]);
    fb.switch_to_block(panic);
    fb.unreachable();
    let func = fb.build();
    let id = mb
        .add_proof_obligation(|id| {
            ProofObligation::new(
                id,
                ObligationKind::BoundsCheck,
                ProofStatus::Pending,
                "size_of != 0",
            )
            .with_site(ObligationSite::new(func, entry, 5))
        })
        .expect("a fresh obligation id");
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");

    let obligation = module
        .proof_obligations
        .iter()
        .find(|o| o.id == id)
        .unwrap()
        .clone();
    assert_eq!(
        derive_site_goal(&module, &obligation),
        Err(GoalDeriveError::GroundGoal)
    );
    let outcomes = attach_bvblast_evidence(&mut module);
    assert!(!outcomes[0].discharged);
    assert!(module.proof_certificates.is_empty());
}

#[test]
fn mul_is_refused_structurally() {
    // Measured: bit-blasting a width-8 multiply goal costs 1,617,446 resolution
    // steps and 1.29 GB of JSON. The bounded exporter now rejects that work, and
    // the narrower TrustIR authority keeps Mul outside its goal language too:
    // an expensive operation cannot become eligible through a later cap bump.
    let mut mb = ModuleBuilder::new("mul");
    let ft = mb.add_func_type(vec![Ty::U64], vec![]);
    let mut fb = mb.function("mul", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    let ok = fb.create_block();
    let panic = fb.create_block();
    fb.switch_to_block(entry);
    let two = fb.iconst(Ty::U64, 2);
    let doubled = fb.binop(BinOp::Mul, Ty::U64, x, two);
    let bound = fb.iconst(Ty::U64, 8);
    let cond = fb.icmp(ICmpOp::Ult, Ty::U64, doubled, bound);
    fb.condbr(cond, ok, vec![], panic, vec![]);
    fb.switch_to_block(ok);
    fb.ret(vec![]);
    fb.switch_to_block(panic);
    fb.unreachable();
    let func = fb.build();
    let id = mb
        .add_proof_obligation(|id| {
            ProofObligation::new(
                id,
                ObligationKind::ArithmeticSafety,
                ProofStatus::Pending,
                "scaled index",
            )
            .with_site(ObligationSite::new(func, entry, 4))
        })
        .expect("a fresh obligation id");
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let obligation = module
        .proof_obligations
        .iter()
        .find(|o| o.id == id)
        .unwrap();
    let err = derive_site_goal(&module, obligation).unwrap_err();
    assert!(
        matches!(&err, GoalDeriveError::Unsupported { detail } if detail.contains("BinOp::Mul")),
        "expected a structural Mul refusal, got {err:?}"
    );
}

#[test]
fn division_and_float_are_refused() {
    for op in [BinOp::UDiv, BinOp::SDiv, BinOp::URem, BinOp::FAdd] {
        let mut mb = ModuleBuilder::new("op");
        let ft = mb.add_func_type(vec![Ty::U64], vec![]);
        let mut fb = mb.function("op", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        let ok = fb.create_block();
        let panic = fb.create_block();
        fb.switch_to_block(entry);
        let k = fb.iconst(Ty::U64, 3);
        let result = fb.binop(op, Ty::U64, x, k);
        let bound = fb.iconst(Ty::U64, 8);
        let cond = fb.icmp(ICmpOp::Ult, Ty::U64, result, bound);
        fb.condbr(cond, ok, vec![], panic, vec![]);
        fb.switch_to_block(ok);
        fb.ret(vec![]);
        fb.switch_to_block(panic);
        fb.unreachable();
        let func = fb.build();
        let id = mb
            .add_proof_obligation(|id| {
                ProofObligation::new(
                    id,
                    ObligationKind::ArithmeticSafety,
                    ProofStatus::Pending,
                    "op",
                )
                .with_site(ObligationSite::new(func, entry, 4))
            })
            .expect("a fresh obligation id");
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let obligation = module
            .proof_obligations
            .iter()
            .find(|o| o.id == id)
            .unwrap();
        assert!(
            matches!(
                derive_site_goal(&module, obligation),
                Err(GoalDeriveError::Unsupported { .. })
            ),
            "{op:?} should be outside the fragment"
        );
    }
}

// ============================================================================
// Site / polarity fail-closed matrix (E1-E5)
// ============================================================================

#[test]
fn site_and_polarity_refusals() {
    // E1 missing site.
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    let row = fixture
        .module
        .proof_obligations
        .iter_mut()
        .find(|o| o.id == fixture.obligation)
        .unwrap();
    row.site = None;
    let obligation = row.clone();
    assert_eq!(
        derive_site_goal(&fixture.module, &obligation),
        Err(GoalDeriveError::NoSite)
    );

    // E2 site index out of range.
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    let row = fixture
        .module
        .proof_obligations
        .iter_mut()
        .find(|o| o.id == fixture.obligation)
        .unwrap();
    row.site = Some(ObligationSite::new(FuncId::new(0), BlockId::new(0), 99));
    let obligation = row.clone();
    assert!(matches!(
        derive_site_goal(&fixture.module, &obligation),
        Err(GoalDeriveError::SiteNotResolvable { .. })
    ));

    // E3 site node is not a CondBr.
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    let row = fixture
        .module
        .proof_obligations
        .iter_mut()
        .find(|o| o.id == fixture.obligation)
        .unwrap();
    row.site = Some(ObligationSite::new(FuncId::new(0), BlockId::new(0), 0));
    let obligation = row.clone();
    assert!(matches!(
        derive_site_goal(&fixture.module, &obligation),
        Err(GoalDeriveError::NotALoweredAssert { .. })
    ));

    // E4 neither successor diverges: ordinary control flow, not an assert.
    let mut mb = ModuleBuilder::new("plain_branch");
    let ft = mb.add_func_type(vec![Ty::U64], vec![]);
    let mut fb = mb.function("plain_branch", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    let a = fb.create_block();
    let b = fb.create_block();
    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    let cond = fb.icmp(ICmpOp::Ult, Ty::U64, x, zero);
    fb.condbr(cond, a, vec![], b, vec![]);
    fb.switch_to_block(a);
    fb.ret(vec![]);
    fb.switch_to_block(b);
    fb.ret(vec![]);
    let func = fb.build();
    let id = mb
        .add_proof_obligation(|id| {
            ProofObligation::new(
                id,
                ObligationKind::BoundsCheck,
                ProofStatus::Pending,
                "not an assert",
            )
            .with_site(ObligationSite::new(func, entry, 2))
        })
        .expect("a fresh obligation id");
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let obligation = module
        .proof_obligations
        .iter()
        .find(|o| o.id == id)
        .unwrap();
    let err = derive_site_goal(&module, obligation).unwrap_err();
    assert!(
        matches!(&err, GoalDeriveError::NotALoweredAssert { detail } if detail.contains("neither successor")),
        "got {err:?}"
    );
}

#[test]
fn a_cross_block_value_is_not_derivable() {
    // The corpus's dominant blocker (149 of 385): the condition reads a value
    // the block's pure prefix does not define.
    let mut mb = ModuleBuilder::new("cross_block");
    let ft = mb.add_func_type(vec![Ty::U64], vec![]);
    let mut fb = mb.function("cross_block", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    let check = fb.create_block();
    let ok = fb.create_block();
    let panic = fb.create_block();

    fb.switch_to_block(entry);
    let bound = fb.iconst(Ty::U64, 16);
    let cond = fb.icmp(ICmpOp::Ult, Ty::U64, x, bound);
    fb.br(check, vec![]);

    fb.switch_to_block(check);
    // `cond` is defined in `entry`, not here.
    fb.condbr(cond, ok, vec![], panic, vec![]);
    fb.switch_to_block(ok);
    fb.ret(vec![]);
    fb.switch_to_block(panic);
    fb.unreachable();

    let func = fb.build();
    let id = mb
        .add_proof_obligation(|id| {
            ProofObligation::new(
                id,
                ObligationKind::BoundsCheck,
                ProofStatus::Pending,
                "cross-block",
            )
            .with_site(ObligationSite::new(func, check, 0))
        })
        .expect("a fresh obligation id");
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let obligation = module
        .proof_obligations
        .iter()
        .find(|o| o.id == id)
        .unwrap();
    assert!(matches!(
        derive_site_goal(&module, obligation),
        Err(GoalDeriveError::ConditionNotPure { .. })
    ));
}

// ============================================================================
// Kind allowlist
// ============================================================================

#[test]
fn memory_safety_is_not_admitted_even_when_it_would_prove() {
    // The kind gate is deliberately narrow: a bit-vector proof that a CondBr
    // condition holds does not establish a borrow-check obligation. Build a
    // MemorySafety row over a condition that IS provable and confirm no
    // evidence is attached.
    let mut fixture = build_mask_bound(15, 16, ObligationKind::MemorySafety);
    let outcomes = attach_bvblast_evidence(&mut fixture.module);
    assert!(outcomes.is_empty(), "{outcomes:?}");
    assert!(fixture.module.proof_certificates.is_empty());
    assert_eq!(
        fixture
            .module
            .proof_obligations
            .iter()
            .find(|o| o.id == fixture.obligation)
            .unwrap()
            .status,
        ProofStatus::Pending
    );
}

#[test]
fn an_out_of_allowlist_kind_is_refused_by_the_capability_too() {
    // Producer-side refusal is not enough: a hand-authored module could carry a
    // MemorySafety row with a genuine certificate. The capability must refuse it
    // independently.
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    discharge(&mut fixture);
    for row in &mut fixture.module.proof_obligations {
        if row.id == fixture.obligation {
            row.kind = ObligationKind::MemorySafety;
        }
    }
    assert!(!accepts(&fixture.module));
}

// ============================================================================
// Sharp boundary + anti-vacuity, the falsifiers for the trusted residual
// (that ay's blaster wires the correct gate topology per node)
// ============================================================================

#[test]
fn sharp_boundary_matrix() {
    // At each width, `(x & mask) <u mask+1` is TRUE and `(x & mask) <u mask` is
    // FALSE. If the blaster's gate topology were wrong in a way that made
    // everything provable, the FALSE column would prove too.
    let cases: [(u32, u128); 4] = [
        (8, u128::from(u8::MAX)),
        (32, u128::from(u32::MAX)),
        (64, u128::from(u64::MAX)),
        (128, u128::MAX),
    ];
    let mut proved = 0;
    let mut refused = 0;
    for (width, mask) in cases {
        let masked = BvTerm::And(
            Box::new(BvTerm::leaf("x", width)),
            Box::new(BvTerm::Const { value: mask, width }),
        );
        // TRUE: `(x & MAX) <u 2^(w-1)` is false; use the exact boundary instead.
        // `(x & (2^(w-1) - 1)) <u 2^(w-1)` is TRUE; at bound 2^(w-1) - 1 it is FALSE.
        let half = if width == 128 {
            1u128 << 127
        } else {
            1u128 << (width - 1)
        };
        let low_mask = half - 1;
        let masked_low = BvTerm::And(
            Box::new(BvTerm::leaf("x", width)),
            Box::new(BvTerm::Const {
                value: low_mask,
                width,
            }),
        );
        let _ = masked;

        let true_goal = BvGoal::predicate(BvTerm::Not(Box::new(BvTerm::CarryOut {
            lhs: Box::new(masked_low.clone()),
            rhs: Box::new(BvTerm::Const { value: half, width }),
            is_sub: true,
        })));
        assert!(
            prove(&true_goal).is_ok(),
            "width {width}: (x & 2^{}-1) <u 2^{} must PROVE",
            width - 1,
            width - 1
        );
        proved += 1;

        let false_goal = BvGoal::predicate(BvTerm::Not(Box::new(BvTerm::CarryOut {
            lhs: Box::new(masked_low),
            rhs: Box::new(BvTerm::Const {
                value: low_mask,
                width,
            }),
            is_sub: true,
        })));
        assert_eq!(
            prove(&false_goal),
            Err(ProveError::NoRefutation),
            "width {width}: the one-off-lower bound must be REFUSED"
        );
        refused += 1;
    }
    assert_eq!((proved, refused), (4, 4), "sharp-boundary matrix: 8/8");
}

#[test]
fn incompleteness_is_never_reported_as_falsity() {
    // `NoRefutation` (the obligation is false) and `Incomplete` (the prover gave
    // up) are distinct variants and must stay distinct: conflating them would
    // let "the solver timed out" print as "the program is wrong".
    let false_goal = BvGoal::predicate(BvTerm::Eq(
        Box::new(BvTerm::leaf("x", 8)),
        Box::new(BvTerm::leaf("y", 8)),
    ));
    assert_eq!(prove(&false_goal), Err(ProveError::NoRefutation));

    let ground = BvGoal::predicate(BvTerm::Eq(
        Box::new(BvTerm::Const { value: 3, width: 8 }),
        Box::new(BvTerm::Const { value: 3, width: 8 }),
    ));
    assert_eq!(prove(&ground), Err(ProveError::GroundGoal));
}

#[test]
fn the_implication_shape_proves_and_its_converse_does_not() {
    // `x <u 16  =>  x <u 32` encoded as `Or(Not(hyp), concl) == #b1`.
    let width = 32;
    let lt = |bound: u128| {
        BvTerm::Not(Box::new(BvTerm::CarryOut {
            lhs: Box::new(BvTerm::leaf("x", width)),
            rhs: Box::new(BvTerm::Const {
                value: bound,
                width,
            }),
            is_sub: true,
        }))
    };
    let implies = |hyp: BvTerm, concl: BvTerm| {
        BvGoal::predicate(BvTerm::Or(
            Box::new(BvTerm::Not(Box::new(hyp))),
            Box::new(concl),
        ))
    };
    assert!(prove(&implies(lt(16), lt(32))).is_ok());
    assert_eq!(
        prove(&implies(lt(32), lt(16))),
        Err(ProveError::NoRefutation),
        "the converse is false and must be refused"
    );
}

// ============================================================================
// The stored artifact round-trips
// ============================================================================

#[test]
fn the_certificate_payload_round_trips_through_bytes() {
    let goal = BvGoal::predicate(BvTerm::Not(Box::new(BvTerm::CarryOut {
        lhs: Box::new(BvTerm::And(
            Box::new(BvTerm::leaf("v1", 64)),
            Box::new(BvTerm::Const {
                value: 15,
                width: 64,
            }),
        )),
        rhs: Box::new(BvTerm::Const {
            value: 16,
            width: 64,
        }),
        is_sub: true,
    })));
    let proof = prove(&goal).expect("proves");
    let payload = BvBlastCertPayload::new(&goal, proof);
    let bytes = payload.to_bytes().unwrap();
    let decoded = BvBlastCertPayload::from_bytes(&bytes).unwrap();
    assert_eq!(payload, decoded);
    assert!(decoded.proof.validate().is_ok());
}

#[test]
fn the_blaster_is_run_to_run_deterministic() {
    // Gate (10) compares the payload's CNF to a freshly re-derived one, which is
    // only meaningful if the blaster is deterministic. Measured, not assumed.
    let goal = BvGoal::predicate(BvTerm::Not(Box::new(BvTerm::CarryOut {
        lhs: Box::new(BvTerm::And(
            Box::new(BvTerm::leaf("v1", 32)),
            Box::new(BvTerm::Const {
                value: 15,
                width: 32,
            }),
        )),
        rhs: Box::new(BvTerm::Const {
            value: 16,
            width: 32,
        }),
        is_sub: true,
    })));
    let a = prove(&goal).unwrap();
    let b = prove(&goal).unwrap();
    assert_eq!(a.vars, b.vars);
    assert_eq!(a.bit_lemmas, b.bit_lemmas);
    assert_eq!(a.clauses, b.clauses);
}

#[test]
fn the_goal_formula_is_stamped_and_binds() {
    let mut fixture = build_mask_bound(15, 16, ObligationKind::BoundsCheck);
    discharge(&mut fixture);
    let obligation = fixture
        .module
        .proof_obligations
        .iter()
        .find(|o| o.id == fixture.obligation)
        .unwrap();
    let goal = derive_site_goal(&fixture.module, obligation).unwrap();
    let expected =
        bvblast_goal_formula(obligation.site.as_ref().unwrap(), &obligation.kind, &goal).unwrap();
    assert_eq!(obligation.formula.as_ref(), Some(&expected));
}

// ============================================================================
// Authority is not a shared currency (regression)
// ============================================================================

/// A bv-blast-proved obligation grants its OWN `Discharged` status and nothing
/// else. It must never become backing for a `ProofRef` claim.
///
/// REGRESSION. The capability's certificate used to be inserted into the same
/// `BTreeSet` that `validate_proof_refs_with_authority` consults. Because
/// `proof_ref_kind_can_back` lets a `BoundsCheck` obligation back every
/// `is_arithmetic_safety()` annotation plus `NoPanic`/`Custom`, one
/// solver-proved bounds check made a `ProofRef`-backed claim validate on ANY
/// node of the same function — measured: `NoOverflow`, `DivNonZero`,
/// `ShiftInRange`, `NoPanic` all accepted, none of them anything the solver
/// proved. Before the capability existed only kernel-rechecked `CleanCic` could
/// enter that set, so this was a widening of a pre-existing mechanism into the
/// first cheap, automatable source of `ProofRef` backing.
#[test]
fn a_bvblast_discharge_does_not_back_an_unrelated_proof_ref() {
    use trust_ir::proof::ProofAnnotation;

    for claim in [
        ProofAnnotation::NoOverflow,
        ProofAnnotation::DivNonZero,
        ProofAnnotation::ShiftInRange,
        ProofAnnotation::NoPanic,
    ] {
        let mut fixture = build_mask_bound(0x0F, 16, ObligationKind::BoundsCheck);
        let _certificate = discharge(&mut fixture);
        assert!(
            accepts(&fixture.module),
            "precondition: the honest discharge itself must validate"
        );

        // Launder: stamp the unrelated claim onto the `and` node (index 1),
        // backed by a ProofRef to the genuinely-proved bounds obligation.
        let node = &mut fixture.module.functions[0].blocks[0].body[1];
        node.proofs.push(claim.clone());
        node.proofs
            .push(ProofAnnotation::ProofRef(fixture.obligation));

        assert!(
            !accepts(&fixture.module),
            "a bv-blast discharge must not back an unrelated {claim:?} claim, but the \
             module validated clean: {}",
            rejection(&fixture.module)
        );
    }
}
