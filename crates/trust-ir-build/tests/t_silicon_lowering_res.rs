// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! T-SILICON ROUTE-1 CNF-ASSURANCE MILESTONE: the i8 ALU lowering-rule
//! FAMILY's SAT refutations replay through the verified resolution checker,
//! with gate-level ENCODING-FIDELITY provenance validated and carried in each
//! artifact. These remain `Pending`: the validator does not independently
//! derive the exact semantic miter, so CNF UNSAT cannot certify lowering.
//!
//! Fixture provenance (`tests/fixtures/t_silicon/`):
//!
//! * `<rule>_miter.{cnf,trace,prov}` for `rule ∈ {iadd,isub,neg,band,bor,bxor}_i8`
//!   — produced IN-TREE by trust-cg's live pipeline
//!   (`trust-cg-verify/tests/t_silicon_sat_export.rs`): `sat_blast` miter →
//!   MicroSAT `--proof` DRAT → vendored drat-trim `s VERIFIED` + `-r` TraceCheck
//!   trace, plus the `satprov1` gate-level clause provenance. Byte-identical
//!   copies are pinned on the trust-cg side; drift between the repos fails the
//!   pins.
//! * `adder_miter.{cnf,trace}` — the 2026-07-04 feasibility scout's 8-bit
//!   adder-equivalence miter (311 clauses / 107 vars, 141 RUP lemmas → 708
//!   binary steps), kept as the converter's golden fixture.
//!
//! The chain exercised here, per rule: fixture (cnf, trace) →
//! `satcert::trace_to_steps` (UNTRUSTED converter) → `SatResolutionCertPayload`;
//! `satprov` provenance parsed + VALIDATED against the payload's clause list
//! (gate-level fidelity) + carried in the cert context → CleanCic certificate →
//! `validate_module` → the `ck0` kernel reduces
//! `Clean.Res.checkRefutes3 (initialTrie cs) (listLen cs) steps` over the
//! payload. A producer-forced `Certified` status is rejected even when replay
//! succeeds; tamper/negative tests confirm every rejection lane is fail-closed.

use trust_ir::Module;
use trust_ir::proof::satprov::MiterProvenance;
use trust_ir::proof::satres::{
    SATRES_CERT_UNSAT_THEOREM, SatResolutionCertPayload, clauses_digest,
};
use trust_ir::proof::{
    CleanCicKernelRecheck, KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE, ObligationKind, ProofDigest,
    ProofEvidence, ProofStatus, clean_cic_lineage_digest,
};
use trust_ir::value::ProofId;
use trust_ir_build::satcert::{
    LoweringResolutionCert, SatCertError, build_lowering_resolution_cert, parse_dimacs,
    trace_to_steps, verify_steps,
};
use trust_ir_build::{ValidationError, validate_module};

/// The i8 ALU family whose lowering VCs trust-cg exports as fixtures.
const ALU_FAMILY: &[&str] = &[
    "iadd_i8", "isub_i8", "neg_i8", "band_i8", "bor_i8", "bxor_i8",
];

const IADD_RULE: &str = "Iadd_I8 -> ADD (8-bit)";

fn fixture(name: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/t_silicon")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

/// Parse a rule's miter CNF and convert its drat-trim trace into a payload.
fn payload_for(key: &str) -> SatResolutionCertPayload {
    let clauses = parse_dimacs(&fixture(&format!("{key}_miter.cnf")))
        .unwrap_or_else(|e| panic!("parse {key} cnf: {e:?}"));
    let steps = trace_to_steps(&clauses, &fixture(&format!("{key}_miter.trace")))
        .unwrap_or_else(|e| panic!("convert {key} trace: {e:?}"));
    SatResolutionCertPayload { clauses, steps }
}

/// Parse a rule's gate-level provenance fixture.
fn provenance_for(key: &str) -> MiterProvenance {
    MiterProvenance::parse(&fixture(&format!("{key}_miter.prov")))
        .unwrap_or_else(|e| panic!("parse {key} prov: {e}"))
}

fn iadd_payload() -> SatResolutionCertPayload {
    payload_for("iadd_i8")
}

/// Simulate a malicious/legacy producer upgrading a non-authoritative CNF
/// assurance artifact to an authority claim. The validator must reject it.
fn force_certified(mut cert: LoweringResolutionCert) -> LoweringResolutionCert {
    cert.obligation.status = ProofStatus::Certified;
    cert
}

/// Kernel-driving tests run on a generous stack: the debug-mode reflection
/// reduction recurses far deeper than libtest's default thread stack (mirrors
/// the clean-kernel / validate.rs test convention).
fn run_on_large_stack(f: fn()) {
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large-stack test thread");
    if let Err(e) = handle.join() {
        std::panic::resume_unwind(e);
    }
}

// ───────────────────────── converter: golden pin + tamper ─────────────────────────

/// GOLDEN PIN on the scout's adder fixture: the Rust converter reproduces the
/// executed-feasibility numbers exactly (311 originals, 141 RUP lemmas → 708
/// binary steps) and the full payload is byte-pinned by digest, so any silent
/// converter behavior change fails here first.
#[test]
fn adder_fixture_converts_with_golden_pin() {
    let clauses = parse_dimacs(&fixture("adder_miter.cnf")).expect("parse adder cnf");
    assert_eq!(clauses.len(), 311, "adder miter clause count");

    let steps = trace_to_steps(&clauses, &fixture("adder_miter.trace")).expect("convert");
    assert_eq!(steps.len(), 708, "expanded binary step count (scout: 708)");
    assert!(
        steps.last().is_some_and(|s| s.resolvent.is_empty()),
        "chain must end in the empty clause"
    );

    let payload = SatResolutionCertPayload { clauses, steps };
    let digest = ProofDigest::trust_ir_stable("t-silicon.test.golden.v1", &payload.to_bytes());
    assert_eq!(
        digest.to_string(),
        GOLDEN_ADDER_PAYLOAD_DIGEST,
        "adder payload drifted; if the converter change is intentional, re-pin"
    );
}

/// Pinned by running the converter over the committed scout fixture (see
/// `adder_fixture_converts_with_golden_pin`).
const GOLDEN_ADDER_PAYLOAD_DIGEST: &str =
    "trust_ir-stable-v1:a080c7dacc052ccb6fb627c31148d4afcaae0c478eeac6b0136a6328a3aad66a";

/// The scout's tampered-chain negative, both flavors: a dropped resolvent
/// literal and a flipped polarity are rejected by the producer-side replay
/// (and would reduce to `Bool.false` in the kernel — see the kernel-side
/// negative below).
#[test]
fn tampered_chains_are_rejected_by_replay() {
    let payload = iadd_payload();
    assert!(verify_steps(&payload.clauses, &payload.steps).is_ok());

    // (a) Drop a literal from a mid-chain resolvent (the scout's tamper).
    let mut dropped = payload.clone();
    let mid = dropped.steps.len() / 2;
    let victim = dropped.steps[mid..]
        .iter()
        .position(|s| !s.resolvent.is_empty())
        .map(|o| mid + o)
        .expect("a non-empty resolvent exists");
    dropped.steps[victim].resolvent.pop();
    assert!(
        matches!(
            verify_steps(&dropped.clauses, &dropped.steps),
            Err(SatCertError::ReplayRejected { .. })
        ),
        "dropped-literal chain must be rejected"
    );

    // (b) Flip a literal polarity.
    let mut flipped = payload;
    flipped.steps[victim].resolvent[0].1 = !flipped.steps[victim].resolvent[0].1;
    assert!(
        matches!(
            verify_steps(&flipped.clauses, &flipped.steps),
            Err(SatCertError::ReplayRejected { .. })
        ),
        "flipped-literal chain must be rejected"
    );
}

/// A trace whose "original clause" section disagrees with the CNF is refused
/// outright — the converter never silently re-derives from foreign clauses.
#[test]
fn trace_cnf_mismatch_is_rejected() {
    let mut clauses = parse_dimacs(&fixture("iadd_i8_miter.cnf")).expect("parse cnf");
    clauses[0][0].1 = !clauses[0][0].1; // CNF no longer matches the trace
    assert!(
        matches!(
            trace_to_steps(&clauses, &fixture("iadd_i8_miter.trace")),
            Err(SatCertError::TraceCnfMismatch { .. })
        ),
        "trace/CNF mismatch must be rejected"
    );
}

// ─────────────── encoding-fidelity provenance: validate + carry + tamper ───────────────

/// Every rule's gate-level provenance VALIDATES against its own clause list:
/// the payload CNF is exactly `⋃ gate-CNFs ∪ {disequality}` with the two sides
/// compared bit-for-bit. This is the gate-level encoding-fidelity check, run
/// from the committed artifacts (reproducible by any reviewer).
#[test]
fn family_provenance_validates_against_clause_lists() {
    for &key in ALU_FAMILY {
        let payload = payload_for(key);
        let prov = provenance_for(key);
        prov.validate(&payload.clauses)
            .unwrap_or_else(|e| panic!("{key} provenance must validate against its CNF: {e}"));
        assert_eq!(prov.width, 8, "{key} width");
    }
}

/// A corrupted provenance (a dropped gate) fails validation AND makes
/// `build_lowering_resolution_cert` refuse to assemble a cert (fail-closed): a
/// cert never ships whose carried provenance lies about its clause list.
#[test]
fn tampered_provenance_is_rejected_at_cert_build() {
    let payload = iadd_payload();
    let mut prov = provenance_for("iadd_i8");
    // Drop a non-diff gate: the payload now has clauses the provenance can no
    // longer account for.
    let victim = prov
        .gates
        .iter()
        .position(|g| g.side != trust_ir::proof::satprov::MiterSide::Diff)
        .expect("a non-diff gate exists");
    prov.gates.remove(victim);

    assert!(
        prov.validate(&payload.clauses).is_err(),
        "a dropped-gate provenance must fail validation"
    );
    assert!(
        build_lowering_resolution_cert(ProofId::new(0), None, IADD_RULE, &payload, Some(&prov))
            .is_none(),
        "cert build must refuse a provenance that does not match the clause list"
    );
}

/// A provenance that validates but names the WRONG rule is refused by the
/// rule-name gate in `build_lowering_resolution_cert`.
#[test]
fn wrong_rule_provenance_is_rejected_at_cert_build() {
    let payload = payload_for("band_i8");
    let prov = provenance_for("band_i8");
    // Ask to build for iadd's name while carrying band's (valid) provenance.
    assert!(
        build_lowering_resolution_cert(ProofId::new(0), None, IADD_RULE, &payload, Some(&prov))
            .is_none(),
        "cert build must refuse a provenance whose rule name != the obligation rule"
    );
}

// ────────────────────────── E2E: Pending CNF assurance ──────────────────────────

/// Each ALU artifact remains `Pending`, while its resolution chain and carried
/// gate provenance are independently checkable. This is deliberately not a
/// translation-validation success test: replay establishes only CNF UNSAT.
#[test]
fn alu_family_lowering_certs_remain_pending_cnf_assurance() {
    for &key in ALU_FAMILY {
        let payload = payload_for(key);
        verify_steps(&payload.clauses, &payload.steps)
            .unwrap_or_else(|e| panic!("{key} resolution replay must pass: {e:?}"));
        let prov = provenance_for(key);
        let rule_name = prov.rule_name.clone();
        let cert = build_lowering_resolution_cert(
            ProofId::new(0),
            None,
            &rule_name,
            &payload,
            Some(&prov),
        )
        .unwrap_or_else(|| panic!("assemble {key} cert (with validated provenance)"));
        assert_eq!(cert.obligation.kind, ObligationKind::TranslationValidation);
        assert_eq!(cert.obligation.status, ProofStatus::Pending);

        // The gate-level provenance is CARRIED in the cert context (digest +
        // satprov1 text), so the fidelity boundary is auditable at the artifact.
        let ProofEvidence::CleanCic { context, .. } = &cert.certificate.evidence else {
            panic!("{key} evidence must be CleanCic");
        };
        let ctx = String::from_utf8_lossy(context);
        assert!(
            ctx.contains("satprov-digest:") && ctx.contains("gate-level CHECKED"),
            "{key} cert context must carry the validated provenance"
        );
    }
}

/// Root regression: even a valid refutation of the trivial contradictory CNF
/// cannot mint `Certified`, because a producer can choose that CNF for any
/// unrelated lowering claim.
#[test]
fn producer_selected_unsat_cnf_cannot_mint_certified() {
    run_on_large_stack(producer_selected_unsat_cnf_cannot_mint_certified_body);
}
fn producer_selected_unsat_cnf_cannot_mint_certified_body() {
    let payload = SatResolutionCertPayload {
        clauses: vec![vec![(0, false)], vec![(0, true)]],
        steps: vec![trust_ir::proof::satres::SatResolutionStep {
            resolvent: vec![],
            prem1: 0,
            prem2: 1,
            pivot_var: 0,
        }],
    };
    let cert = force_certified(
        build_lowering_resolution_cert(ProofId::new(0), None, IADD_RULE, &payload, None)
            .expect("assemble assurance artifact"),
    );
    let mut m = Module::new("producer-selected-unsat-cnf");
    m.proof_obligations.push(cert.obligation);
    m.proof_certificates.push(cert.certificate);

    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("producer-selected clause list")
                    && reason.contains("cannot mint Certified")
        )),
        "valid CNF replay must still reject an unbound Certified claim, got: {errs:?}"
    );
}

/// THE MILESTONE, tamper-negative: flip one resolvent literal mid-chain
/// (clause list — and hence the formula digest binding — untouched) and the
/// KERNEL rejects: `checkRefutes3` reduces to `Bool.false`, registration of
/// the ground theorem fails, and the obligation is refused. The rejection is
/// the kernel's judgment, not any producer-side string/digest check.
#[test]
fn tampered_step_chain_is_rejected_by_kernel() {
    run_on_large_stack(tampered_step_chain_is_rejected_by_kernel_body);
}
fn tampered_step_chain_is_rejected_by_kernel_body() {
    let mut payload = iadd_payload();
    let mid = payload.steps.len() / 2;
    let victim = payload.steps[mid..]
        .iter()
        .position(|s| !s.resolvent.is_empty())
        .map(|o| mid + o)
        .expect("non-empty resolvent");
    payload.steps[victim].resolvent[0].1 = !payload.steps[victim].resolvent[0].1;

    // Build with provenance None: the tampered payload's clause list is
    // unchanged, so provenance would still validate — this test isolates the
    // KERNEL rejection of the step chain.
    let cert = force_certified(
        build_lowering_resolution_cert(ProofId::new(0), None, IADD_RULE, &payload, None)
            .expect("assemble tampered cert"),
    );
    let mut m = Module::new("t-silicon-iadd-i8-tampered");
    m.proof_obligations.push(cert.obligation);
    m.proof_certificates.push(cert.certificate);

    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("did not reduce to Bool.true")
        )),
        "a tampered resolution chain must be REJECTED by the kernel reflection, got: {errs:?}"
    );
}

// ───────────────────────── fail-closed rejection lanes ─────────────────────────

/// kind→anchor guard, direction 1: a TranslationValidation obligation citing
/// a CROSS-DOMAIN anchor (the true-but-unrelated constructive Farkas anchor)
/// is rejected before any kernel work.
#[test]
fn translation_validation_citing_cross_domain_anchor_is_rejected() {
    let payload = iadd_payload();
    let prov = provenance_for("iadd_i8");
    let mut cert = force_certified(
        build_lowering_resolution_cert(ProofId::new(0), None, IADD_RULE, &payload, Some(&prov))
            .expect("assemble cert"),
    );
    let ProofEvidence::CleanCic { kernel_recheck, .. } = &mut cert.certificate.evidence else {
        unreachable!()
    };
    *kernel_recheck = Some(CleanCicKernelRecheck {
        module: "Crownproof.SlackCertZ".to_string(),
        theorems: vec!["NNVerify.farkas_combine_2_le_bound".to_string()],
        anchor: KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE.to_string(),
        allowed_axioms: vec![],
        binding: None,
    });

    let mut m = Module::new("cross-domain-anchor");
    m.proof_obligations.push(cert.obligation);
    m.proof_certificates.push(cert.certificate);
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("law-library theorem")
                    && reason.contains("cannot mint Certified")
        )),
        "cross-domain anchor must be rejected by the kind→anchor guard, got: {errs:?}"
    );
}

/// kind→anchor guard, direction 2: a NON-TranslationValidation obligation may
/// not borrow the lowering-resolution anchor.
#[test]
fn non_translation_validation_kind_cannot_borrow_the_lowering_anchor() {
    let payload = iadd_payload();
    let prov = provenance_for("iadd_i8");
    let cert = force_certified(
        build_lowering_resolution_cert(ProofId::new(0), None, IADD_RULE, &payload, Some(&prov))
            .expect("assemble cert"),
    );
    let mut oblig = cert.obligation;
    oblig.kind = ObligationKind::Postcondition;
    // Re-bind the lineage so ONLY the kind→anchor guard is under test.
    let lineage = clean_cic_lineage_digest(&oblig);
    let mut certificate = cert.certificate;
    let ProofEvidence::CleanCic {
        lineage: cert_lineage,
        ..
    } = &mut certificate.evidence
    else {
        unreachable!()
    };
    *cert_lineage = lineage;

    let mut m = Module::new("kind-borrow");
    m.proof_obligations.push(oblig);
    m.proof_certificates.push(certificate);
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("non-authoritative CNF assurance")
                    && reason.contains("TranslationValidation")
        )),
        "a Postcondition obligation citing the lowering anchor must be rejected, got: {errs:?}"
    );
}

/// Claim-binding: a certificate whose payload refutes a DIFFERENT clause list
/// than the one the obligation's formula pins is rejected by the digest gate
/// (a refutation of an easier CNF cannot discharge this obligation).
#[test]
fn clause_list_digest_mismatch_is_rejected() {
    let payload = iadd_payload();
    let prov = provenance_for("iadd_i8");
    let cert = force_certified(
        build_lowering_resolution_cert(ProofId::new(0), None, IADD_RULE, &payload, Some(&prov))
            .expect("assemble cert"),
    );

    // Swap in a payload refuting the trivial CNF {x, ¬x} — genuinely UNSAT,
    // trivially "provable", but NOT the pinned clause list.
    let easy = SatResolutionCertPayload {
        clauses: vec![vec![(0, false)], vec![(0, true)]],
        steps: vec![trust_ir::proof::satres::SatResolutionStep {
            resolvent: vec![],
            prem1: 0,
            prem2: 1,
            pivot_var: 0,
        }],
    };
    assert_ne!(
        clauses_digest(&easy.clauses),
        clauses_digest(&payload.clauses)
    );
    let mut certificate = cert.certificate;
    let ProofEvidence::CleanCic { term, .. } = &mut certificate.evidence else {
        unreachable!()
    };
    *term = easy.to_bytes();

    let mut m = Module::new("digest-mismatch");
    m.proof_obligations.push(cert.obligation);
    m.proof_certificates.push(certificate);
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("digest mismatch")
        )),
        "an easier-CNF payload must be rejected by the clause-list digest gate, got: {errs:?}"
    );
}

/// Citation policy: the directive must cite EXACTLY the ground theorem — a
/// padded citation set (even of true kernel theorems) is rejected.
#[test]
fn padded_theorem_citation_is_rejected() {
    let payload = iadd_payload();
    let prov = provenance_for("iadd_i8");
    let cert = force_certified(
        build_lowering_resolution_cert(ProofId::new(0), None, IADD_RULE, &payload, Some(&prov))
            .expect("assemble cert"),
    );
    let mut certificate = cert.certificate;
    let ProofEvidence::CleanCic { kernel_recheck, .. } = &mut certificate.evidence else {
        unreachable!()
    };
    kernel_recheck
        .as_mut()
        .expect("directive present")
        .theorems
        .push("Clean.Res.checkRefutes3_sound".to_string());

    let mut m = Module::new("padded-citation");
    m.proof_obligations.push(cert.obligation);
    m.proof_certificates.push(certificate);
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("must cite exactly") && reason.contains(SATRES_CERT_UNSAT_THEOREM)
        )),
        "padded citations must be rejected, got: {errs:?}"
    );
}

/// Formula policy: a lowering-resolution obligation with NO formula (no
/// pinned clause list) cannot certify.
#[test]
fn missing_formula_is_rejected() {
    let payload = iadd_payload();
    let prov = provenance_for("iadd_i8");
    let cert = force_certified(
        build_lowering_resolution_cert(ProofId::new(0), None, IADD_RULE, &payload, Some(&prov))
            .expect("assemble cert"),
    );
    let mut oblig = cert.obligation;
    oblig.formula = None;
    let lineage = clean_cic_lineage_digest(&oblig);
    let mut certificate = cert.certificate;
    let ProofEvidence::CleanCic {
        lineage: cert_lineage,
        ..
    } = &mut certificate.evidence
    else {
        unreachable!()
    };
    *cert_lineage = lineage;

    let mut m = Module::new("no-formula");
    m.proof_obligations.push(oblig);
    m.proof_certificates.push(certificate);
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("no formula")
        )),
        "a formula-less lowering obligation must be rejected, got: {errs:?}"
    );
}
