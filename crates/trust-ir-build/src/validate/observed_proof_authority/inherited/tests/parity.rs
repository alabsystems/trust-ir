// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_actual_inherited_oracle_matches_all_three_original_policies() {
    let m = fixture();
    let a = input(&m);
    let auth = authenticated(&m, Some(SiteOutcome::Authenticated));
    for p in [
        ImportPolicy::Structural,
        ImportPolicy::Refuse,
        ImportPolicy::Authenticated(&auth),
    ] {
        run(&a, p);
    }
}
#[test]
fn malformed_external_reference_emits_each_independent_dangling_error_then_policy_error() {
    let mut m = fixture();
    if let ProofEvidence::InheritedFromCallee {
        external: Some(r), ..
    } = &mut m.proof_certificates[2].evidence
    {
        r.module = ImportId::new(u32::MAX);
        r.obligation = None;
    }
    let a = input(&m);
    let auth = authenticated(&m, None);
    for p in [
        ImportPolicy::Structural,
        ImportPolicy::Refuse,
        ImportPolicy::Authenticated(&auth),
    ] {
        run(&a, p);
    }
}
#[test]
fn sealed_authenticated_reported_refused_and_unexamined_outcomes_keep_exact_details() {
    let m = fixture();
    let a = input(&m);
    for state in [
        Some(SiteOutcome::Authenticated),
        Some(SiteOutcome::Reported),
        Some(SiteOutcome::Refused(
            "whole retained detailé🦀\0".repeat(130),
        )),
        None,
    ] {
        let auth = authenticated(&m, state);
        run(&a, ImportPolicy::Authenticated(&auth));
    }
}
#[test]
fn changed_full_certificate_selector_does_not_reuse_same_id_authenticated_row() {
    let m = fixture();
    let mut changed = m.proof_certificates[2].clone();
    changed.prover.push('x');
    let auth = AuthenticatedImports::inherited_fixture_for_observed_tests(vec![(
        changed,
        SiteOutcome::Authenticated,
    )]);
    run(&input(&m), ImportPolicy::Authenticated(&auth));
}
#[test]
fn local_missing_callee_ground_and_last_scoped_owner_diagnostics_keep_exact_order() {
    let mut m = fixture();
    m.functions.clear();
    m.proof_obligations[0].function = Some(FuncId::new(8));
    m.proof_obligations.push(row(1, ProofStatus::Pending));
    m.proof_obligations.last_mut().unwrap().function = None;
    let mut a = input(&m);
    a.kernel.clear();
    let out = oracle(&a, ImportPolicy::Refuse);
    assert!(matches!(
        out.first(),
        Some(ValidationError::InheritedProofCalleeNotFound { .. })
    ));
    run(&a, ImportPolicy::Refuse);
}
#[test]
fn full_local_restatement_result_and_weakest_coverage_are_reported_after_prior_errors() {
    let m = refused_local();
    run(&input(&m), ImportPolicy::Refuse);
    let mut m = fixture();
    m.proof_certificates[0].assurance = Some(CoverageAssurance {
        bound: CoverageBound::UnwindBounded { depth: 0 },
        request_digest: ProofDigest::sha256([0; 32]),
    });
    m.proof_certificates[1].assurance = Some(CoverageAssurance {
        bound: CoverageBound::Unbounded,
        request_digest: ProofDigest::sha256([0; 32]),
    });
    run(&input(&m), ImportPolicy::Refuse);
}
#[test]
fn exact_debug_symbol_handles_apostrophe_controls_unicode_and_all_source_bytes() {
    let mut m = fixture();
    if let ProofEvidence::InheritedFromCallee {
        external: Some(r), ..
    } = &mut m.proof_certificates[2].evidence
    {
        r.symbol = "'\"\\\n\r\t\0\u{1}\u{1248}é🦀\u{200d}".repeat(150);
    }
    let (base, _) = run(&input(&m), ImportPolicy::Refuse);
    assert!(base.events.iter().any(|e| e.work == 2928));
}
#[test]
fn duplicate_local_and_far_rows_and_pending_certificates_do_not_invent_grounding() {
    for which in [0, 1] {
        let mut m = fixture();
        m.proof_obligations.push(m.proof_obligations[which].clone());
        run(&input(&m), ImportPolicy::Refuse);
    }
    let m = fixture();
    let mut a = input(&m);
    a.discharged = a.kernel.clone();
    a.kernel.clear();
    run(&a, ImportPolicy::Refuse);
}
