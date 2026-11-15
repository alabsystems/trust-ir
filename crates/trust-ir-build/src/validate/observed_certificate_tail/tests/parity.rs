// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_eight_evidence_sixteen_kind_five_status_cells_match_original() {
    for evidence in evidence() {
        for kind in kinds() {
            for status in [
                ProofStatus::Pending,
                ProofStatus::Discharged,
                ProofStatus::Failed,
                ProofStatus::Trusted,
                ProofStatus::Certified,
            ] {
                let mut m = Module::new("");
                m.proof_obligations.push(row(7, status, kind.clone()));
                m.proof_certificates.push(cert(7, evidence.clone()));
                run(&m);
            }
        }
    }
}
#[test]
fn exact_original_error_group_and_within_certificate_order_is_preserved() {
    let out = run(&fixture()).0;
    assert_eq!(
        out,
        vec![
            ValidationError::DanglingProofCertificate { obligation: 99 },
            ValidationError::GroundCertificateStatusInconsistent {
                obligation: 7,
                status: "Failed"
            },
            ValidationError::EvidenceKindMismatch {
                obligation: 7,
                kind: "bounds_check",
                evidence: "TranslationValidation"
            },
            ValidationError::TrustedWithoutJustification { obligation: 9 }
        ]
    );
}
#[test]
fn empty_and_only_dangling_certificates_are_reported_in_physical_order() {
    let mut m = Module::new("");
    assert!(run(&m).0.is_empty());
    m.proof_certificates = vec![
        cert(9, ProofEvidence::Trusted(" ".into())),
        cert(2, ProofEvidence::SmtProof(vec![])),
        cert(9, ProofEvidence::LeanProof("".into())),
    ];
    assert_eq!(
        run(&m).0,
        vec![
            ValidationError::DanglingProofCertificate { obligation: 9 },
            ValidationError::DanglingProofCertificate { obligation: 2 },
            ValidationError::DanglingProofCertificate { obligation: 9 }
        ]
    );
}
#[test]
fn duplicate_ids_skip_status_kind_but_not_physical_trusted_attribution() {
    let mut m = Module::new("");
    m.proof_obligations = vec![
        row(7, ProofStatus::Failed, ObligationKind::BoundsCheck),
        row(7, ProofStatus::Trusted, ObligationKind::Precondition),
        row(7, ProofStatus::Trusted, ObligationKind::Postcondition),
    ];
    m.proof_certificates.push(cert(
        7,
        ProofEvidence::TranslationValidation {
            rule_name: "wrong-kind".into(),
            smt_hash: [0; 32],
        },
    ));
    assert_eq!(
        run(&m).0,
        vec![
            ValidationError::TrustedWithoutJustification { obligation: 7 },
            ValidationError::TrustedWithoutJustification { obligation: 7 }
        ]
    );
    m.proof_certificates
        .push(cert(7, ProofEvidence::Trusted("attributed".into())));
    assert!(run(&m).0.is_empty());
}
#[test]
fn inherited_evidence_only_skips_failed_status_not_other_actual_rules() {
    let mut m = Module::new("");
    m.proof_obligations
        .push(row(7, ProofStatus::Failed, ObligationKind::BoundsCheck));
    m.proof_certificates.push(cert(
        7,
        ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(u32::MAX),
            obligation: ProofId::new(u32::MAX),
            external: None,
        },
    ));
    assert!(run(&m).0.is_empty());
    m.proof_certificates
        .push(cert(7, ProofEvidence::Trusted(" ".into())));
    assert_eq!(
        run(&m).0,
        vec![ValidationError::GroundCertificateStatusInconsistent {
            obligation: 7,
            status: "Failed"
        }]
    );
}
#[test]
fn unicode_trim_empty_equivalence_keeps_nonwhite_zero_width_nul_and_tail_content() {
    for text in [
        "",
        " \t\n\r\u{b}\u{c}",
        "\u{85}\u{a0}\u{1680}\u{2000}\u{200a}\u{2028}\u{2029}\u{202f}\u{205f}\u{3000}",
        "\u{200b}",
        "\0",
        " \u{a0}attributed\u{3000}",
        " \t\u{3000}\0",
    ] {
        let mut m = Module::new("");
        m.proof_obligations
            .push(row(7, ProofStatus::Trusted, ObligationKind::Precondition));
        m.proof_certificates
            .push(cert(7, ProofEvidence::Trusted(text.into())));
        assert_eq!(run(&m).0.is_empty(), !text.trim().is_empty());
    }
}
#[test]
fn a_later_nonblank_matching_trusted_row_can_justify_after_blank_wrongid_and_wrongshape() {
    let mut m = Module::new("");
    m.proof_obligations
        .push(row(7, ProofStatus::Trusted, ObligationKind::Precondition));
    m.proof_certificates = vec![
        cert(99, ProofEvidence::Trusted("not for7".into())),
        cert(7, ProofEvidence::LeanProof("not trusted".into())),
        cert(7, ProofEvidence::Trusted("\u{3000}".into())),
        cert(7, ProofEvidence::Trusted("\u{3000}yes".into())),
    ];
    assert!(
        !run(&m)
            .0
            .iter()
            .any(|e| matches!(e, ValidationError::TrustedWithoutJustification { .. }))
    );
    m.proof_certificates.pop();
    assert!(run(&m).0.iter().any(|e| matches!(
        e,
        ValidationError::TrustedWithoutJustification { obligation: 7 }
    )));
}
#[test]
fn shape_only_decisions_do_not_walk_prover_or_nontrusted_evidence_payloads() {
    let mut m = Module::new("");
    m.proof_obligations
        .push(row(7, ProofStatus::Pending, ObligationKind::Precondition));
    m.proof_certificates
        .push(cert(7, ProofEvidence::LeanProof("short".into())));
    let (_, small, _) = run(&m);
    m.proof_certificates[0].prover = "unused λ\0".repeat(10000);
    m.proof_certificates[0].evidence = ProofEvidence::LeanProof("unused 尾\0".repeat(10000));
    let (_, large, _) = run(&m);
    assert_eq!(small.events, large.events);
}
#[test]
fn unique_resolution_uses_all_physical_rows_not_position_or_first_match() {
    let mut m = Module::new("");
    m.proof_obligations = vec![
        row(9, ProofStatus::Pending, ObligationKind::Precondition),
        row(7, ProofStatus::Failed, ObligationKind::BoundsCheck),
        row(10, ProofStatus::Pending, ObligationKind::Precondition),
    ];
    m.proof_certificates.push(cert(
        7,
        ProofEvidence::TranslationValidation {
            rule_name: "ignored".into(),
            smt_hash: [0; 32],
        },
    ));
    assert_eq!(run(&m).0.len(), 2);
    m.proof_obligations.push(row(
        7,
        ProofStatus::Pending,
        ObligationKind::TranslationValidation,
    ));
    assert!(run(&m).0.is_empty());
}
