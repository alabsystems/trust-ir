// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_and_all_fifteen_noncustom_kinds_keep_the_original_no_namespace_boundary() {
    assert!(run(&Module::new("")).0.is_empty());
    let mut m = Module::new("");
    for (id, kind) in [
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::LoopInvariant,
        ObligationKind::TypeInvariant,
        ObligationKind::RefinementType,
        ObligationKind::TranslationValidation,
        ObligationKind::MemorySafety,
        ObligationKind::PanicFreedom,
        ObligationKind::TemporalSafety,
        ObligationKind::Liveness,
        ObligationKind::ArithmeticSafety,
        ObligationKind::BoundsCheck,
        ObligationKind::GiveBackRefinement,
        ObligationKind::Termination,
        ObligationKind::Ownership,
    ]
    .into_iter()
    .enumerate()
    {
        m.proof_obligations.push(row(id as u32, kind));
    }
    assert!(run(&m).0.is_empty());
}
#[test]
fn every_later_duplicate_id_is_reported_once_in_physical_order_including_sparse_extremes() {
    let mut m = Module::new("");
    m.proof_obligations = [7, u32::MAX, 7, 7, u32::MAX]
        .into_iter()
        .map(|id| row(id, ObligationKind::Liveness))
        .collect();
    assert_eq!(
        run(&m).0,
        vec![
            ValidationError::DuplicateProofObligationId(7),
            ValidationError::DuplicateProofObligationId(7),
            ValidationError::DuplicateProofObligationId(u32::MAX)
        ]
    );
}
#[test]
fn every_exact_pinned_namespace_accepts_an_empty_or_unknown_label_without_examining_it() {
    for ns in ADMITTED_OBLIGATION_NAMESPACES {
        for name in ["", "unknown label / λ\0TAIL"] {
            let mut m = Module::new("");
            m.proof_obligations.push(custom(3, ns, name));
            assert!(run(&m).0.is_empty());
        }
    }
}
#[test]
fn case_prefix_padding_embedded_nul_and_unknown_namespaces_remain_raw_distinct_refusals() {
    for ns in [
        "",
        "TRUST.VC",
        "trust.vc.extra",
        "trust.v",
        " trust.vc",
        "trust.vc ",
        "trust.vc\0",
        "unadmittedλ",
    ] {
        let mut m = Module::new("");
        m.proof_obligations
            .push(custom(u32::MAX, ns, "nameλ\0TAIL"));
        assert_eq!(
            run(&m).0,
            vec![ValidationError::UnpinnedCustomObligationNamespace {
                obligation: u32::MAX,
                namespace: ns.into(),
                name: "nameλ\0TAIL".into()
            }]
        );
    }
}
#[test]
fn all_duplicate_diagnostics_precede_namespace_diagnostics_despite_interleaved_rows() {
    let mut m = Module::new("");
    m.proof_obligations = vec![
        custom(7, "badA", "A"),
        custom(7, "badB", "B"),
        custom(9, "trust.vc", "ignored"),
        custom(7, "badC", "C"),
    ];
    let errors = run(&m).0;
    assert_eq!(errors.len(), 5);
    assert_eq!(
        &errors[..2],
        &[
            ValidationError::DuplicateProofObligationId(7),
            ValidationError::DuplicateProofObligationId(7)
        ]
    );
    for (offset, ns, name) in [(2, "badA", "A"), (3, "badB", "B"), (4, "badC", "C")] {
        assert_eq!(
            errors[offset],
            ValidationError::UnpinnedCustomObligationNamespace {
                obligation: 7,
                namespace: ns.into(),
                name: name.into()
            }
        );
    }
}
#[test]
fn repeated_invalid_namespace_rows_each_retain_complete_raw_names_without_deduplicating_them() {
    let ns = "namespaceλ\0TAIL".repeat(500);
    let name = "label尾\0TAIL".repeat(500);
    let mut m = Module::new("");
    m.proof_obligations = vec![custom(4, &ns, &name), custom(5, &ns, &name)];
    let errors = run(&m).0;
    assert_eq!(errors.len(), 2);
    for (error, id) in errors.iter().zip([4, 5]) {
        assert_eq!(
            error,
            &ValidationError::UnpinnedCustomObligationNamespace {
                obligation: id,
                namespace: ns.clone(),
                name: name.clone()
            }
        );
    }
}
#[test]
fn admitted_custom_label_and_other_unread_payloads_do_not_change_observation() {
    let mut a = Module::new("");
    a.proof_obligations.push(custom(3, "trust.vc", "x"));
    let mut b = a.clone();
    b.name = "unread".repeat(100_000);
    b.proof_obligations[0].description = "unread".repeat(100_000);
    b.proof_obligations[0].kind = ObligationKind::Custom {
        namespace: "trust.vc".into(),
        name: "unread".repeat(100_000),
    };
    let (_, left, cut_a) = run(&a);
    let (_, right, cut_b) = run(&b);
    assert_eq!(cut_a, cut_b);
    assert_eq!(left.events, right.events);
}
