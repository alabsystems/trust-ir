// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_original_integrity_output_keeps_all_four_group_orders() {
    let m = fixture();
    let (out, _, _) = run(&m);
    assert_eq!(out.len(), 12);
    assert!(matches!(
        &out[0],
        ValidationError::DuplicateProofObligationId(7)
    ));
    assert!(matches!(
        &out[1],
        ValidationError::UnpinnedCustomObligationNamespace { .. }
    ));
    assert!(
        matches!(&out[2],ValidationError::FormulaTextsDisagree{site:FormulaSite::Obligation(id)}if *id==ProofId::new(7))
    );
    assert!(matches!(
        &out[3],
        ValidationError::InvalidProofObligationSourceTextId {
            field: "source_id",
            ..
        }
    ));
    assert!(matches!(
        &out[9],
        ValidationError::DuplicatePublicObligationId { .. }
    ));
    assert!(matches!(
        &out[10],
        ValidationError::DanglingProofCertificate { obligation: 99 }
    ));
    assert!(matches!(
        &out[11],
        ValidationError::TrustedWithoutJustification { obligation: 9 }
    ));
}
#[test]
fn empty_full_integrity_still_executes_all_children_and_retires_batch_buffers() {
    let m = Module::new("");
    let (out, o, _) = run(&m);
    assert!(out.is_empty());
    assert!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .count()
            > 16
    );
    assert!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Publication)
            .count()
            > 8
    );
}
#[test]
fn actual_header_formula_source_and_tail_children_combine_to_the_same_full_vector() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut combined =
        validate_module_proof_obligation_header_observed(&m, &mut s, site()).unwrap();
    let a = combined.len();
    combined.extend(validate_module_formula_texts_observed(&m, &mut s, site()).unwrap());
    let b = combined.len();
    combined.extend(validate_module_obligation_source_observed(&m, &mut s, site()).unwrap());
    let c = combined.len();
    combined
        .extend(validate_module_certificate_integrity_tail_observed(&m, &mut s, site()).unwrap());
    assert_eq!((a, b, c, combined.len()), (2, 3, 10, 12));
    assert_eq!(combined, run(&m).0);
    retire_validation_errors_observed(combined, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
}
#[test]
fn nested_raw_diagnostics_are_not_truncated_reordered_or_normalized_by_aggregation() {
    let mut m = fixture();
    let namespace = "unadmitted λ\0尾".repeat(1000);
    let name = "full-name 尾\0λ".repeat(900);
    m.proof_obligations[0].kind = ObligationKind::Custom {
        namespace: namespace.clone(),
        name: name.clone(),
    };
    let out = run(&m).0;
    assert!(
        matches!(&out[1],ValidationError::UnpinnedCustomObligationNamespace{namespace:n,name:s,..}if n==&namespace&&s==&name)
    );
}
#[test]
fn bounded_header_swaps_then_pops_preserve_every_nested_row_order() {
    for count in 0..9 {
        let batch: Vec<_> = (0..count).map(|n| error(&n.to_string())).collect();
        let mut state = State {
            batch: batch.clone(),
            errors: vec![error("prior")],
            row: None,
        };
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        state.append(&mut w).unwrap();
        let mut expected = vec![error("prior")];
        expected.extend(batch);
        assert_eq!(state.errors, expected);
        assert_eq!(state.batch.capacity(), 0);
        assert!(state.row.is_none());
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
}
#[test]
fn already_allocated_empty_child_batch_is_retired_before_any_next_child() {
    let mut state = State {
        batch: Vec::with_capacity(9),
        ..State::default()
    };
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        state.before_child(&mut w),
        Err(ObservedValueError::InvalidRange)
    );
    state.append(&mut w).unwrap();
    assert_eq!(state.batch.capacity(), 0);
    state.before_child(&mut w).unwrap();
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
