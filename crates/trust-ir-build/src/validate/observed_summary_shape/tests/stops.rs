// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_mixed_output_callback_can_refuse_without_publishing_a_shorter_report() {
    let (m, f, summary) = mixed();
    let (_, baseline) = execute(&m, &f, &summary);
    for at in 1..=baseline.events.len() {
        let mut o = Observer {
            at: Some(at),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_function_summary_signature_effect_shape_observed(
                &m,
                &f,
                &summary,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original interior");
    }
}
#[test]
fn output_allocation_refusal_preserves_the_whole_pending_detail_until_consuming_cleanup() {
    let (_, f, _) = fixture();
    let detail = "λ\n'".repeat(10000);
    let mut state = State {
        detail: detail.clone(),
        errors: Vec::new(),
    };
    let mut o = Observer {
        byte_cap: Some(0),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let result = state.issue(&f, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.detail, detail);
    assert_eq!((state.errors.len(), state.errors.capacity()), (0, 0));
    assert_eq!(
        state.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.detail.is_empty() && state.errors.is_empty());
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "bytes");
    drop(s);
    assert!(
        o.events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement && e.work >= detail.len())
    );
}
#[test]
fn pending_detail_and_existing_diagnostic_prefix_are_consumed_after_the_original_failure() {
    let (_, f, _) = fixture();
    let first = "first-λ".repeat(1000);
    let pending = "pending-λ".repeat(1000);
    let next = Rc::new(Cell::new(false));
    let mut state = State {
        detail: pending.clone(),
        errors: vec![ValidationError::InvalidFunctionSummary {
            function: f.id.index(),
            detail: first.clone(),
        }],
    };
    let mut o = Observer {
        next: Some(next.clone()),
        cleanup: true,
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    next.set(true);
    let result = state.issue(&f, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.detail, pending);
    assert_eq!(state.errors.len(), 1);
    assert!(
        matches!(&state.errors[0], ValidationError::InvalidFunctionSummary { function, detail } if *function == f.id.index() && detail == &first)
    );
    assert_eq!(
        state.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.detail.is_empty() && state.errors.is_empty());
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "original interior");
    drop(s);
    // The local partial detail explicitly accounts for its byte extent.
    assert!(
        o.events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                && e.work == pending.len() + size_of::<String>() + 1)
    );
    // Generic290a consumes the full prior String, but correctly accounts for
    // its flat header/drop rather than inventing a byte traversal. The two
    // complete header events are that String and the now-empty output Vec.
    assert_eq!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement
                && e.work == size_of::<String>() + 1)
            .count(),
        2
    );
}
#[test]
fn repeated_complete_stage_calls_share_the_original_work_and_fuel_budget() {
    let (m, f, summary) = mixed();
    let (_, baseline) = execute(&m, &f, &summary);
    let mut o = Observer {
        cap: Some(baseline.work),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_function_summary_signature_effect_shape_observed(&m, &f, &summary, &mut s, site())
            .unwrap(),
        oracle::ordinary(&m, &f, &summary)
    );
    assert_eq!(
        validate_function_summary_signature_effect_shape_observed(&m, &f, &summary, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "work");
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
}
#[test]
fn actual_interior_core_canonical_comparison_stop_rejects_the_module_stage() {
    let (m, f, mut summary) = fixture();
    summary.effects = Some(
        EffectSummary::pure().reading(EffectSet::Places(
            (0..100)
                .map(|index| EffectPlace::ParamPointee { index })
                .collect(),
        )),
    );
    let (_, trace) = execute(&m, &f, &summary);
    let at = trace
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<(EffectPlace, EffectPlace)>()
        })
        .nth(49)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        at: Some(at),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_function_summary_signature_effect_shape_observed(&m, &f, &summary, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original interior");
}
