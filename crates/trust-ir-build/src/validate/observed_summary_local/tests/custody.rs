// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn output_growth_refusal_keeps_complete_pending_text_and_allocates_no_output_buffer() {
    let (_, f, _) = fixture();
    let detail = "pending-λ\0".repeat(10000);
    let mut state = State {
        detail: detail.clone(),
        errors: Vec::new(),
    };
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let result = state.issue(&f, &mut work);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.detail, detail);
    assert_eq!((state.errors.len(), state.errors.capacity()), (0, 0));
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.detail.is_empty() && state.errors.is_empty());
    drop(work);
    drop(session);
    assert!(
        observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                && e.work == detail.len() + size_of::<String>() + 1)
    );
}
#[test]
fn final_error_header_refusal_after_capacity_admission_still_keeps_pending_text() {
    let (_, f, _) = fixture();
    let pending = "intact λ".repeat(2000);
    let mut state = State {
        detail: pending.clone(),
        errors: Vec::new(),
    };
    // issue has reserve probe, first requested buffer, then final move/header.
    let mut observer = Observer {
        at: Some(3),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let result = state.issue(&f, &mut work);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert!(state.errors.is_empty() && state.errors.capacity() >= 1);
    assert_eq!(state.detail, pending);
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.detail.is_empty() && state.errors.is_empty());
}
#[test]
fn prior_error_and_pending_text_survive_original_stop_then_both_are_fully_consumed() {
    let (_, f, _) = fixture();
    let first = "prior λ".repeat(6000);
    let pending = "pending 文".repeat(7000);
    let trigger = Rc::new(Cell::new(true));
    let mut state = State {
        detail: pending.clone(),
        errors: vec![ValidationError::InvalidFunctionSummary {
            function: f.id.index(),
            detail: first.clone(),
        }],
    };
    let mut observer = Observer {
        next: Some(trigger),
        cleanup: true,
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let result = state.issue(&f, &mut work);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.detail, pending);
    assert!(
        matches!(&state.errors[..], [ValidationError::InvalidFunctionSummary { function, detail }]
        if *function == f.id.index() && detail == &first)
    );
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.detail.is_empty() && state.errors.is_empty());
    drop(work);
    assert_eq!(session.first_refusal().unwrap().cause, "original interior");
    drop(session);
    assert!(
        observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                && e.work == pending.len() + size_of::<String>() + 1)
    );
    // Generic290a intentionally charges the flat String header, not its bytes.
    // Its prior String and final Vec headers have equal current representation.
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement
                && e.work == size_of::<String>() + 1)
            .count(),
        2
    );
    assert!(
        observer.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn cleanup_first_refusal_consumes_preexisting_outputs_and_prevents_publication() {
    let (_, f, _) = fixture();
    let mut state = State {
        detail: "partial 文".repeat(100),
        errors: vec![ValidationError::InvalidFunctionSummary {
            function: f.id.index(),
            detail: "prior".repeat(500),
        }],
    };
    let mut observer = Observer {
        cleanup: true,
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.finish(Ok(()), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.detail.is_empty() && state.errors.is_empty());
    drop(work);
    assert_eq!(session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn terminal_outer_publication_refusal_consumes_the_complete_diagnostic_vector() {
    let (m, f, summary) = mixed();
    let (_, baseline) = execute(&m, &f, &summary, SummaryCitation::Absent);
    let final_event = baseline.events.last().unwrap();
    assert_eq!(
        (final_event.phase, final_event.work, final_event.copy_bytes),
        (
            ExecutionPhase::Publication,
            1,
            size_of::<Vec<ValidationError>>()
        )
    );
    // Replay the identical public entry and refuse only its final admission.
    // Earlier local empty-detail retirement remains identical to baseline.
    let mut observer = Observer {
        at: Some(baseline.events.len()),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_summary_local_backing_observed(
            &m,
            &f,
            &summary,
            SummaryCitation::Absent,
            &mut session,
            site(),
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "original interior");
    drop(session);
    assert!(observer.events.len() > baseline.events.len());
    assert!(
        observer.events[baseline.events.len()..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn typed_failure_without_observer_refusal_still_consumes_every_owned_field() {
    let (_, f, _) = fixture();
    let mut state = State {
        detail: "pending".repeat(1000),
        errors: vec![ValidationError::InvalidFunctionSummary {
            function: f.id.index(),
            detail: "prior".repeat(1000),
        }],
    };
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.finish(Err(ObservedValueError::CapacityOverflow), &mut work),
        Err(ObservedValueError::CapacityOverflow)
    );
    assert!(state.detail.is_empty() && state.errors.is_empty());
    drop(work);
    assert!(session.first_refusal().is_none());
    drop(session);
    // Generic cleanup's terminal 0/0 publication is a cleanup return, not a
    // published module report; this is deliberately distinct from sticky stop.
    assert_eq!(
        observer
            .events
            .last()
            .map(|e| (e.phase, e.work, e.copy_bytes)),
        Some((ExecutionPhase::Publication, 0, 0))
    );
}
