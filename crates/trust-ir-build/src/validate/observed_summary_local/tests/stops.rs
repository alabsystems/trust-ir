// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_mixed_callback_refuses_without_publishing_a_shorter_error_list() {
    let (m, f, summary) = mixed();
    let (_, trace) = execute(&m, &f, &summary, SummaryCitation::Absent);
    for at in 1..=trace.events.len() {
        let mut observer = Observer {
            at: Some(at),
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
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn repeated_whole_calls_share_the_same_cumulative_work_budget() {
    let (m, f, summary) = mixed();
    let (_, trace) = execute(&m, &f, &summary, SummaryCitation::Absent);
    let mut observer = Observer {
        cap: Some(trace.work),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let expected = oracle::ordinary(&m, &f, &summary, SummaryCitation::Absent);
    assert_eq!(
        validate_function_summary_local_backing_observed(
            &m,
            &f,
            &summary,
            SummaryCitation::Absent,
            &mut session,
            site(),
        )
        .unwrap(),
        expected
    );
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
    assert_eq!(session.first_refusal().unwrap().cause, "work");
}
#[test]
fn repeated_whole_calls_share_the_same_copy_budget() {
    let (m, f, summary) = mixed();
    let (_, trace) = execute(&m, &f, &summary, SummaryCitation::Absent);
    let mut observer = Observer {
        byte_cap: Some(trace.bytes),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(
        validate_function_summary_local_backing_observed(
            &m,
            &f,
            &summary,
            SummaryCitation::Absent,
            &mut session,
            site(),
        )
        .is_ok()
    );
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
    assert_eq!(session.first_refusal().unwrap().cause, "bytes");
}
#[test]
fn original_first_header_admission_can_stop_before_state_construction() {
    let (m, f, summary) = mixed();
    let mut observer = Observer {
        at: Some(1),
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
    drop(session);
    assert_eq!(observer.events.len(), 1);
    assert_eq!(
        observer.events[0].copy_bytes,
        size_of::<State>() + size_of::<Work<'_, '_, Observer>>()
    );
}
#[test]
fn duplicate_equality_can_stop_inside_the_actual_long_payload_comparison() {
    let (m, f, mut summary) = fixture();
    let a = "x".repeat(65536);
    let mut b = a.clone();
    b.replace_range(65535.., "y");
    summary.requires = vec![formula(&a), formula(&b)];
    let (_, trace) = execute(&m, &f, &summary, SummaryCitation::Absent);
    let at = trace
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| {
            event.phase == ExecutionPhase::Validation && event.work == 1024 && event.copy_bytes == 0
        })
        .nth(20)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        at: Some(at),
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
}
#[test]
fn backing_equality_can_stop_inside_the_actual_scoped_row_payload() {
    let (mut m, f, mut summary) = fixture();
    let payload = "文".repeat(30000);
    summary.requires = vec![formula(&payload)];
    m.proof_obligations.push(row(
        1,
        ObligationKind::Precondition,
        ProofStatus::Certified,
        Some(formula(&payload)),
        Some(f.id),
    ));
    let (_, trace) = execute(&m, &f, &summary, SummaryCitation::Absent);
    let at = trace
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| {
            event.phase == ExecutionPhase::Validation && event.work == 1024 && event.copy_bytes == 0
        })
        .nth(40)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        at: Some(at),
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
}
#[test]
fn actual_long_raw_clause_rendering_can_stop_between_chunks() {
    let (m, f, mut summary) = fixture();
    summary.requires = vec![formula(&"λ".repeat(30000))];
    let (_, trace) = execute(&m, &f, &summary, SummaryCitation::Absent);
    let at = trace
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| {
            event.phase == ExecutionPhase::Validation
                && event.work == 1024
                && event.copy_bytes == 1024
        })
        .nth(25)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        at: Some(at),
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
    drop(session);
    assert!(
        observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement && e.work > 20000)
    );
}
#[test]
fn wide_scope_scan_is_observed_before_each_physical_row_guard() {
    let (mut m, f, _) = fixture();
    for id in 0..100 {
        m.proof_obligations.push(row(
            id,
            ObligationKind::Precondition,
            ProofStatus::Failed,
            None,
            None,
        ));
    }
    // Both baseline and refusal use the identical private failed_rows entry.
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    state
        .failed_rows(
            &m,
            &f,
            &mut Work {
                session: &mut session,
                site: site(),
            },
        )
        .unwrap();
    drop(session);
    let at = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| {
            event.phase == ExecutionPhase::Validation && event.work == 2 && event.copy_bytes == 0
        })
        .nth(49)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        at: Some(at),
        ..Default::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let result = state.failed_rows(&m, &f, &mut work);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.detail.is_empty() && state.errors.is_empty());
}
