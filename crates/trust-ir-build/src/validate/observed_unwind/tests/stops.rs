// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_unwind_event_refuses_without_smaller_diagnostic_success() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_unwind_structure_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "original stop");
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn original_work_and_requested_bytes_are_shared_across_repeated_unwind_validation() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work),
            byte_cap: bytes.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_unwind_structure_observed(&f, &mut session, site()).unwrap(),
            validate_unwind_structure(&f)
        );
        assert_eq!(
            validate_function_unwind_structure_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn leading_pad_index_refuses_storage_before_allocation() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    assert_eq!(
        state.leading(&fixture(), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((state.leading.len(), state.leading.capacity()), (0, 0));
    state.retire_scratch(&mut work);
}
#[test]
fn pending_reason_survives_error_vector_growth_stop_then_retires() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    let mut saw_pending = false;
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = Checking::default();
        // This test's entry differs from the public baseline by one header;
        // sweeping its full prefix plus tail still covers all direct events.
        let result = state
            .leading(&f, &mut work)
            .and_then(|()| state.edges(&f, &mut work))
            .and_then(|()| state.pads(&f, &mut work));
        if let Some(ValidationError::MisplacedLandingPad { reason, .. }) = &state.pending {
            assert!(!reason.is_empty());
            saw_pending = true;
            assert!(result.is_err());
        }
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert!(state.pending.is_none());
        assert!(state.text.is_empty());
        assert!(state.errors.is_empty());
    }
    assert!(saw_pending);
}
#[test]
fn bounded_decimal_reason_text_preserves_usize_extremes_without_formatting() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    for value in [0, 1, usize::MAX] {
        let mut output = String::new();
        work.number(value, &mut output).unwrap();
        assert_eq!(output, value.to_string());
        work.retire(output);
    }
}
#[test]
fn final_publication_refusal_retires_the_complete_reason_vectors() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    let mut observer = Observer {
        stop_at: Some(baseline.events.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_unwind_structure_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(
        observer
            .events
            .iter()
            .skip(baseline.events.len())
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
