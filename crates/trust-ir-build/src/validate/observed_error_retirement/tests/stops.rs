// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_actual_cleanup_and_terminal_callback_keeps_first_cause_and_finishes_all_inputs() {
    let baseline = run_corpus();
    for (index, expected) in baseline.events.iter().copied().enumerate() {
        let mut observer = Observer {
            stop: Some(index + 1),
            refuse_later: true,
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            retire_validation_errors_observed(corpus(), &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, expected);
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original cleanup refusal"
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        // Refusal does not drop unvisited inputs through an enclosing Vec Drop.
        // Actual per-payload pre/post callbacks still reach the same full count.
        assert_eq!(headers(&observer), headers(&baseline));
        assert!(
            observer
                .events
                .iter()
                .skip(index + 1)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
        assert_eq!(
            observer.events.len(),
            baseline.events.len() - usize::from(index + 1 < baseline.events.len())
        );
    }
}

#[test]
fn already_sticky_original_session_still_consumes_all_269_variants_and_nested_payloads() {
    let mut observer = Observer {
        stop: Some(1),
        refuse_later: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let initial = ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 1,
        copy_bytes: 0,
    };
    assert!(session.admit(initial).is_err());
    let cases = witnesses::all();
    let expected_headers = cases.iter().map(|(_, n)| n).sum::<usize>() + 1;
    let errors = cases.into_iter().map(|(e, _)| e).collect();
    assert_eq!(
        retire_validation_errors_observed(errors, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().progress, initial);
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original cleanup refusal"
    );
    assert_eq!(headers(&observer), expected_headers);
    assert!(
        observer
            .events
            .iter()
            .skip(1)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn cumulative_original_work_cap_is_not_renewed_and_subsequent_inputs_are_still_consumed() {
    let baseline = run_corpus();
    let mut observer = Observer {
        work_cap: Some(baseline.work),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    retire_validation_errors_observed(corpus(), &mut session, site()).unwrap();
    assert_eq!(
        retire_validation_errors_observed(corpus(), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let cause = session.first_refusal().unwrap().progress;
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original cumulative work"
    );
    assert_eq!(
        retire_validation_errors_observed(corpus(), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().progress, cause);
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert_eq!(headers(&observer), 3 * headers(&baseline));
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Publication)
            .count(),
        1
    );
    assert!(
        observer
            .events
            .iter()
            .all(|e| e.site == site() && e.copy_bytes == 0)
    );
}

#[test]
fn refusal_at_final_empty_buffer_post_drop_poll_denies_terminal_publication() {
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    retire_validation_errors_observed(Vec::with_capacity(32), &mut session, site()).unwrap();
    let stop = baseline.events.len() - 1;
    assert_eq!(
        baseline.events[stop - 1].phase,
        ExecutionPhase::ScratchRetirement
    );
    assert_eq!(baseline.events[stop - 1].work, 0);
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        retire_validation_errors_observed(Vec::with_capacity(32), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress,
        baseline.events[stop - 1]
    );
    assert_eq!(observer.events.len(), stop);
    assert!(
        observer
            .events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn final_publication_refusal_has_no_remaining_owned_payload_to_abandon() {
    let baseline = run_corpus();
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        retire_validation_errors_observed(corpus(), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert_eq!(observer.events.len(), stop);
    assert_eq!(headers(&observer), headers(&baseline));
}

#[test]
fn actual_wide_string_and_numeric_lists_finish_under_initial_resource_refusal() {
    let strings = (0..50_000).map(|_| String::from("owned")).collect();
    let errors = vec![
        ValidationError::ImportCycle {
            import: 0,
            path: strings,
        },
        ValidationError::AmbiguousImportedSymbol {
            symbol: "symbol".into(),
            imports: vec![7; 50_000],
        },
    ];
    let mut observer = Observer {
        work_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        retire_validation_errors_observed(errors, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original cumulative work"
    );
    assert_eq!(headers(&observer), 50_000 + 4); // All Strings,2 list buffers,outer buffer.
    assert!(observer.events.len() > 200_000);
    assert!(
        observer
            .events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn single_error_also_finishes_nested_payloads_after_an_original_refusal() {
    let (error, count) = nested_cases::specs().pop().unwrap();
    let baseline = one(error, count);
    let (error, _) = nested_cases::specs().pop().unwrap();
    let mut observer = Observer {
        stop: Some(2),
        refuse_later: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        retire_validation_error_observed(error, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original cleanup refusal"
    );
    assert_eq!(headers(&observer), count);
    assert_eq!(observer.events.len(), baseline.events.len() - 1);
    assert!(
        observer
            .events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
