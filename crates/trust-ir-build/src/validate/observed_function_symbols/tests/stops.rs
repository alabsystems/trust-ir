// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_marker_equality_copy_move_cleanup_and_publication_callback_refuses() {
    let m = fixtures::fixture();
    let (_, baseline) = run(&m);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_module_function_symbols_observed(&m, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original symbol stop"
        );
        assert_eq!(
            session.first_refusal().unwrap().progress,
            baseline.events[stop - 1]
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_function_symbols_observed(&m, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cumulative_original_work_and_copy_do_not_reset_across_complete_calls() {
    let m = fixtures::fixture();
    let (_, baseline) = run(&m);
    for copy in [false, true] {
        let mut observer = Observer {
            work_cap: (!copy).then_some(baseline.work),
            byte_cap: copy.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_module_function_symbols_observed(&m, &mut session, site())
                .unwrap()
                .len(),
            4
        );
        assert_eq!(
            validate_module_function_symbols_observed(&m, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copy { "copy cap" } else { "work cap" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn actual_long_marker_scan_stops_inside_positions_before_reading_the_far_tail() {
    let m = module(vec![function(
        0,
        &("x".repeat(10000) + SYNTHETIC_SYMBOL_MARKER),
    )]);
    let mut observer = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.walk(&m, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.errors.is_empty());
    assert_eq!(
        work.session.first_refusal().unwrap().progress.work,
        SYNTHETIC_SYMBOL_MARKER.len()
    );
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "work cap");
    assert!(
        observer
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Validation
                && e.work == SYNTHETIC_SYMBOL_MARKER.len())
            .count()
            >= 2
    );
}
#[test]
fn actual_name_equality_stops_after_a_real_equal_prefix_before_the_final_difference() {
    let first = "λ".repeat(4000) + "a";
    let second = "λ".repeat(4000) + "b";
    let mut observer = Observer {
        work_cap: Some(1500),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        work.equal(&first, &second),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(work.session.first_refusal().unwrap().progress.work, 1024);
    assert_eq!(work.session.first_refusal().unwrap().cause, "work cap");
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|e| e.work == 1024 && e.copy_bytes == 0)
            .count(),
        2
    );
}
#[test]
fn first_state_header_is_admitted_before_owned_scratch_or_output_allocation() {
    let m = fixtures::fixture();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_module_function_symbols_observed(&m, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(observer.events.len(), 1);
    assert_eq!(observer.events[0].phase, ExecutionPhase::Validation);
}
#[test]
fn final_publication_refusal_consumes_all_completed_owning_attribution_errors() {
    let m = fixtures::fixture();
    let (_, baseline) = run(&m);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_module_function_symbols_observed(&m, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > stop + 4);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
