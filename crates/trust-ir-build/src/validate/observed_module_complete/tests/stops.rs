// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_validation_copy_scratch_and_publication_callback_refuses_without_partial_label() {
    let mut complete = Module::new("complete");
    complete.completeness = Some(ModuleCompleteness::Complete);
    for module in [
        Module::new("none"),
        complete,
        partial(vec![]),
        fixtures::module(),
    ] {
        let (_, baseline) = run(&module);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                validate_module_complete_observed(&module, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original completeness stop"
            );
            assert_eq!(
                session.first_refusal().unwrap().progress,
                baseline.events[stop - 1]
            );
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert_eq!(
                validate_module_complete_observed(&module, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn every_display_callback_refuses_in_both_error_variants_without_partial_text() {
    for error in fixtures::errors() {
        let (_, baseline) = text(&error);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                error.display_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().progress,
                baseline.events[stop - 1]
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original completeness stop"
            );
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn every_consuming_retirement_callback_still_reaches_all_original_rows_and_fields() {
    for error in fixtures::errors() {
        let baseline = retired(error.clone());
        let expected = baseline
            .events
            .iter()
            .copied()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .collect::<Vec<_>>();
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                error.clone().retire_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original completeness stop"
            );
            assert_eq!(
                session.first_refusal().unwrap().progress,
                baseline.events[stop - 1]
            );
            assert_eq!(
                observer
                    .events
                    .iter()
                    .copied()
                    .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
                    .collect::<Vec<_>>(),
                expected
            );
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_original_work_and_copy_cover_successive_partial_clones_without_reset() {
    let module = fixtures::module();
    let (_, baseline) = run(&module);
    for copy in [false, true] {
        let mut observer = Observer {
            work_cap: (!copy).then_some(baseline.work),
            byte_cap: copy.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(
            validate_module_complete_observed(&module, &mut session, site())
                .unwrap()
                .is_err()
        );
        assert_eq!(
            validate_module_complete_observed(&module, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copy { "copy cap" } else { "work cap" }
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_complete_observed(&module, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn cumulative_display_work_and_copy_share_the_original_owner_across_errors() {
    let error = CompletenessError::ModuleIncomplete {
        rows: fixtures::rows(),
    };
    let (_, baseline) = text(&error);
    for copy in [false, true] {
        let mut observer = Observer {
            work_cap: (!copy).then_some(baseline.work),
            byte_cap: copy.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        error.display_observed(&mut session, site()).unwrap();
        assert_eq!(
            error.display_observed(&mut session, site()),
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
fn initial_state_and_string_headers_refuse_before_any_owned_scratch_is_constructed() {
    let module = fixtures::module();
    let error = CompletenessError::ModuleIncomplete {
        rows: fixtures::rows(),
    };
    for display in [false, true] {
        let mut observer = Observer {
            byte_cap: Some(0),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        if display {
            assert_eq!(
                error.display_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        } else {
            assert_eq!(
                validate_module_complete_observed(&module, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        }
        assert_eq!(session.first_refusal().unwrap().cause, "copy cap");
        assert_eq!(observer.events.len(), 1);
        assert_eq!(observer.events[0].phase, ExecutionPhase::Validation);
    }
}
#[test]
fn final_validation_and_display_publication_refusal_consumes_completed_owned_output() {
    let module = partial(vec![row("symbol", Some("path"), "reason")]);
    let (_, baseline) = run(&module);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_module_complete_observed(&module, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    for bytes in ["symbol".len(), "path".len(), "reason".len()] {
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                    && e.work == bytes + size_of::<String>() + 1)
        );
    }
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    let error = CompletenessError::ModuleIncomplete {
        rows: fixtures::rows(),
    };
    let (output, baseline) = text(&error);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        error.display_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(observer.events.len(), stop + 2);
    assert_eq!(
        observer.events[stop].work,
        output.len() + size_of::<String>() + 1
    );
}
#[test]
fn cumulative_consuming_retirement_work_cannot_resume_after_its_original_stop() {
    let error = CompletenessError::ModuleIncomplete {
        rows: fixtures::rows(),
    };
    let baseline = retired(error.clone());
    let expected = baseline
        .events
        .iter()
        .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .count();
    let mut observer = Observer {
        work_cap: Some(baseline.work),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    error.clone().retire_observed(&mut session, site()).unwrap();
    assert_eq!(
        error.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work cap");
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .count(),
        2 * expected
    );
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Publication)
            .count(),
        1
    );
}
