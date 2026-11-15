// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_component_event_stops_without_partial_success_and_only_retires_afterward() {
    let f = fixture();
    for case in [Case::Structure, Case::BodyGate, Case::Symbols] {
        let (_, baseline) = observed(&f, case);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop_at: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                run(&f, case, &mut session),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
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
fn cumulative_work_and_bytes_are_shared_across_all_three_constituents() {
    let f = fixture();
    let cases = [Case::Structure, Case::BodyGate, Case::Symbols];
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for case in cases {
        run(&f, case, &mut session).unwrap();
    }
    for bytes in [false, true] {
        let mut observer = if bytes {
            Observer {
                byte_cap: Some(baseline.bytes - 1),
                ..Observer::default()
            }
        } else {
            Observer {
                work_cap: Some(baseline.work - 1),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        run(&f, Case::Structure, &mut session).unwrap();
        run(&f, Case::BodyGate, &mut session).unwrap();
        assert_eq!(
            run(&f, Case::Symbols, &mut session),
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
fn full_pending_diagnostic_is_retained_when_error_vector_growth_is_refused() {
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    state
        .detail(
            "detail",
            |detail| ValidationError::InvalidBodyGate {
                function: 81,
                detail,
            },
            &mut work,
        )
        .unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let stop = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == 1 && e.copy_bytes == size_of::<ValidationError>())
        .nth(1)
        .unwrap()
        .0
        + 1;
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
    assert_eq!(
        state.detail(
            "detail",
            |detail| ValidationError::InvalidBodyGate {
                function: 81,
                detail
            },
            &mut work
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(
        matches!(&state.pending, Some(ValidationError::InvalidBodyGate { detail, .. }) if detail == "detail")
    );
    assert_eq!(state.errors.capacity(), 0);
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn fixed_definition_workspace_growth_is_admitted_before_any_allocation() {
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
        state.definition(8, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.definitions.is_empty());
    assert_eq!(state.definitions.capacity(), 0);
    state.retire_scratch(&mut work);
    assert_eq!(work.session.first_refusal().unwrap().cause, "bytes");
}
#[test]
fn final_publication_refusal_retires_each_completed_error_string_before_return() {
    let f = fixture();
    for case in [Case::Structure, Case::BodyGate, Case::Symbols] {
        let (_, baseline) = observed(&f, case);
        let last = baseline.events.len();
        let mut observer = Observer {
            stop_at: Some(last),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            run(&f, case, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
        assert!(observer.events.len() > last);
        assert!(
            observer
                .events
                .iter()
                .skip(last)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cross_crate_retirement_keeps_actual_callbacks_and_original_sticky_cause() {
    let mut observer = Observer {
        stop_at: Some(1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(
        session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: site(),
                work: 1,
                copy_bytes: 0
            })
            .is_err()
    );
    let mut state = Checking {
        errors: vec![ValidationError::InvalidBodyGate {
            function: 81,
            detail: "owned".into(),
        }],
        ..Checking::default()
    };
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(work.session.first_refusal().unwrap().cause, "interior");
    assert_eq!(
        work.session.remaining_fuel(),
        InterpretOptions::default().fuel
    );
    assert!(observer.events.len() > 5);
    assert!(
        observer
            .events
            .iter()
            .skip(1)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
