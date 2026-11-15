// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_shape_callback_refuses_and_only_original_retirement_follows() {
    let f = fixture();
    let (_, baseline) = run(&f, 32);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_exhaustive_switch_shape_observed(&f, 32, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original exhaustive stop"
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
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
fn work_and_copy_remain_cumulative_across_full_shape_calls_and_retries() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for _ in 0..2 {
        assert_eq!(
            validate_function_exhaustive_switch_shape_observed(&f, 32, &mut session, site())
                .unwrap()
                .len(),
            4
        );
    }
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_exhaustive_switch_shape_observed(&f, 32, &mut session, site())
                .unwrap()
                .len(),
            4
        );
        assert_eq!(
            validate_function_exhaustive_switch_shape_observed(&f, 32, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            validate_function_exhaustive_switch_shape_observed(&f, 32, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn all_map_key_partial_spelling_and_completed_diagnostics_remain_owned_until_cleanup() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    s.walk(&f, 32, &mut work).unwrap();
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    let (mut map, mut seen, mut text, mut output) = (false, false, false, false);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut s = State::default();
        if s.walk(&f, 32, &mut work).is_err() {
            map |= s.values.is_some();
            seen |= !s.seen.is_empty();
            text |= !s.first.is_empty() && !s.second.is_empty();
            output |= !s.errors.is_empty();
        }
        s.retire_scratch(&mut work);
        s.retire_errors(&mut work);
        assert!(empty(&s));
    }
    assert!(map && seen && text && output);
}
#[test]
fn diagnostic_reserve_refuses_before_any_owned_reason_moves() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State {
        reason: "retained reason".into(),
        ..State::default()
    };
    assert_eq!(
        s.commit(0, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.reason, "retained reason");
    assert_eq!(s.errors.capacity(), 0);
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
}
#[test]
fn actual_case_scan_can_refuse_interior_work_instead_of_publishing_a_shorter_set() {
    let f = function(Some(Ty::U128), (0..5000).map(Constant::Int).collect());
    let mut observer = Observer {
        work_cap: Some(5000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    assert_eq!(
        s.walk(&f, 128, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(!s.seen.is_empty());
    assert!(s.seen.len() < 5000);
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
}
#[test]
fn final_publication_and_cleanup_refusals_drain_complete_retained_context_and_errors() {
    let f = fixture();
    let (_, baseline) = run(&f, 32);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_exhaustive_switch_shape_observed(&f, 32, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > stop + 10);
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    s.walk(&f, 32, &mut work).unwrap();
    assert_eq!(s.errors.len(), 4);
    arm.set(true);
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original exhaustive cleanup"
    );
}
#[test]
fn original_header_refusal_precedes_all_local_allocation() {
    let f = fixture();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_exhaustive_switch_shape_observed(&f, 32, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(observer.events.len(), 1);
    assert_eq!(observer.events[0].phase, ExecutionPhase::Validation);
}
