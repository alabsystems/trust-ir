// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_visit_growth_output_cleanup_and_publication_callback_refuses() {
    let m = fixture();
    for kind in [Component::Spans, Component::Weights, Component::Diagnostics] {
        let (_, base) = run(&m, kind);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                component(&m, kind, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "original metadata stop");
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert!(
                o.events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_original_work_and_copy_span_repeated_calls_without_owner_reset() {
    let m = fixture();
    for kind in [Component::Spans, Component::Weights, Component::Diagnostics] {
        let (_, base) = run(&m, kind);
        for bytes in [false, true] {
            let mut o = Observer {
                work_cap: (!bytes).then_some(base.work),
                byte_cap: bytes.then_some(base.bytes),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            component(&m, kind, &mut s, site()).unwrap();
            assert_eq!(
                component(&m, kind, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            let first = s.first_refusal().unwrap().progress;
            assert_eq!(
                component(&m, kind, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, first);
            assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
        }
    }
}
#[test]
fn actual_id_collection_reaches_last_original_row_before_any_diagnostic_result() {
    let mut m = fixture();
    m.proof_obligations = (0..500).map(obligation).collect();
    m.obligation_diagnostics = vec![diagnostic(999, None)];
    let mut o = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.diagnostics(&m, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(!state.ids.is_empty());
    assert!(state.ids.len() < 500);
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn membership_interior_cancellation_keeps_complete_id_scratch_and_no_partial_error() {
    let mut m = fixture();
    m.proof_obligations = (0..200).map(obligation).collect();
    m.obligation_diagnostics = vec![diagnostic(999, None)];
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.diagnostics(&m, &mut work).unwrap();
    let validation = base
        .events
        .iter()
        .filter(|e| e.phase == ExecutionPhase::Validation)
        .count();
    assert!(validation > 1000);
    let stop = base
        .events
        .iter()
        .enumerate()
        .rfind(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .unwrap()
        .0
        - 100;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.diagnostics(&m, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.ids, (0..200).collect::<Vec<_>>());
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn actual_output_allocation_and_move_refusals_preserve_prior_complete_diagnostics() {
    let m = fixture();
    let (_, base) = run(&m, Component::Weights);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .nth(2)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.weights(&m, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(!state.errors.is_empty());
    assert!(state.errors.len() < 5);
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn initial_header_and_final_publication_refuse_without_any_result_escape() {
    let m = fixture();
    for kind in [Component::Spans, Component::Weights, Component::Diagnostics] {
        let mut o = Observer {
            byte_cap: Some(0),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            component(&m, kind, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(o.events.len(), 1);
        let (_, base) = run(&m, kind);
        let stop = base.events.len();
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            component(&m, kind, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
        assert!(o.events.len() > stop);
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn refused_cleanup_consumes_all_ids_and_completed_errors_in_same_original_session() {
    let m = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.diagnostics(&m, &mut work).unwrap();
    assert!(!state.ids.is_empty());
    assert_eq!(state.errors.len(), 2);
    arm.set(true);
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn preexisting_stop_does_not_walk_inputs_and_preserves_original_first_cause() {
    let m = fixture();
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 11,
        copy_bytes: 0,
    };
    assert!(s.admit(first).is_err());
    for kind in [Component::Spans, Component::Weights, Component::Diagnostics] {
        assert_eq!(
            component(&m, kind, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
    }
    assert_eq!(o.events, vec![first]);
}
