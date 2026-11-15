// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

#[test]
fn every_actual_callback_refuses_without_partial_map_and_preserves_original_cause() {
    let f = fixture();
    for contextual in [false, true] {
        let module = Module::new("stops");
        let context = contextual.then_some(&module);
        let (_, baseline) = run(&f, context);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            let result = match context {
                Some(module) => build_module_value_types_observed(&f, module, &mut session, site()),
                None => build_function_value_types_observed(&f, &mut session, site()),
            };
            assert!(matches!(result, Err(ObservedValueError::AdmissionRefused)));
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original value stop"
            );
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}

#[test]
fn cumulative_work_and_copy_caps_span_whole_map_calls_without_a_new_session() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    build_function_value_types_observed(&f, &mut session, site()).unwrap();
    build_function_value_types_observed(&f, &mut session, site()).unwrap();
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        build_function_value_types_observed(&f, &mut session, site()).unwrap();
        assert!(matches!(
            build_function_value_types_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert!(matches!(
            build_function_value_types_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
    }
}

#[test]
fn first_row_storage_refuses_before_growth_and_keeps_the_pending_owned_type() {
    let mut state = State::default();
    state.pending = Some(Ty::Tuple(vec![Ty::U32; 64]));
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.commit(1, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        (state.output.rows.len(), state.output.rows.capacity()),
        (0, 0)
    );
    assert!(matches!(state.pending,Some(Ty::Tuple(ref values)) if values.len()==64));
    state.retire_scratch(&mut work);
    assert!(state.pending.is_none());
    assert_eq!(work.session.first_refusal().unwrap().cause, "bytes");
}

#[test]
fn successful_clone_stays_pending_across_the_next_lookup_refusal() {
    let f = function(vec![node(
        Inst::Undef {
            ty: Ty::Tuple(vec![Ty::U32; 128]),
        },
        &[1],
    )]);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    state.walk(&f, Context::Function, &mut work).unwrap();
    let stop = baseline
        .events
        .iter()
        .position(|event| event.phase == ExecutionPhase::Publication)
        .unwrap()
        + 2;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.walk(&f, Context::Function, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.output.rows.is_empty());
    assert!(matches!(state.pending,Some(Ty::Tuple(ref values)) if values.len()==128));
    state.retire_scratch(&mut work);
    assert!(state.pending.is_none());
    assert!(observer.events.len() > stop + 128);
}

#[test]
fn displaced_tree_is_retired_after_replacement_and_cleanup_stop_denies_success() {
    fn state() -> State {
        let mut state = State::default();
        state.output.rows.push((1, Ty::Tuple(vec![Ty::U32; 128])));
        state.pending = Some(Ty::U16);
        state
    }
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut first = state();
    first
        .commit(
            1,
            &mut Work {
                session: &mut session,
                site: site(),
            },
        )
        .unwrap();
    let stop = baseline
        .events
        .iter()
        .position(|event| event.phase == ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = state();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.commit(1, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.output.rows, vec![(1, Ty::U16)]);
    assert!(state.pending.is_none());
    state.output.retire(&mut work);
    assert!(state.output.rows.is_empty() && state.output.rows.capacity() == 0);
    assert!(observer.events.len() > stop + 128);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn actual_lookup_interior_stop_is_typed_refusal_instead_of_missing() {
    let mut map = ObservedValueTypes::default();
    map.rows = (0..100).map(|id| (id, Ty::U32)).collect();
    let mut observer = Observer {
        work_cap: Some(3),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        map.get_observed(v(99), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(map.rows.len(), 100);
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert_eq!(
        map.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}

#[test]
fn final_publication_stop_retires_completed_rows_without_changing_input() {
    let f = fixture();
    let input = f.clone();
    let (_, baseline) = run(&f, None);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(matches!(
        build_function_value_types_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert_eq!(f, input);
    assert!(observer.events.len() > stop + 8);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn whole_successful_row_retirement_drains_nested_types_even_if_first_callback_refuses() {
    let mut map = ObservedValueTypes::default();
    map.rows = vec![(1, Ty::Tuple(vec![Ty::U32; 512])), (2, Ty::Ptr)];
    let mut observer = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        map.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original value stop"
    );
    assert!(observer.events.len() > 512);
    assert!(
        observer
            .events
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
