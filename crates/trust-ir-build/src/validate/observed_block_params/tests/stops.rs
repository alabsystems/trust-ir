// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
#[test]
fn every_actual_callback_refuses_and_only_retires_under_the_original_first_cause() {
    let (call, module) = call_fixture(true);
    let base = fixture();
    for (f, module) in [(&base, None), (&call, Some(&module))] {
        let (_, baseline) = observed(f, module);
        for stop_at in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop_at: Some(stop_at),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                validate_function_block_params_observed(f, module, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original block-param stop"
            );
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop_at)
                    .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn repeated_components_keep_cumulative_work_bytes_and_the_same_original_refusal() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for _ in 0..2 {
        validate_function_block_params_observed(&f, None, &mut session, site()).unwrap();
    }
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_block_params_observed(&f, None, &mut session, site())
                .unwrap()
                .len(),
            3
        );
        assert_eq!(
            validate_function_block_params_observed(&f, None, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(
            validate_function_block_params_observed(&f, None, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn output_storage_refusal_keeps_the_complete_pending_diagnostic_before_allocation() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Diagnostics {
        pending: Some(ValidationError::BranchArgCountMismatch {
            block: 0,
            target: 1,
            expected: 2,
            actual: 1,
        }),
        ..Diagnostics::default()
    };
    assert_eq!(
        state.commit(&mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.pending.is_some());
    assert_eq!((state.errors.len(), state.errors.capacity()), (0, 0));
    state.retire_scratch(&mut work);
    assert!(state.pending.is_none());
}
#[test]
fn actual_edges_map_text_pending_and_prior_errors_remain_owned_at_every_later_stop() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.run(&f, None, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.diagnostics.retire_errors(&mut work);
    let (mut edges, mut map, mut text, mut pending, mut errors) =
        (false, false, false, false, false);
    for stop_at in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        if state.run(&f, None, &mut work).is_err() {
            edges |= !state.edges.is_empty();
            map |= state.values.is_some();
            text |= !state.diagnostics.expected.is_empty();
            pending |= matches!(
                state.diagnostics.pending,
                Some(ValidationError::BranchArgTypeMismatch { .. })
            );
            errors |= !state.diagnostics.errors.is_empty();
        }
        state.retire_scratch(&mut work);
        state.diagnostics.retire_errors(&mut work);
        assert!(state.values.is_none() && state.edges.is_empty());
        assert!(state.diagnostics.pending.is_none() && state.diagnostics.errors.is_empty());
        assert!(state.diagnostics.expected.is_empty() && state.diagnostics.actual.is_empty());
    }
    assert!(edges && map && text && pending && errors);
}
#[test]
fn final_publication_refusal_retires_all_completed_error_strings_and_the_result_buffer() {
    let f = fixture();
    let (_, baseline) = observed(&f, None);
    let mut observer = Observer {
        stop_at: Some(baseline.events.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_block_params_observed(&f, None, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    let cleanup = &observer.events[baseline.events.len()..];
    assert!(cleanup.len() > 6);
    assert!(
        cleanup
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn local_map_and_edge_cleanup_finishes_after_a_same_session_retirement_refusal() {
    let f = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        cleanup_stop: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.run(&f, None, &mut work).unwrap();
    // Tighten this same observer only after construction. No fresh owner,
    // successful result or replacement session is introduced for cleanup.
    arm.set(true);
    state.retire_scratch(&mut work);
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    state.diagnostics.retire_errors(&mut work);
    assert!(state.values.is_none() && state.edges.is_empty());
    assert!(state.diagnostics.errors.is_empty());
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original cleanup stop"
    );
}
#[test]
fn actual_reverse_target_scan_stops_interiorly_without_cloning_parameter_maps() {
    let mut f = fixture();
    f.blocks.extend((2..5000).map(|id| Block::new(b(id))));
    let mut observer = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert!(matches!(
        walk::target_params(&f, 0, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
    assert!(observer.events.len() < 150);
}
#[test]
fn an_existing_partial_string_or_pending_error_is_not_implicitly_overwritten() {
    let mut state = Diagnostics {
        expected: String::with_capacity(10),
        ..Diagnostics::default()
    };
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.count(0, 1, 2, 1, &mut work),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(state.expected.capacity() >= 10);
    state.retire_scratch(&mut work);
    assert_eq!(state.expected.capacity(), 0);
    state.pending = Some(ValidationError::BranchArgCountMismatch {
        block: 0,
        target: 1,
        expected: 2,
        actual: 1,
    });
    assert_eq!(
        state.mismatch(0, 1, 0, &Ty::U32, &Ty::I32, &mut work),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(state.pending.is_some());
    state.retire_scratch(&mut work);
    assert!(state.pending.is_none());
}
#[test]
fn real_observed_type_spelling_stops_inside_wide_expected_text_and_keeps_custody() {
    let expected = Ty::Tuple(vec![Ty::U32; 5000]);
    let actual = Ty::I32;
    let mut observer = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Diagnostics::default();
    assert_eq!(
        state.mismatch(0, 1, 0, &expected, &actual, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(state.pending.is_none() && state.errors.is_empty());
    assert!(state.expected.is_empty() && state.actual.is_empty());
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
}
