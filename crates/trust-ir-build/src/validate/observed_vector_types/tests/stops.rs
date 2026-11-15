// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_actual_module_and_block_callback_refuses_without_partial_diagnostics() {
    let module = fixture();
    let ty = Ty::Vector(Box::new(bad()), 0);
    for module_case in [false, true] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        if module_case {
            validate_module_vector_types_observed(&module, &mut session, site()).unwrap();
        } else {
            validate_vector_type_observed(&ty, 42, &mut session, site()).unwrap();
        }
        for (index, expected) in baseline.events.into_iter().enumerate() {
            let mut observer = Observer {
                stop: Some(index + 1),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            let result = if module_case {
                validate_module_vector_types_observed(&module, &mut session, site())
            } else {
                validate_vector_type_observed(&ty, 42, &mut session, site())
            };
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(session.first_refusal().unwrap().progress, expected);
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original vector stop"
            );
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(
                observer
                    .events
                    .iter()
                    .skip(index + 1)
                    .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}

#[test]
fn cumulative_work_and_requested_byte_caps_persist_across_both_public_entries() {
    let module = fixture();
    let (_, baseline) = run(&module);
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work),
            byte_cap: bytes.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_module_vector_types_observed(&module, &mut session, site()).unwrap(),
            validate_module_vector_types(&module)
        );
        assert_eq!(
            validate_vector_type_observed(&bad(), 0, &mut session, site()),
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
fn initial_frame_and_location_requests_refuse_before_storage_is_allocated() {
    let ty = bad();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.check(&ty, Context::Block(0), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((state.frames.len(), state.frames.capacity()), (0, 0));
    state.retire_scratch(&mut work);
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
        state.location(Location::Global("λ"), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((state.location.len(), state.location.capacity()), (0, 0));
    state.retire_scratch(&mut work);
}

#[test]
fn completed_location_type_reason_are_retained_before_first_error_storage_request() {
    let ty = bad();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        location: "location λ".into(),
        ..State::default()
    };
    state.report(&ty, LANE, Context::Module, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    // Same private report entry and State in baseline and replay. Last two
    // Validation events are Vec growth and the retained enum construction.
    let stop = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.phase == ExecutionPhase::Validation)
        .rev()
        .nth(1)
        .unwrap()
        .0
        + 1;
    assert_eq!(
        baseline.events[stop - 1].copy_bytes,
        size_of::<ValidationError>()
    );
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        location: "location λ".into(),
        ..State::default()
    };
    assert_eq!(
        state.report(&ty, LANE, Context::Module, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.pending_location, "location λ");
    assert_eq!(state.pending_ty, "<0 x ptr>");
    assert_eq!(state.pending_reason, LANE);
    assert_eq!((state.errors.len(), state.errors.capacity()), (0, 0));
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert_eq!(
        state.pending_location.capacity()
            + state.pending_ty.capacity()
            + state.pending_reason.capacity(),
        0
    );
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn reason_copy_refusal_retains_completed_helper_type_and_uncommitted_reason_allocation() {
    let ty = bad();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        location: "location λ".into(),
        ..State::default()
    };
    state.report(&ty, LANE, Context::Module, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    // Actual reason copy follows its identically priced first growth event.
    let stop = baseline
        .events
        .iter()
        .rposition(|e| {
            e.phase == ExecutionPhase::Validation
                && e.work == LANE.len()
                && e.copy_bytes == LANE.len()
        })
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        location: "location λ".into(),
        ..State::default()
    };
    assert_eq!(
        state.report(&ty, LANE, Context::Module, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.pending_location, "location λ");
    assert_eq!(state.pending_ty, "<0 x ptr>");
    assert!(state.pending_reason.is_empty() && state.pending_reason.capacity() >= LANE.len());
    assert!(state.errors.is_empty());
    state.retire_scratch(&mut work);
    assert_eq!(
        state.pending_ty.capacity() + state.pending_reason.capacity(),
        0
    );
}

#[test]
fn late_location_copy_and_actual_type_formatter_copy_use_same_original_refusal() {
    let name = "λ".repeat(3000);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.location(Location::Global(&name), &mut work).unwrap();
    state.retire_scratch(&mut work);
    // Prefix growth is8; name growth is1048, so these1024 events are actual
    // copies. Refuse second copy after exactly first1024UTF8 bytes are owned.
    let stop = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == 1024 && e.copy_bytes == 1024)
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.location(Location::Global(&name), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.location, "global '".to_owned() + &"λ".repeat(512));
    state.retire_scratch(&mut work);
    let ty = Ty::Vector(
        Box::new(Ty::Dialect(Box::new(trust_ir::DialectTy::new(
            &name, "raw", 0,
        )))),
        1,
    );
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    validate_vector_type_observed(&ty, 0, &mut session, site()).unwrap();
    let stop = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_vector_type_observed(&ty, 0, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original vector stop"
    );
    assert!(observer.events.len() > stop);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn late_tuple_stop_keeps_prior_errors_and_lazy_headers_until_explicit_retirement() {
    let ty = Ty::Tuple(vec![bad(), Ty::Tuple(vec![Ty::Bool; 64]), bad()]);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.check(&ty, Context::Block(17), &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let mut saw = false;
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
        let mut state = State::default();
        let result = state.check(&ty, Context::Block(17), &mut work);
        if result.is_err() && state.errors.len() == 2 && !state.frames.is_empty() {
            saw = true;
            assert_eq!(
                state.errors,
                vec![
                    block_error(17, "<0 x ptr>", ZERO),
                    block_error(17, "<0 x ptr>", LANE)
                ]
            );
        }
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert_eq!(
            state.frames.capacity()
                + state.errors.capacity()
                + state.pending_ty.capacity()
                + state.pending_reason.capacity(),
            0
        );
    }
    assert!(saw);
}

#[test]
fn final_publication_refusal_retires_each_string_and_post_drop_stop_never_resumes() {
    let module = fixture();
    let (_, baseline) = run(&module);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_module_vector_types_observed(&module, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    // Each18 module errors has3 string pre/post drops plus pop/last poll.
    assert!(observer.events.len() >= stop + 18 * 8 + 2);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    let mut observer = Observer {
        stop: Some(2),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    work.retire(String::from("owned"));
    assert_eq!(work.session.first_refusal().unwrap().progress.work, 0);
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original vector stop"
    );
}
