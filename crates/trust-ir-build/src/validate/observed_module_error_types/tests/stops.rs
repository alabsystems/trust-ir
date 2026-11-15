// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_actual_callback_refuses_without_a_partial_error_census_and_preserves_cause() {
    let module = fixture();
    let (_, baseline) = observed(&module);
    for (index, expected) in baseline.events.into_iter().enumerate() {
        let mut observer = Observer {
            stop: Some(index + 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_module_error_types_observed(&module, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, expected);
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original poison stop"
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

#[test]
fn cumulative_original_work_and_byte_caps_cover_repeated_complete_module_passes() {
    let module = fixture();
    let (_, baseline) = observed(&module);
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work),
            byte_cap: bytes.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_module_error_types_observed(&module, &mut session, site()).unwrap(),
            validate_module_error_types(&module)
        );
        assert_eq!(
            validate_module_error_types_observed(&module, &mut session, site()),
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
fn first_frame_and_location_storage_refuse_before_any_allocation() {
    let ty = Ty::Error;
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
        state.check(&ty, Buffer::Base, &mut work),
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
fn three_completed_owned_error_strings_remain_pending_at_first_error_storage_refusal() {
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
    state.poison(Buffer::Base, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    // Identical private entries. The second-last Validation callback is the
    // requested first output slot, immediately before enum construction.
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
        state.poison(Buffer::Base, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.pending_location, "location λ");
    assert_eq!(state.pending_expected, EXPECTED);
    assert_eq!(state.pending_actual, "error");
    assert_eq!((state.errors.len(), state.errors.capacity()), (0, 0));
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert_eq!(
        state.pending_location.capacity()
            + state.pending_expected.capacity()
            + state.pending_actual.capacity(),
        0
    );
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original poison stop"
    );
    assert!(observer.events.len() > stop + 6);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn later_global_name_copy_refusal_keeps_an_exact_owned_utf8_prefix() {
    let name = "λ".repeat(3000);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.alignment(&name, 0, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    // The first growth and first copy both charge1024. The third such event
    // is the second actual copy, with first1024 bytes already retained.
    let stop = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == 1024 && e.copy_bytes == 1024)
        .nth(2)
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
        state.alignment(&name, 0, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.pending_location, "λ".repeat(512));
    assert!(
        state.pending_expected.is_empty()
            && state.pending_actual.is_empty()
            && state.errors.is_empty()
    );
    state.retire_scratch(&mut work);
    assert_eq!(state.pending_location.capacity(), 0);
}

#[test]
fn borrowed_inline_types_continuations_and_prior_owned_error_survive_a_late_stop() {
    let mut module = Module::new("retained");
    module.functions.push(function(
        "F",
        vec![],
        vec![Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: Ty::Error,
            dst_ty: Ty::Tuple(vec![Ty::Bool; 32]),
            operand: ValueId::new(0),
        }],
    ));
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.functions(&module, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let mut saw_retained = false;
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
        let result = state.functions(&module, &mut work);
        if result.is_err()
            && state.types.len() == 2
            && !state.frames.is_empty()
            && state.errors.len() == 1
        {
            saw_retained = true;
            let Inst::Cast { src_ty, dst_ty, .. } = &module.functions[0].blocks[0].body[0].inst
            else {
                unreachable!()
            };
            assert!(core::ptr::eq(state.types[0], src_ty));
            assert!(core::ptr::eq(state.types[1], dst_ty));
            assert_eq!(
                state.errors[0],
                poison("function 'F' bb42 instruction 0 (cast)")
            );
        }
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert_eq!(
            state.types.capacity() + state.frames.capacity() + state.errors.capacity(),
            0
        );
        assert!(
            state.location.is_empty()
                && state.attribute.is_empty()
                && state.pending_location.is_empty()
        );
    }
    assert!(saw_retained);
}

#[test]
fn actual_tuple_interior_refusal_never_publishes_a_smaller_census() {
    let mut module = Module::new("interior");
    module.types.push(Ty::Tuple(vec![Ty::Error; 4096]));
    let mut observer = Observer {
        work_cap: Some(1000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_module_error_types_observed(&module, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert!(
        observer
            .events
            .iter()
            .all(|e| e.phase != ExecutionPhase::Publication)
    );
}

#[test]
fn final_publication_retires_each_actual_string_and_post_drop_refusal_cannot_resume() {
    let module = fixture();
    let (_, baseline) = observed(&module);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_module_error_types_observed(&module, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    //20 three-string poison errors (8callbacks each), one one-string align
    // error (4callbacks), final result buffer pre/post deallocation (2).
    assert!(observer.events.len() >= stop + 20 * 8 + 4 + 2);
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
        "original poison stop"
    );
}
