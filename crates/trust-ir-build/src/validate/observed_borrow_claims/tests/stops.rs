// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
mod custody;

#[test]
fn every_public_callback_refuses_without_partial_diagnostics_or_a_new_original_scope() {
    let mut f = fixture();
    f.producer = Some(Producer::TRust);
    f.blocks[0].body.push(node(
        Inst::Br {
            target: b(1),
            args: vec![v(1)],
        },
        &[],
    ));
    let mut target = Block::new(b(1)).with_param(v(7), Ty::Ptr);
    target.body.push(node(Inst::BorrowMut { ptr: v(7) }, &[8]));
    f.blocks.push(target);
    let (_, baseline, prefix) = run(&f, None);
    for stop in prefix + 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let types =
            super::super::super::build_function_value_types_observed(&f, &mut session, site())
                .unwrap();
        assert_eq!(
            validate_function_borrow_structure_observed(&f, &types, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().progress,
            baseline.events[stop - 1]
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original claim stop"
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
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    validate_function_rust_reference_spelling_observed(&f, &mut session, site()).unwrap();
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_rust_reference_spelling_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().progress,
            baseline.events[stop - 1]
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original claim stop"
        );
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn original_cumulative_work_and_copy_budgets_span_map_borrow_and_reference_components() {
    let mut f = fixture();
    f.producer = Some(Producer::TRust);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let types =
        super::super::super::build_function_value_types_observed(&f, &mut session, site()).unwrap();
    validate_function_borrow_structure_observed(&f, &types, &mut session, site()).unwrap();
    validate_function_rust_reference_spelling_observed(&f, &mut session, site()).unwrap();
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let types =
            super::super::super::build_function_value_types_observed(&f, &mut session, site())
                .unwrap();
        validate_function_borrow_structure_observed(&f, &types, &mut session, site()).unwrap();
        assert_eq!(
            validate_function_rust_reference_spelling_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(
            validate_function_borrow_structure_observed(&f, &types, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}

#[test]
fn first_definition_incoming_stack_and_name_storage_are_refused_before_allocation() {
    let f = fixture();
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
        state.need_definitions(&f, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.definitions.is_none());
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
        state.need_incoming(&f, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.incoming.is_none());
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
        state.trace(v(1), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((state.stack.len(), state.stack.capacity()), (0, 0));
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
        state.reference("λ", 1, 2, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((state.name.len(), state.name.capacity()), (0, 0));
    state.retire_scratch(&mut work);
}

#[test]
fn actual_definition_collection_stops_interiorly_and_never_marks_a_partial_result_complete() {
    let f = function(
        (0..5000)
            .map(|i| node(Inst::Undef { ty: Ty::Ptr }, &[i]))
            .collect(),
    );
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
        state.need_definitions(&f, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    let length = state.definitions.as_ref().unwrap().len();
    assert!(length > 0 && length < 5000);
    state.retire_scratch(&mut work);
    assert!(state.definitions.is_none());
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
}

#[test]
fn final_publication_and_same_observer_cleanup_refusal_cannot_publish_owned_errors() {
    let mut f = fixture();
    f.producer = Some(Producer::TRust);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    validate_function_rust_reference_spelling_observed(&f, &mut session, site()).unwrap();
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_rust_reference_spelling_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() >= stop + 4 * 4 + 2);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        retire_stop: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let types =
        super::super::super::build_function_value_types_observed(&f, &mut session, site()).unwrap();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.borrows(&f, &types, &mut work).unwrap();
    assert!(state.definitions.is_some() && state.incoming.is_some() && !state.errors.is_empty());
    arm.set(true); // Tighten the same original observer only, no renewed grant.
    assert_eq!(
        state.finish(Ok(()), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.definitions.is_none() && state.incoming.is_none());
    assert_eq!(state.errors.capacity() + state.name.capacity(), 0);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original claim retirement"
    );
}
