// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
fn empty(state: &State) -> bool {
    state.op.capacity() == 0
        && state.reason.capacity() == 0
        && state.spelling.capacity() == 0
        && state.errors.capacity() == 0
}

#[test]
fn every_actual_callback_in_both_element_families_stops_without_resumed_work() {
    let module = module();
    let sequence = Ty::Sequence(TyId::new(0));
    for (function, context) in [
        (failing(), None),
        (
            fixture(Kind::Extract, Some(sequence), Some(Ty::I32), None, Ty::F32),
            Some(&module),
        ),
    ] {
        let values = values(&function, context);
        let rows = [(1, -1)];
        let (_, baseline) = run(&function, &rows, context);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                validate_element_operands_observed(
                    0,
                    subject(&function),
                    &values,
                    &rows,
                    context,
                    &mut session,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original element stop"
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
fn cumulative_work_and_copy_caps_cover_repeated_components_and_remain_sticky() {
    let function = failing();
    let values = values(&function, None);
    let rows = [(1, -1)];
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for _ in 0..2 {
        assert_eq!(
            validate_element_operands_observed(
                0,
                subject(&function),
                &values,
                &rows,
                None,
                &mut session,
                site()
            )
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
            validate_element_operands_observed(
                0,
                subject(&function),
                &values,
                &rows,
                None,
                &mut session,
                site()
            )
            .unwrap()
            .len(),
            4
        );
        assert_eq!(
            validate_element_operands_observed(
                0,
                subject(&function),
                &values,
                &rows,
                None,
                &mut session,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(
            validate_element_operands_observed(
                0,
                subject(&function),
                &values,
                &rows,
                None,
                &mut session,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
    }
}

#[test]
fn diagnostic_storage_refusal_happens_before_any_pending_string_moves() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        op: "extract_element".into(),
        reason: "pending reason".into(),
        ..State::default()
    };
    assert_eq!(
        state.commit(0, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        (&*state.op, &*state.reason),
        ("extract_element", "pending reason")
    );
    assert_eq!(state.errors.capacity(), 0);
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
}

#[test]
fn actual_returned_long_spelling_and_partial_utf8_reason_are_retained_until_cleanup() {
    let ty = Ty::Handle(Box::new(HandleTy::new("λ".repeat(1800), "runtime")));
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state
        .wrong_kind(0, "extract_element", &ty, &mut work)
        .unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    // Direct wrong_kind and direct replay have the same header-free entry.
    // Find the second actual bounded reason copy AFTER the type formatter
    // returned at its own Publication, excluding all formatter-internal work.
    let publication = baseline
        .events
        .iter()
        .position(|event| event.phase == ExecutionPhase::Publication)
        .unwrap();
    let copies = baseline
        .events
        .iter()
        .enumerate()
        .skip(publication + 1)
        .filter(|(_, event)| {
            event.copy_bytes > 0 && event.copy_bytes <= 1024 && event.work == event.copy_bytes
        })
        .collect::<Vec<_>>();
    assert!(copies.len() >= 2);
    let first_copy = copies[0].1.copy_bytes;
    let stop = copies[1].0 + 1;
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
        state.wrong_kind(0, "extract_element", &ty, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.spelling.len() > 3000);
    assert_eq!(
        state.reason.len(),
        "operand must be vector, array or sequence, got ".len() + first_copy
    );
    assert_eq!(
        &state.reason["operand must be vector, array or sequence, got ".len()..],
        &state.spelling[..first_copy]
    );
    assert!(state.reason.is_char_boundary(state.reason.len()));
    assert!(state.errors.is_empty());
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original element stop"
    );
}

#[test]
fn completed_diagnostics_remain_owned_at_every_later_direct_state_refusal() {
    let function = failing();
    let values = values(&function, None);
    let rows = [(1, -1)];
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state
        .check(0, subject(&function), &values, &rows, None, &mut work)
        .unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let mut prior_output = false;
    let mut pending_text = false;
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
        if state
            .check(0, subject(&function), &values, &rows, None, &mut work)
            .is_err()
        {
            prior_output |= !state.errors.is_empty();
            pending_text |= !state.reason.is_empty();
        }
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert!(empty(&state));
    }
    assert!(prior_output && pending_text);
}

#[test]
fn real_constant_row_scan_and_deep_structural_comparison_have_interior_stops() {
    let function = fixture(
        Kind::Extract,
        Some(Ty::Vector(Box::new(Ty::U32), 3)),
        Some(Ty::U32),
        None,
        Ty::U32,
    );
    let row_values = values(&function, None);
    let rows = std::iter::once((1, -1))
        .chain((100..50_100).map(|key| (key, 0)))
        .collect::<Vec<_>>();
    let mut observer = Observer {
        work_cap: Some(1000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_element_operands_observed(
            0,
            subject(&function),
            &row_values,
            &rows,
            None,
            &mut session,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert!(observer.events.len() < 2000);
    let mut function = fixture(
        Kind::Extract,
        Some(Ty::Vector(Box::new(Ty::Tuple(vec![Ty::U32; 5000])), 3)),
        None,
        None,
        Ty::Tuple(vec![Ty::U32; 5000]),
    );
    if let Inst::ExtractElement {
        ty: Ty::Tuple(fields),
        ..
    } = &mut function.blocks[0].body[0].inst
    {
        fields[4999] = Ty::I32;
    }
    let deep_values = values(&function, None);
    let mut observer = Observer {
        work_cap: Some(1000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_element_operands_observed(
            0,
            subject(&function),
            &deep_values,
            &[],
            None,
            &mut session,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
}

#[test]
fn final_publication_and_cleanup_refusals_consume_all_completed_errors() {
    let function = failing();
    let values = values(&function, None);
    let rows = [(1, -1)];
    let (_, baseline) = run(&function, &rows, None);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_element_operands_observed(
            0,
            subject(&function),
            &values,
            &rows,
            None,
            &mut session,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > stop + 10);
    assert!(
        observer.events[stop..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
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
    state
        .check(0, subject(&function), &values, &rows, None, &mut work)
        .unwrap();
    assert_eq!(state.errors.len(), 4);
    arm.set(true);
    state.retire_scratch(&mut work);
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = work.session.first_refusal().unwrap().progress;
    state.retire_errors(&mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original element cleanup"
    );
    assert_eq!(work.session.first_refusal().unwrap().progress, first);
}

#[test]
fn initial_header_refusal_publishes_nothing_and_never_allocates_local_scratch() {
    let function = failing();
    let values = values(&function, None);
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_element_operands_observed(
            0,
            subject(&function),
            &values,
            &[],
            None,
            &mut session,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "bytes");
    assert_eq!(observer.events.len(), 1);
    assert_eq!(observer.events[0].phase, ExecutionPhase::Validation);
}
