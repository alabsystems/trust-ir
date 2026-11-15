// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
fn empty(state: &State) -> bool {
    state.op.capacity() == 0
        && state.role.capacity() == 0
        && state.expected.capacity() == 0
        && state.actual.capacity() == 0
        && state.errors.capacity() == 0
}

#[test]
fn every_actual_numeric_callback_refuses_and_only_original_retirement_follows() {
    let module = module();
    for (function, context) in [
        (fixture(), None),
        (
            f(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U32,
                lhs: v(6),
                rhs: v(8),
            }),
            Some(&module),
        ),
    ] {
        let values = values(&function, context);
        let (_, baseline) = run(&function, context);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                validate_instruction_numeric_type_operands_observed(
                    0,
                    &function.blocks[0].body[0].inst,
                    &values,
                    context,
                    &mut session,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original numeric stop"
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
fn cumulative_numeric_work_and_copy_budgets_are_not_renewed_between_components() {
    let function = fixture();
    let values = values(&function, None);
    let inst = &function.blocks[0].body[0].inst;
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for _ in 0..2 {
        assert_eq!(
            validate_instruction_numeric_type_operands_observed(
                0,
                inst,
                &values,
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
            validate_instruction_numeric_type_operands_observed(
                0,
                inst,
                &values,
                None,
                &mut session,
                site()
            )
            .unwrap()
            .len(),
            4
        );
        assert_eq!(
            validate_instruction_numeric_type_operands_observed(
                0,
                inst,
                &values,
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
            validate_instruction_numeric_type_operands_observed(
                0,
                inst,
                &values,
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
fn diagnostic_storage_is_admitted_before_moving_any_pending_string() {
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
        op: "add".into(),
        role: "lhs".into(),
        expected: "f32".into(),
        actual: "i32".into(),
        ..State::default()
    };
    assert_eq!(
        state.commit(Diagnostic::Operand(0), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        (&*state.op, &*state.role, &*state.expected, &*state.actual),
        ("add", "lhs", "f32", "i32")
    );
    assert_eq!(state.errors.capacity(), 0);
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
}

#[test]
fn actual_pending_spelling_and_prior_diagnostics_retain_custody_at_every_later_stop() {
    let function = fixture();
    let values = values(&function, None);
    let inst = &function.blocks[0].body[0].inst;
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.check(0, inst, &values, None, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let (mut text, mut completed) = (false, false);
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
        if state.check(0, inst, &values, None, &mut work).is_err() {
            text |= !state.expected.is_empty() && !state.actual.is_empty();
            completed |= !state.errors.is_empty();
        }
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert!(empty(&state));
    }
    assert!(text && completed);
}

#[test]
fn final_publication_and_same_session_cleanup_refusals_drain_complete_outputs() {
    let function = fixture();
    let values = values(&function, None);
    let (_, baseline) = run(&function, None);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_instruction_numeric_type_operands_observed(
            0,
            &function.blocks[0].body[0].inst,
            &values,
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
    assert!(observer.events.len() > stop + 20);
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
        .check(
            0,
            &function.blocks[0].body[0].inst,
            &values,
            None,
            &mut work,
        )
        .unwrap();
    assert_eq!(state.errors.len(), 4);
    arm.set(true);
    state.retire_scratch(&mut work);
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    state.retire_errors(&mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original numeric cleanup"
    );
}

#[test]
fn nested_actual_equality_and_spelling_cannot_publish_partial_results_on_interior_stop() {
    let mut function = f(Inst::UnOp {
        op: UnOp::Neg,
        ty: Ty::Tuple(vec![Ty::U32; 5000]),
        operand: v(0),
    });
    function.blocks[0].params[0].1 =
        Ty::Tuple(vec![Ty::U32; 4999].into_iter().chain([Ty::I32]).collect());
    let values = values(&function, None);
    let mut observer = Observer {
        work_cap: Some(10_000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_instruction_numeric_type_operands_observed(
            0,
            &function.blocks[0].body[0].inst,
            &values,
            None,
            &mut session,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert!(observer.events.len() < 30_000);
}

#[test]
fn actual_numeric_diagnostic_spelling_stops_inside_wide_unicode_and_keeps_other_fields_owned() {
    let expected = Ty::Handle(Box::new(HandleTy::new("λ".repeat(6000), "runtime")));
    let mut observer = Observer {
        work_cap: Some(5000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    // Enter the actual helper used after a numeric mismatch. No equality
    // prewalk can consume this cap before the real formatter is entered.
    assert_eq!(
        state.mismatch(
            Diagnostic::Operand(0),
            "neg",
            Some("operand"),
            &expected,
            &Ty::I32,
            &mut work
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.op, "neg");
    assert_eq!(state.role, "operand");
    assert_eq!(state.expected.capacity(), 0);
    assert!(state.errors.is_empty());
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
    assert!(
        observer
            .events
            .iter()
            // Real scalar classification now prepays the complete pinned Unicode
            // table bound as well as the fixed scalar guards. Observe both
            // actual classifications, including the one refused by the cap.
            .filter(|event| event.phase == ExecutionPhase::Validation
                && event.copy_bytes == size_of::<core::char::EscapeDebug>()
                && event.work >= 8 * u32::BITS as usize)
            .count()
            >= 2
    );
    assert!(
        observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
