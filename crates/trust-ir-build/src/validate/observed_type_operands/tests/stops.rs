// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_actual_basic_operand_callback_refuses_and_only_cleanup_follows() {
    let function = fixture();
    let values = values(&function, None);
    let (_, baseline) = run(&function, None);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_instruction_basic_type_operands_observed(
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
            session.first_refusal().unwrap().cause,
            "original operand stop"
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

#[test]
fn two_instruction_components_share_original_cumulative_work_and_copy_caps() {
    let function = fixture();
    let values = values(&function, None);
    let inst = &function.blocks[0].body[0].inst;
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for _ in 0..2 {
        assert_eq!(
            validate_instruction_basic_type_operands_observed(
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
            validate_instruction_basic_type_operands_observed(
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
            validate_instruction_basic_type_operands_observed(
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
            validate_instruction_basic_type_operands_observed(
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
fn all_four_strings_remain_owned_if_diagnostic_allocation_is_refused() {
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
        op: "copy".into(),
        role: "operand".into(),
        expected: "u32".into(),
        actual: "i32".into(),
        ..State::default()
    };
    assert_eq!(
        state.commit(Diagnostic::Operand(0), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        (&*state.op, &*state.role, &*state.expected, &*state.actual),
        ("copy", "operand", "u32", "i32")
    );
    assert_eq!(state.errors.capacity(), 0);
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
}

fn empty(state: &State) -> bool {
    state.op.capacity() == 0
        && state.role.capacity() == 0
        && state.expected.capacity() == 0
        && state.actual.capacity() == 0
        && state.errors.capacity() == 0
}

#[test]
fn actual_pending_text_and_completed_errors_survive_every_later_stop_until_cleanup() {
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
    let (mut pending, mut completed) = (false, false);
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
            pending |= !state.op.is_empty() || !state.actual.is_empty();
            completed |= !state.errors.is_empty();
        }
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert!(empty(&state));
    }
    assert!(pending && completed);
}

#[test]
fn final_publication_refusal_consumes_every_completed_nested_string() {
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
        validate_instruction_basic_type_operands_observed(
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
}

#[test]
fn retirement_refusal_finishes_drain_and_denies_same_session_publication() {
    let function = fixture();
    let values = values(&function, None);
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
        "original operand cleanup"
    );
}

#[test]
fn bounded_utf8_copy_stops_after_a_nonempty_prefix_without_renewing_storage() {
    let input = "λ".repeat(10_000);
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
    assert_eq!(
        work.text(&input, &mut state.actual),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(!state.actual.is_empty() && state.actual.len() < input.len());
    assert!(input.starts_with(&state.actual));
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
}

#[test]
fn gep_index_iteration_refuses_interiorly_instead_of_returning_a_partial_clean_result() {
    let function = f(Inst::GEP {
        pointee_ty: Ty::U32,
        base: v(0),
        indices: vec![v(1); 5000],
        inbounds: false,
    });
    let values = values(&function, None);
    let mut observer = Observer {
        work_cap: Some(300),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_instruction_basic_type_operands_observed(
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
    assert!(observer.events.len() < 300);
}

#[test]
fn a_retained_empty_string_capacity_is_never_silently_overwritten() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        actual: String::with_capacity(5),
        ..State::default()
    };
    assert_eq!(
        state.ready(&mut work),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(
        work.spelling(&Ty::U32, &mut state.actual),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(state.actual.capacity() >= 5);
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
}
