// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_actual_callback_refuses_without_partial_diagnostics_and_preserves_cause() {
    let m = fixture();
    let (_, baseline) = run(&m);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_module_result_arities_observed(&m, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original count stop"
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
fn original_cumulative_work_and_copy_budgets_span_repeated_whole_walks() {
    let m = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    validate_module_result_arities_observed(&m, &mut session, site()).unwrap();
    validate_module_result_arities_observed(&m, &mut session, site()).unwrap();
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        validate_module_result_arities_observed(&m, &mut session, site()).unwrap();
        assert_eq!(
            validate_module_result_arities_observed(&m, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(
            validate_module_result_arities_observed(&m, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}

#[test]
fn first_static_token_storage_refuses_before_any_allocation() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut text = String::new();
    assert_eq!(
        work.token("landingpad", &mut text),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((text.len(), text.capacity()), (0, 0));
    work.retire(text);
}

#[test]
fn complete_opcode_stays_pending_when_first_error_vector_storage_is_refused() {
    let instruction = Inst::LandingPad {
        is_cleanup: true,
        catch_type_indices: vec![],
    };
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    state
        .diagnostic(
            7,
            &instruction,
            2,
            1,
            &mut Work {
                session: &mut session,
                site: site(),
            },
        )
        .unwrap();
    // Final validation events are fixed enum construction then first Vec
    // storage; select by relative position, never an ambiguous size match.
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
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.diagnostic(7, &instruction, 2, 1, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.op, "landingpad");
    assert_eq!((state.errors.len(), state.errors.capacity()), (0, 0));
    work.retire(take(&mut state.op));
    state.retire_errors(&mut work);
    assert_eq!(state.op.capacity(), 0);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original count stop"
    );
}

#[test]
fn actual_sparse_lookup_interior_stop_is_not_zero_result_count_or_a_partial_success() {
    let mut m = Module::new("lookup");
    for id in 0..100 {
        m.functions.push(Function::new(
            FuncId::new(id),
            "other",
            FuncTyId::new(0),
            b(0),
        ));
    }
    let instruction = Inst::Call {
        callee: FuncId::new(999),
        args: vec![],
    };
    let mut observer = Observer {
        work_cap: Some(70),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        count::expected(
            &instruction,
            &m,
            &mut Work {
                session: &mut session,
                site: site()
            }
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert!(observer.events.len() < 10);
}

#[test]
fn final_publication_refusal_retires_all_completed_owned_opcode_fields() {
    let m = fixture();
    let (_, baseline) = run(&m);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_module_result_arities_observed(&m, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert_eq!(observer.events.len(), stop + 4 * 3 + 2);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn first_scratch_retirement_refusal_cannot_publish_complete_diagnostics() {
    let m = fixture();
    let (_, baseline) = run(&m);
    let stop = baseline
        .events
        .iter()
        .position(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_module_result_arities_observed(&m, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
    assert!(
        observer
            .events
            .iter()
            .all(|e| e.phase != ExecutionPhase::Publication)
    );
    assert!(observer.events.len() > stop + 4);
}

#[test]
fn wide_actual_node_walk_refuses_interiorly_and_retires_all_accumulated_opcodes() {
    let m = module(
        (0..4096)
            .map(|_| node(Inst::Undef { ty: Ty::U32 }, 0))
            .collect(),
    );
    let mut observer = Observer {
        work_cap: Some(5000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.walk(&m, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(!state.errors.is_empty() && state.errors.len() < 4096);
    work.retire(take(&mut state.op));
    state.retire_errors(&mut work);
    assert_eq!((state.errors.len(), state.errors.capacity()), (0, 0));
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
}
