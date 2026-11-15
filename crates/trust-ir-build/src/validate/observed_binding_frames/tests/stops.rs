// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

fn with_edge() -> Function {
    let mut f = fixture();
    f.blocks[0].body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![v(1)],
    }));
    let mut target = Block::new(b(1));
    target.params.push((v(20), Ty::Ptr));
    target.body.push(load(20, 0, Ty::I32));
    f.blocks.push(target);
    f
}
fn pipeline<'a, O: ExecutionObserver>(
    state: &mut State<'a>,
    f: &'a Function,
    work: &mut Work<'_, '_, O>,
) -> R {
    state.collect(f, work)?;
    state.propagate(f, work)?;
    state.count_opens(f, work)?;
    state.uses(f, work)?;
    state.unclosed(f, work)
}
fn empty(state: &State<'_>) -> bool {
    state.declarations.capacity() == 0
        && state.flow.storage_empty()
        && state.opens.capacity() == 0
        && state.closes.capacity() == 0
        && state.actual_type.is_none()
        && state.expected.capacity() == 0
        && state.actual.capacity() == 0
        && state.errors.capacity() == 0
}

#[test]
fn every_actual_callback_keeps_the_original_cause_and_only_retires_after_refusal() {
    let f = with_edge();
    let (_, baseline) = run(&f);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_binding_frames_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original frame stop"
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
fn repeated_whole_frame_passes_do_not_renew_original_work_or_copy_caps() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for _ in 0..2 {
        assert_eq!(
            validate_function_binding_frames_observed(&f, &mut session, site())
                .unwrap()
                .len(),
            6
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
            validate_function_binding_frames_observed(&f, &mut session, site())
                .unwrap()
                .len(),
            6
        );
        assert_eq!(
            validate_function_binding_frames_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(
            validate_function_binding_frames_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}

#[test]
fn sorted_rows_are_admitted_before_the_first_allocation() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut rows = Vec::<(u32, u32)>::new();
    assert_eq!(
        work.reserve(&mut rows),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((rows.len(), rows.capacity()), (0, 0));
    assert_eq!(work.session.first_refusal().unwrap().cause, "bytes");
}

#[test]
fn actual_edges_query_types_sorted_rows_strings_and_prior_errors_retain_custody() {
    let f = with_edge();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    pipeline(&mut state, &f, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let (mut rows, mut analysis, mut edges, mut ty, mut text, mut errors) =
        (false, false, false, false, false, false);
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
        if pipeline(&mut state, &f, &mut work).is_err() {
            rows |= state.flow.has_rows() && !state.declarations.is_empty();
            analysis |= state.flow.has_analysis();
            edges |= state.flow.has_edges();
            ty |= state.actual_type.is_some();
            text |= !state.expected.is_empty();
            errors |= !state.errors.is_empty();
        }
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert!(empty(&state));
    }
    assert!(rows && analysis && edges && ty && text && errors);
}

#[test]
fn diagnostic_growth_refusal_preserves_both_complete_pending_type_strings() {
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
        expected: "expected tuple".into(),
        actual: "actual integer".into(),
        ..State::default()
    };
    assert_eq!(
        state.type_error(uses::Access::Write, 0, 7, 1, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.expected, "expected tuple");
    assert_eq!(state.actual, "actual integer");
    assert_eq!(state.errors.capacity(), 0);
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
}

#[test]
fn an_interrupted_sorted_insertion_retires_even_its_partially_permuted_rows() {
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut rows = vec![(2u32, 2u32), (4, 4)];
    assert!(work.set(&mut rows, 1, 1).unwrap());
    assert_eq!(rows, vec![(1, 1), (2, 2), (4, 4)]);
    let mut partial = false;
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
        let mut rows = vec![(2u32, 2u32), (4, 4)];
        if work.set(&mut rows, 1, 1).is_err() {
            partial |= rows.iter().any(|row| row.0 == 1)
                && rows.windows(2).any(|pair| pair[0].0 > pair[1].0);
        }
        work.drain(&mut rows);
        assert_eq!(rows.capacity(), 0);
    }
    assert!(partial);
}

#[test]
fn final_publication_refusal_drains_every_completed_nested_diagnostic() {
    let f = fixture();
    let (_, baseline) = run(&f);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_binding_frames_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > stop + 12);
    assert!(
        observer.events[stop..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn same_session_cleanup_refusal_drains_all_owning_stores_and_denies_publication() {
    let f = with_edge();
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
    pipeline(&mut state, &f, &mut work).unwrap();
    assert!(!state.errors.is_empty());
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
        "original frame cleanup stop"
    );
}

#[test]
fn frame_count_overflow_is_typed_before_wrapping_or_replacing_the_original_count() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut rows = vec![(7, u32::MAX)];
    assert_eq!(
        work.increment(&mut rows, 7),
        Err(ObservedValueError::CapacityOverflow)
    );
    assert_eq!(rows, vec![(7, u32::MAX)]);
    assert!(work.session.first_refusal().is_none());
    work.drain(&mut rows);
    assert_eq!(rows.capacity(), 0);
}

#[test]
fn even_empty_retained_text_is_refused_before_an_implicit_overwrite() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        expected: String::with_capacity(4),
        ..State::default()
    };
    assert_eq!(
        State::text_ready(&state.expected, &state.actual, &mut work),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(state.expected.capacity() >= 4);
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
}

#[test]
fn ordinary_wrapper_reports_analysis_failure_without_swallowing_it() {
    for error in [
        ObservedValueError::InvalidRange,
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
    ] {
        let reason = error.to_string();
        assert_eq!(
            ordinary_result(Err(error)),
            vec![ValidationError::BindingFrameAnalysisFailed { reason }]
        );
    }
}

#[test]
fn flat_flow_storage_admits_before_allocation_and_preserves_owned_state_on_stop() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut rows = Vec::<u8>::new();
    assert_eq!(
        work.resize(&mut rows, 32, 0),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((rows.len(), rows.capacity()), (0, 0));
    assert_eq!(work.session.first_refusal().unwrap().cause, "bytes");
    work.drain(&mut rows);
}

#[test]
fn cyclic_flow_refusal_retains_the_original_stop_and_retires_its_fixed_point_state() {
    let mut f = function(vec![InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![],
    })]);
    let mut header = Block::new(b(1));
    header.body = vec![
        open(0, vec![], 1),
        close(1),
        InstrNode::new(Inst::CondBr {
            cond: v(11),
            then_target: b(1),
            then_args: vec![],
            else_target: b(2),
            else_args: vec![],
        }),
    ];
    f.blocks.push(header);
    f.blocks.push(Block::new(b(2)));
    let (_, baseline) = run(&f);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_binding_frames_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original frame stop"
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
fn flow_storage_size_overflow_is_typed_before_allocation() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut rows = Vec::<u64>::new();
    assert_eq!(
        work.resize(&mut rows, usize::MAX, 0),
        Err(ObservedValueError::CapacityOverflow)
    );
    assert_eq!((rows.len(), rows.capacity()), (0, 0));
    assert!(work.session.first_refusal().is_none());
}
