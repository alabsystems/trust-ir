// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_returned_semantic_error_is_retained_before_prefix_allocation_and_copy() {
    const PREFIX: &str = "cannot derive semantic_body_digest: ";
    let mut module = module();
    module.functions[0]
        .source_provenance
        .as_mut()
        .unwrap()
        .binding_digest = ProofDigest::zero();
    let missing = Module::new("missing");
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state
        .walk(&module.functions[0], Some(&missing), &mut work)
        .unwrap();
    retire(&mut state, &mut work);
    let event = |e: &ExecutionProgress| {
        e.phase == ExecutionPhase::Validation
            && e.work == PREFIX.len()
            && e.copy_bytes == PREFIX.len()
    };
    let pairs: Vec<_> = measured
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, p)| event(&p[0]) && event(&p[1]))
        .map(|(i, _)| i)
        .collect();
    assert_eq!(pairs.len(), 1);
    // The first event is String growth, the SECOND is its actual prefix copy.
    let copy_ordinal = pairs[0] + 2;
    for stop in [copy_ordinal, copy_ordinal + 1] {
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
            state.walk(&module.functions[0], Some(&missing), &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.errors.len(), 2);
        assert_eq!(
            state.pending,
            "source provenance target function #161 is missing or duplicated"
        );
        assert!(state.detail.capacity() >= PREFIX.len());
        assert_eq!(state.detail, if stop == copy_ordinal { "" } else { PREFIX });
        let first = work.session.first_refusal().unwrap().progress;
        assert_eq!(first, measured.events[stop - 1]);
        retire(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(work.session.first_refusal().unwrap().progress, first);
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original provenance stop"
        );
    }
}
#[test]
fn actual_unicode_debug_formatter_stops_inside_owned_partial_text_without_earlier_equality() {
    let name = "λ".repeat(5000);
    let expected = format!("source loop 0 bindings are not strictly name-sorted at {name:?}");
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
        state.unsorted(161, 0, &name, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(
        state
            .detail
            .starts_with("source loop 0 bindings are not strictly name-sorted at \"λ")
    );
    assert!(state.detail.len() < expected.len());
    assert!(!state.detail.ends_with('"'));
    assert!(state.errors.is_empty());
    let first = work.session.first_refusal().unwrap().progress;
    retire(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().progress, first);
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
    assert!(
        observer
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Validation && e.work == 8 * u32::BITS as usize)
            .count()
            > 3
    );
}
#[test]
fn diagnostic_growth_and_final_header_admission_keep_owned_detail_before_move() {
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        detail: "owned pending detail".into(),
        pending: "owned semantic detail".into(),
        ..State::default()
    };
    state.commit(161, &mut work).unwrap();
    retire(&mut state, &mut work);
    let admissions: Vec<_> = measured
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(admissions.len(), 2);
    assert_eq!(admissions[1], admissions[0] + 1);
    for (position, stop) in admissions.into_iter().enumerate() {
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
            detail: "owned pending detail".into(),
            pending: "owned semantic detail".into(),
            ..State::default()
        };
        assert_eq!(
            state.commit(161, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, position == 0);
        assert_eq!(state.detail, "owned pending detail");
        assert_eq!(state.pending, "owned semantic detail");
        retire(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original provenance stop"
        );
    }
}
#[test]
fn refused_cleanup_prices_long_owned_text_and_consumes_actual_edges_tree_names_and_errors() {
    let module = module();
    let function = &module.functions[0];
    let missing = Module::new("missing");
    let long_detail = "λ".repeat(5000);
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.walk(function, None, &mut work).unwrap();
    assert!(
        state.dominators.is_some() && !state.global_names.is_empty() && !state.errors.is_empty()
    );
    state.pending = missing
        .source_provenance_semantic_digest_observed(function.id, work.session, work.site)
        .unwrap()
        .unwrap_err();
    state.edges = function.blocks[0].body[0]
        .inst
        .successor_edges_observed(work.session, work.site)
        .unwrap();
    assert!(!state.edges.is_empty());
    state.detail = long_detail;
    let work_before_drop = state.detail.len() + size_of::<String>() + 1;
    arm.set(true);
    state.retire_scratch(&mut work);
    assert!(
        state.dominators.is_none()
            && state.edges.capacity() == 0
            && state.global_names.capacity() == 0
    );
    assert_eq!(state.detail.capacity(), 0);
    assert_eq!(state.pending.capacity(), 0);
    let first = work.session.first_refusal().unwrap().progress;
    assert_eq!(first.phase, ExecutionPhase::ScratchRetirement);
    assert_eq!(first.work, work_before_drop);
    assert_eq!(first.copy_bytes, 0);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
    assert!(empty(&state));
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(work.session.first_refusal().unwrap().progress, first);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original provenance cleanup"
    );
}
#[test]
fn final_publication_refusal_consumes_complete_output_after_all_analysis_scratch() {
    let module = module();
    let (_, baseline) = run(&module.functions[0], None);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_source_provenance_observed(
            &module.functions[0],
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
    assert_eq!(
        session.first_refusal().unwrap().progress.copy_bytes,
        size_of::<Vec<ValidationError>>()
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
