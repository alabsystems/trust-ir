// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_real_original_callback_refuses_without_partial_diagnostics_or_resumed_work() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    for (index, expected) in baseline.events.into_iter().enumerate() {
        let mut observer = Observer {
            stop: Some(index + 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_standalone_refinements_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, expected);
        assert_eq!(session.first_refusal().unwrap().cause, "original stop");
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
fn original_cumulative_work_and_memory_caps_include_repeated_full_traversal_and_text() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work),
            byte_cap: bytes.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_standalone_refinements_observed(&f, &mut session, site()).unwrap(),
            validate_standalone_refinement_surface(&f)
        );
        assert_eq!(
            validate_function_standalone_refinements_observed(&f, &mut session, site()),
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
fn first_borrowed_frame_and_name_storage_refuse_before_any_allocation() {
    let ty = refined();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    assert_eq!(
        state.contains(&ty, &mut work),
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
    let mut text = String::new();
    assert_eq!(
        work.text("λ", &mut text),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((text.len(), text.capacity()), (0, 0));
    work.retire(text);
}

#[test]
fn complete_owned_location_and_detail_survive_first_error_vector_growth_refusal() {
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    state
        .diagnostic("λ", 7, Surface::Parameter(11), &mut work)
        .unwrap();
    // Direct construction baseline and replay match. The last two events are
    // first error-vector storage and fixed-enum construction respectively.
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let stop = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| event.phase == ExecutionPhase::Validation)
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
    let mut state = Checking::default();
    assert_eq!(
        state.diagnostic("λ", 7, Surface::Parameter(11), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.location, "function 'λ' bb7 param 11");
    assert_eq!(state.detail, DETAIL);
    assert_eq!((state.errors.len(), state.errors.capacity()), (0, 0));
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert_eq!((state.location.len(), state.location.capacity()), (0, 0));
    assert_eq!((state.detail.len(), state.detail.capacity()), (0, 0));
    assert_eq!(work.session.first_refusal().unwrap().cause, "original stop");
    assert!(observer.events.len() > stop + 2);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn actual_tuple_interior_cancellation_is_never_a_false_predicate_answer() {
    let ty = Ty::Tuple(vec![Ty::Bool; 4096]);
    let mut observer = Observer {
        stop: Some(200),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    assert_eq!(
        state.contains(&ty, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(work.session.first_refusal().unwrap().cause, "original stop");
    state.retire_scratch(&mut work);
    assert_eq!(state.frames.capacity(), 0);
}

#[test]
fn returned_inline_borrows_and_pending_frames_survive_late_predicate_refusal() {
    let f = function(
        "retained",
        vec![block(
            0,
            vec![],
            vec![cast(refined(), Ty::Tuple(vec![Ty::Bool; 32]))],
        )],
    );
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    state.walk(&f, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let mut saw_owned = false;
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
        let mut state = Checking::default();
        let result = state.walk(&f, &mut work);
        if result.is_err() && state.types.len() == 2 && !state.frames.is_empty() {
            saw_owned = true;
            let Inst::Cast { src_ty, dst_ty, .. } = &f.blocks[0].body[0].inst else {
                unreachable!()
            };
            assert!(core::ptr::eq(state.types[0], src_ty));
            assert!(core::ptr::eq(state.types[1], dst_ty));
        }
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert_eq!((state.types.len(), state.types.capacity()), (0, 0));
        assert_eq!((state.frames.len(), state.frames.capacity()), (0, 0));
        assert!(state.location.is_empty() && state.detail.is_empty() && state.errors.is_empty());
    }
    assert!(saw_owned);
}

#[test]
fn cancellation_during_the_actual_later_name_chunk_keeps_a_valid_owned_utf8_prefix() {
    let name = "λ".repeat(3000);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    state
        .diagnostic(&name, 0, Surface::Instruction(0), &mut work)
        .unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
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
    let mut state = Checking::default();
    assert_eq!(
        state.diagnostic(&name, 0, Surface::Instruction(0), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.location, format!("function '{}", "λ".repeat(512)));
    assert!(state.detail.is_empty() && state.errors.is_empty());
    state.retire_scratch(&mut work);
    assert_eq!(state.location.capacity(), 0);
}

#[test]
fn final_publication_and_actual_post_drop_retirement_refusals_keep_original_cause() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    let mut observer = Observer {
        stop: Some(baseline.events.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_standalone_refinements_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    // Four completed owned-string diagnostics: per-error pop, two separately
    // pre/post-polled strings, final error poll; then buffer pre/post polls.
    assert!(observer.events.len() >= baseline.events.len() + 4 * 6 + 2);
    assert!(
        observer
            .events
            .iter()
            .skip(baseline.events.len())
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
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
    assert_eq!(work.session.first_refusal().unwrap().cause, "original stop");
}
