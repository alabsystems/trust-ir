// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn real_callee_name_second_copy_stop_retains_the_exact_first_utf8_chunk() {
    let mut module = Module::new("callee-prefix");
    module
        .functions
        .push(callee(9, &"λ".repeat(5000), false, false));
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert!(
        state
            .call(
                "call",
                FuncId::new(9),
                Some(&module),
                Claim::ReadNone,
                &mut work
            )
            .unwrap()
    );
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let copies: Vec<_> = measured
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .map(|(i, _)| i + 1)
        .collect();
    assert!(copies.len() > 2);
    let stop = copies[1];
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
        state.call(
            "call",
            FuncId::new(9),
            Some(&module),
            Claim::ReadNone,
            &mut work
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        state.inst_text,
        format!("call @{}", &module.functions[0].name[..1024])
    );
    assert!(state.function_name.is_empty() && state.errors.is_empty());
    let first = work.session.first_refusal().unwrap().progress;
    assert_eq!(first, measured.events[stop - 1]);
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().progress, first);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original effect stop"
    );
}
#[test]
fn partial_function_name_pending_inst_and_prior_diagnostic_survive_a_later_stop() {
    let mut f = fixture();
    f.name = "λ".repeat(3000);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.run(&f, None, &mut work).unwrap();
    assert_eq!(state.errors.len(), 3);
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let chunk_event = |e: &ExecutionProgress| {
        e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
    };
    // Each new empty function-name String first admits a 1024-byte growth,
    // immediately followed by the separate real 1024-byte copy. Exclude the
    // FIRST event of that pair, rather than confusing allocation with copy.
    assert_eq!(
        measured
            .events
            .windows(2)
            .filter(|pair| chunk_event(&pair[0]) && chunk_event(&pair[1]))
            .count(),
        3
    );
    let copies: Vec<_> = measured
        .events
        .iter()
        .enumerate()
        .filter(|(i, e)| chunk_event(e) && !measured.events.get(i + 1).is_some_and(chunk_event))
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(copies.len(), 15);
    // Five complete 1024-byte copies per 6000-byte function name. The seventh
    // copy is the second chunk of the SECOND diagnostic's name.
    let stop = copies[6];
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
        state.run(&f, None, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors.len(), 1);
    assert_eq!(state.function_name, &f.name[..1024]);
    assert_eq!(
        state.inst_text,
        "call to function #9 (a callee's attributes cannot be resolved without module context)"
    );
    assert!(!state.definitions.is_empty());
    let first = work.session.first_refusal().unwrap().progress;
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().progress, first);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original effect stop"
    );
}
#[test]
fn growth_and_final_move_admissions_both_precede_moving_pending_strings() {
    let f = function(vec![]);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        inst_text: "prepared diagnostic".into(),
        ..State::default()
    };
    state.commit(&f, 0, Claim::ReadNone, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
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
    for (ordinal, stop) in admissions.into_iter().enumerate() {
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
            inst_text: "prepared diagnostic".into(),
            ..State::default()
        };
        assert_eq!(
            state.commit(&f, 0, Claim::ReadNone, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, ordinal == 0);
        assert_eq!(state.function_name, f.name);
        assert_eq!(state.inst_text, "prepared diagnostic");
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original effect stop"
        );
    }
}
#[test]
fn refused_cleanup_and_final_publication_consume_index_scratch_and_nested_errors() {
    let f = fixture();
    let (_, baseline) = run(&f, None);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_effect_claims_observed(&f, None, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > stop + 10);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    let mut module = Module::new("index-retirement");
    module.functions.push(callee(9, "pure", true, false));
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
    state.run(&f, Some(&module), &mut work).unwrap();
    assert_eq!(state.errors.len(), 2);
    assert!(state.drop_index.is_some());
    arm.set(true);
    state.retire_scratch(&mut work);
    assert!(state.drop_index.is_none());
    assert_eq!(state.definitions.capacity(), 0);
    state.retire_errors(&mut work);
    assert!(empty(&state));
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original effect cleanup"
    );
}
