// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
mod custody;
#[test]
fn every_real_callback_including_root_drop_cleanup_and_publication_can_refuse() {
    let mut module = Module::new("observed-drop");
    module.drop_glue.push(DropGlueEntry {
        ty: Ty::Tuple(vec![Ty::U32, Ty::Bool]),
        glue: FuncId::new(9),
    });
    module.functions.push(callee(9, "glue", true, false));
    let cases = [
        (fixture(), None),
        (
            function(vec![
                node(
                    Inst::Drop {
                        ty: Ty::Tuple(vec![Ty::U32, Ty::Bool]),
                        ptr: v(1),
                    },
                    &[],
                ),
                node(store(1), &[]),
            ]),
            Some(module),
        ),
    ];
    for (f, module) in cases {
        let (_, baseline) = run(&f, module.as_ref());
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                validate_function_effect_claims_observed(&f, module.as_ref(), &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original effect stop"
            );
            assert_eq!(
                session.first_refusal().unwrap().progress,
                baseline.events[stop - 1]
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
}
#[test]
fn work_and_copy_caps_accumulate_across_calls_and_sticky_refusal_cannot_resume() {
    let f = fixture();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    for _ in 0..2 {
        assert_eq!(
            validate_function_effect_claims_observed(&f, None, &mut session, site())
                .unwrap()
                .len(),
            3
        );
    }
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(measured.work - 1),
            byte_cap: bytes.then_some(measured.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_effect_claims_observed(&f, None, &mut session, site())
                .unwrap()
                .len(),
            3
        );
        assert_eq!(
            validate_function_effect_claims_observed(&f, None, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            validate_function_effect_claims_observed(&f, None, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn first_header_refusal_precedes_any_allocation_or_source_walk() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_effect_claims_observed(&fixture(), None, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "bytes");
    assert_eq!(observer.events.len(), 1);
}
#[test]
fn actual_wide_result_definition_collection_stops_and_retires_its_partial_rows() {
    let mut f = function(vec![node(alloca(), &[])]);
    f.blocks[0].body[0].results = (10..5010).map(v).collect();
    let mut observer = Observer {
        work_cap: Some(2000),
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
    assert!(!state.definitions.is_empty());
    assert!(state.definitions.len() < 5001);
    assert!(state.drop_index.is_none());
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
}
#[test]
fn actual_root_stack_seen_and_roots_remain_owned_until_explicit_retirement() {
    let f = function(vec![
        node(alloca(), &[10]),
        node(copy(10), &[20]),
        node(copy(10), &[20]),
        node(copy(30), &[30]),
    ]);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.collect(&f, &mut work).unwrap();
    let prefix = measured.events.len();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut trace_work = Work {
        session: &mut session,
        site: site(),
    };
    assert!(!state.trace(v(20), &mut trace_work).unwrap());
    state.retire_scratch(&mut trace_work);
    state.retire_errors(&mut trace_work);
    let count = observer
        .events
        .iter()
        .take_while(|e| e.phase != ExecutionPhase::ScratchRetirement)
        .count();
    assert!(prefix > 0);
    let (mut saw_stack, mut saw_seen, mut saw_roots) = (false, false, false);
    for stop in 1..=count {
        // This narrow trace control seeds borrowed definition headers as test
        // setup; the public pass collects them under its supplied owner.
        let mut setup = Observer::default();
        let mut setup_session = ObservedSession::new(InterpretOptions::default(), &mut setup);
        let mut setup_work = Work {
            session: &mut setup_session,
            site: site(),
        };
        let mut state = State::default();
        state.collect(&f, &mut setup_work).unwrap();
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        assert_eq!(
            state.trace(v(20), &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw_stack |= !state.stack.is_empty();
        saw_seen |= !state.seen.is_empty();
        saw_roots |= !state.roots.is_empty();
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original effect stop"
        );
    }
    assert!(saw_stack && saw_seen && saw_roots);
}
#[test]
fn actual_drop_type_comparison_refusal_cannot_turn_into_an_unresolved_diagnostic() {
    let ty = Ty::Tuple(vec![Ty::U32; 5000]);
    let instruction = Inst::Drop {
        ty: ty.clone(),
        ptr: v(1),
    };
    let mut module = Module::new("wide-drop-key");
    module.drop_glue.push(DropGlueEntry {
        ty,
        glue: FuncId::new(9),
    });
    let mut setup = Observer::default();
    let mut setup_session = ObservedSession::new(InterpretOptions::default(), &mut setup);
    let index = module
        .drop_glue_index_observed(&mut setup_session, site())
        .unwrap();
    let mut state = State {
        drop_index: Some(index),
        ..State::default()
    };
    let mut observer = Observer {
        work_cap: Some(2000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert!(matches!(
        state.effect(&instruction, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert!(state.drop_index.is_some());
    assert!(state.errors.is_empty());
    assert!(state.inst_text.is_empty());
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
    assert!(
        observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::DropGlueIndex)
    );
    assert!(
        observer
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Validation)
            .count()
            > 10
    );
}
