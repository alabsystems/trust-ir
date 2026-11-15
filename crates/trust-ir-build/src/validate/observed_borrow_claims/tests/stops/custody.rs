// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn completed_raw_name_remains_pending_when_error_vector_storage_is_refused() {
    let name = "raw'λ\n\0".repeat(700);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.reference(&name, 8, 9, &mut work).unwrap();
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
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.reference(&name, 8, 9, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.name, name);
    assert_eq!((state.errors.len(), state.errors.capacity()), (0, 0));
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert_eq!(state.name.capacity(), 0);
}

#[test]
fn actual_name_copy_refusal_retains_an_exact_utf8_prefix_until_retirement() {
    let name = "λ".repeat(3000);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.reference(&name, 8, 9, &mut work).unwrap();
    // First growth and first copy both price1024. Third match is second copy.
    let stop = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == 1024 && e.copy_bytes == 1024)
        .nth(2)
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
    let mut state = State::default();
    assert_eq!(
        state.reference(&name, 8, 9, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.name, "λ".repeat(512));
    assert!(state.errors.is_empty());
    state.retire_scratch(&mut work);
    assert_eq!(state.name.capacity(), 0);
}

#[test]
fn canonical_edge_vector_and_partial_incoming_rows_stay_owned_at_every_later_stop() {
    let f = function(vec![node(
        Inst::CondBr {
            cond: v(99),
            then_target: b(1),
            then_args: vec![v(1), v(2)],
            else_target: b(2),
            else_args: vec![v(3)],
        },
        &[],
    )]);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.need_incoming(&f, &mut work).unwrap();
    let mut saw = false;
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
        let result = state.need_incoming(&f, &mut work);
        if result.is_err()
            && !state.edges.is_empty()
            && state.incoming.as_ref().is_some_and(|rows| !rows.is_empty())
        {
            saw = true;
            assert_eq!(state.edges.len(), 2);
            assert_eq!(state.incoming.as_ref().unwrap()[0], (1, 0, v(1)));
        }
        state.retire_scratch(&mut work);
        assert_eq!(state.edges.capacity(), 0);
        assert!(state.incoming.is_none());
    }
    assert!(saw);
}

#[test]
fn actual_any_root_trace_retains_stack_seen_and_all_definitions_until_cleanup() {
    let mut f = fixture();
    f.blocks[0].body.insert(
        2,
        node(
            Inst::Select {
                ty: Ty::Ptr,
                cond: v(99),
                then_val: v(1),
                else_val: v(2),
            },
            &[7],
        ),
    );
    let mut baseline = Observer::default();
    let count = baseline.count.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.need_definitions(&f, &mut work).unwrap();
    state.need_incoming(&f, &mut work).unwrap();
    let prefix = count.get();
    assert!(state.trace(v(7), &mut work).unwrap());
    let mut saw = false;
    for stop in prefix + 1..=baseline.events.len() {
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
        state.need_definitions(&f, &mut work).unwrap();
        state.need_incoming(&f, &mut work).unwrap();
        let result = state.trace(v(7), &mut work);
        if result.is_err() && !state.stack.is_empty() && !state.seen.is_empty() {
            saw = true;
            assert!(
                state
                    .definitions
                    .as_ref()
                    .is_some_and(|rows| !rows.is_empty())
            );
        }
        state.retire_scratch(&mut work);
        assert_eq!(state.stack.capacity() + state.seen.capacity(), 0);
        assert!(state.definitions.is_none() && state.incoming.is_none());
    }
    assert!(saw);
}
