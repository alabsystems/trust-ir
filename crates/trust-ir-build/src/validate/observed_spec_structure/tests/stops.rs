// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::unnecessary_to_owned,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_public_callback_refuses_without_shorter_success_or_replaced_cause() {
    let m = input();
    let (_, base) = run(&m);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_spec_structure_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original structural mapping"
        );
    }
}
#[test]
fn actual_child_vector_is_held_whole_before_first_fallible_parent_read() {
    let m = input();
    let trigger = Rc::new(Cell::new(false));
    let mut o = Observer {
        trigger: Some(trigger.clone()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let child =
        trust_ir::validate_spec_structure_observed(&m.spec_modules, &mut s, site()).unwrap();
    assert_eq!(child.len(), 1);
    let mut state = State {
        batch: Some(child.into_iter()),
        ..Default::default()
    };
    trigger.set(true);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        state.merge(&mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.batch.as_ref().unwrap().len(), 1);
    assert!(state.pending.is_none());
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
#[test]
fn next_owned_violation_is_retained_before_allocation_and_before_the_error_move() {
    let expected = rows();
    for stop in [3, 4] {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            batch: Some(expected.clone().into_iter()),
            ..Default::default()
        };
        assert_eq!(
            state.merge(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.pending.as_ref(), Some(&expected[0]));
        assert_eq!(state.batch.as_ref().unwrap().len(), 2);
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, stop == 3);
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
}
#[test]
fn later_stop_retains_complete_prefix_pending_and_a_real_nonempty_owned_tail() {
    let expected = rows();
    let count = {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            batch: Some(expected.clone().into_iter()),
            ..Default::default()
        };
        state.merge(&mut w).unwrap();
        drop(w);
        drop(s);
        o.events.len()
    };
    let mut hits = 0;
    for stop in 1..=count {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            batch: Some(expected.clone().into_iter()),
            ..Default::default()
        };
        assert_eq!(
            state.merge(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if state.errors.len() == 1
            && state.pending.as_ref() == Some(&expected[1])
            && state.batch.as_ref().is_some_and(|b| b.len() == 1)
        {
            hits += 1;
            assert_eq!(
                state.errors[0],
                ValidationError::InvalidSpecStructure {
                    violation: expected[0].clone()
                }
            );
            assert_eq!(state.batch.as_ref().unwrap().as_slice(), &expected[2..]);
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    assert!(hits >= 2);
}
#[test]
fn one_original_cumulative_work_and_copy_budget_covers_child_and_parent() {
    let m = input();
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_module_spec_structure_observed(&m, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_spec_structure_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn initial_state_copy_refusal_prevents_the_core_walk_and_cannot_be_retried_within_sticky_owner() {
    let m = input();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_spec_structure_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        validate_module_spec_structure_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    drop(s);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn cleanup_refusal_consumes_pending_and_every_full_tail_violation_then_the_prior_prefix() {
    let owned = rows();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        batch: Some(owned[1..].to_vec().into_iter()),
        pending: Some(owned[0].clone()),
        errors: vec![ValidationError::InvalidSpecStructure {
            violation: owned[0].clone(),
        }],
    };
    arm.set(true);
    assert_eq!(
        state.finish(Ok(()), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(w.session.first_refusal().unwrap().cause, "cleanup");
    drop(w);
    drop(s);
    // Core pending/tail consuming APIs account for their full String extent.
    // Generic prefix retirement retains its separate constant-header contract.
    assert!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .map(|e| e.work)
            .sum::<usize>()
            > 60000
    );
}
#[test]
fn final_parent_publication_refusal_occurs_after_empty_batch_and_consumes_the_complete_result() {
    let m = input();
    let (_, base) = run(&m);
    let mut o = Observer {
        stop: Some(base.events.len()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_spec_structure_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    drop(s);
    assert!(o.events.len() > base.events.len());
    assert!(
        o.events
            .iter()
            .skip(base.events.len())
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
