// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn filled<O: ExecutionObserver>(group: Group, w: &mut Work<'_, '_, O>) -> State {
    let m = module(&[9, 1, 9, 1, 9]);
    let catalog = ModuleFunctionCatalog::new(&m);
    let mut state = State::default();
    match group {
        Group::Structs => state.structs(&m, w),
        Group::Functions => state.functions(&catalog, w),
    }
    .unwrap();
    assert_eq!(state.errors, expected(&m, group));
    state
}
#[test]
fn held_local_errors_survive_real_id_finish_and_later_nonempty_cleanup_refusal() {
    for group in [Group::Structs, Group::Functions] {
        for error in [
            ObservedValueError::CapacityOverflow,
            ObservedValueError::AllocationFailed,
            ObservedValueError::InvalidRange,
            ObservedValueError::UnsupportedValue,
        ] {
            let arm = Rc::new(Cell::new(false));
            let mut o = Observer {
                cleanup: Some(arm.clone()),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let mut w = Work {
                session: &mut s,
                site: site(),
            };
            let mut state = filled(group, &mut w);
            assert!(!state.errors.is_empty());
            arm.set(true);
            // Actual State.finish with a complete real source-derived batch.
            // Typed held errors are explicit inputs, not forced allocator failures.
            assert_eq!(state.finish(Err(error), &mut w), Err(error));
            empty(&state);
            assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
            assert_eq!(
                s.first_refusal().unwrap().progress.phase,
                ExecutionPhase::ScratchRetirement
            );
        }
    }
}
#[test]
fn healthy_full_id_batch_is_withheld_when_actual_scratch_cleanup_refuses() {
    for group in [Group::Structs, Group::Functions] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            cleanup: Some(arm.clone()),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = filled(group, &mut w);
        arm.set(true);
        assert_eq!(
            state.finish(Ok(()), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        empty(&state);
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(first.phase, ExecutionPhase::ScratchRetirement);
        drop(s);
        let at = o.events.iter().position(|e| *e == first).unwrap();
        assert!(
            o.events[at..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn earlier_original_refusal_stays_immutable_while_held_id_error_and_all_state_drain() {
    for group in [Group::Structs, Group::Functions] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            arm: Some(arm.clone()),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut o,
        );
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = filled(group, &mut w);
        arm.set(true);
        assert_eq!(w.admit(1, 0), Err(ObservedValueError::AdmissionRefused));
        let first = w.session.first_refusal().unwrap().progress;
        assert_eq!(
            state.finish(Err(ObservedValueError::InvalidRange), &mut w),
            Err(ObservedValueError::InvalidRange)
        );
        empty(&state);
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.first_refusal().unwrap().cause, "original module IDs");
        assert_eq!(s.remaining_fuel(), 0);
    }
}
#[test]
fn healthy_real_id_finish_preserves_complete_ordinary_groups_and_caller_terminal() {
    for group in [Group::Structs, Group::Functions] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = filled(group, &mut w);
        let expected = state.errors.clone();
        let errors = state.finish(Ok(()), &mut w).unwrap();
        assert_eq!(errors, expected);
        empty(&state);
        retire_validation_errors_observed(errors, &mut s, site()).unwrap();
        assert!(s.first_refusal().is_none());
    }
}
