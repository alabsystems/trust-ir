// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

fn prepared(w: &mut Work<'_, '_, Observer>) -> State {
    let mut state = State::default();
    state.run(&fixture(), Rule::PanicSites, w).unwrap();
    assert_eq!(state.errors.len(), 6);
    w.text("full partial cleanup name λ", &mut state.text)
        .unwrap();
    w.admit(1, size_of::<Option<ValidationError>>()).unwrap();
    state.pending = state.errors.pop();
    assert!(!state.errors.is_empty() && state.pending.is_some() && !state.text.is_empty());
    state
}
#[test]
fn held_local_errors_survive_real_policy_finish_and_later_nonempty_cleanup_refusal() {
    for error in [
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
        ObservedValueError::InvalidRange,
    ] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            cleanup: Some(arm.clone()),
            ..Default::default()
        };
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = prepared(&mut w);
        let begin = calls.get();
        arm.set(true);
        assert_eq!(state.finish(Err(error), &mut w), Err(error));
        empty(&state);
        let first = w.session.first_refusal().unwrap();
        assert_eq!(first.cause, "cleanup");
        assert_eq!(first.progress.site, site());
        assert_eq!(first.progress.phase, ExecutionPhase::ScratchRetirement);
        drop(w);
        drop(s);
        assert!(!o.events[begin..].is_empty());
        assert!(
            o.events[begin..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn healthy_full_policy_batch_is_withheld_when_actual_scratch_cleanup_refuses() {
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
    let mut state = State::default();
    state.run(&fixture(), Rule::PanicSites, &mut w).unwrap();
    assert_eq!(state.errors.len(), 6);
    arm.set(true);
    assert_eq!(
        state.finish(Ok(()), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    empty(&state);
    assert_eq!(w.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn earlier_original_refusal_stays_immutable_while_held_error_and_all_scratch_drain() {
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
    let mut state = prepared(&mut w);
    arm.set(true);
    w.record(19, 23);
    let first = w.session.first_refusal().unwrap();
    let saved = (first.progress, first.cause);
    assert_eq!(
        state.finish(Err(ObservedValueError::CapacityOverflow), &mut w),
        Err(ObservedValueError::CapacityOverflow)
    );
    empty(&state);
    let first = w.session.first_refusal().unwrap();
    assert_eq!((first.progress, first.cause), saved);
}
#[test]
fn healthy_completion_keeps_the_whole_ordinary_policy_batch_and_caller_terminal() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    let result = state.run(&m, Rule::PanicSites, &mut w);
    let output = state.finish(result, &mut w).unwrap();
    assert_eq!(output, expected(&m, Rule::PanicSites));
    empty(&state);
    retire_validation_errors_observed(output, w.session, w.site).unwrap();
    assert!(w.session.first_refusal().is_none());
    drop(w);
    drop(s);
    assert_eq!(
        o.events.last(),
        Some(&ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        })
    );
}
