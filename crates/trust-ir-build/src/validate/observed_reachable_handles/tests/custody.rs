// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_partial_closure_retains_frames_seen_rows_child_text_and_output_until_cleanup() {
    let mut m = Module::new("");
    m.types = vec![Ty::Tuple(vec![array(0), handle("A")])];
    let roots = [array(0), handle("B")];
    let wanted = expected(&m, &roots, &[]);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &roots, &[], &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    let mut stack = false;
    let mut frames = false;
    let mut seen = false;
    let mut handles = false;
    let mut pending = false;
    let mut partial = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            cleanup_after: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.run(&m, &roots, &[], &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        stack |= !state.stack.is_empty();
        frames |= !state.frames.is_empty();
        seen |= !state.seen.is_empty();
        handles |= !state.handles.is_empty();
        if !state.pending.is_empty() {
            pending = true;
            assert!([handle("A").to_string(), handle("B").to_string()].contains(&state.pending));
        }
        partial |= !state.output.is_empty() && state.output.len() < wanted.len();
        assert!(wanted.starts_with(&state.output));
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original handle-name stop"
        );
        drop(work);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(stack && frames && seen && handles && pending && partial);
}
#[test]
fn whole_returned_display_string_is_held_before_and_after_output_allocation_refusals() {
    let m = Module::new("");
    let roots = [handle("Name")];
    let rendered = roots[0].to_string();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &roots, &[], &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    let mut before = false;
    let mut after = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.run(&m, &roots, &[], &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        let event = baseline.events[cut - 1];
        if state.pending == rendered
            && state.output.is_empty()
            && event.work == rendered.len()
            && event.copy_bytes == rendered.len()
        {
            if state.output.capacity() == 0 {
                before = true;
            } else {
                after = true;
            }
            assert_eq!(state.handles.len(), 1);
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
    assert!(before && after);
}
#[test]
fn deep_inline_continuations_retire_iteratively_after_a_real_interior_stop() {
    let m = Module::new("");
    let mut root = handle("Bottom");
    for _ in 0..1024 {
        root = Ty::Tuple(vec![root]);
    }
    let (_, baseline, _) = run(&m, core::slice::from_ref(&root), &[]);
    let cut = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 48
                && e.copy_bytes == 2 * size_of::<Frame<'_>>() + size_of::<Option<Key>>()
        })
        .nth(600)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        cleanup_after: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        reachable_handles_text_observed(&m, core::slice::from_ref(&root), &[], &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events.len() > cut + 250);
    // The original input's destruction is separate, explicit fixture work.
    loop {
        match root {
            Ty::Tuple(mut one) => {
                assert_eq!(one.len(), 1);
                root = one.pop().unwrap();
            }
            other => {
                drop(other);
                break;
            }
        }
    }
}
#[test]
fn sticky_retirement_consumes_all_partial_borrowed_and_owned_stores_without_replacing_cause() {
    let roots = [handle("A"), handle("B")];
    let mut state = State {
        stack: roots.iter().collect(),
        frames: vec![Frame::Visit(&roots[0]), Frame::Children(&roots, 1)],
        seen: vec![Key::Ty(0), Key::Enum(1)],
        handles: roots.iter().collect(),
        pending: "whole child λ\0FULL".into(),
        output: "prior output 尾\0FULL".into(),
    };
    let mut o = Observer {
        stop: Some(1),
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original handle-name stop"
    );
    drop(work);
    drop(s);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events.len() > 16);
}
#[test]
fn complete_successful_text_remains_caller_owned_until_original_explicit_string_cleanup() {
    let m = fixture();
    let roots = [Ty::Closure(ClosureTyId::new(0))];
    let (expected, _, bound) = run(&m, &roots, &[]);
    let mut o = Observer {
        cleanup_after: Some(bound),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let output = reachable_handles_text_observed(&m, &roots, &[], &mut s, site()).unwrap();
    assert_eq!(output, expected);
    assert_eq!(calls.get(), bound);
    assert!(s.first_refusal().is_none());
    {
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        work.flat(output);
    }
    assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
    drop(s);
    // Work::flat is explicit String-header disposal followed by a retirement
    // poll; it is not generic error-vector retirement's terminal publication.
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
