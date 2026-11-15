// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_definition_and_raw_runtime_are_held_across_both_output_allocation_cuts() {
    let raw: &'static str = Box::leak("λ\0尾".repeat(350).into_boxed_str());
    let r = HandleRegistry {
        pins: vec![pin(raw)],
    };
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state
        .definition("record", u32::MAX, raw, &r, &mut work)
        .unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    for cut in [end - 1, end] {
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
            state.definition("record", u32::MAX, raw, &r, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.def, "record #4294967295");
        assert_eq!(state.runtime, raw);
        assert!(state.errors.is_empty());
        if cut == end - 1 {
            assert_eq!(state.errors.capacity(), 0);
        } else {
            assert!(state.errors.capacity() > 0);
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn actual_partial_runtime_and_prior_rows_survive_every_cut_until_sticky_retirement() {
    let raw: &'static str = Box::leak("λ\0尾".repeat(250).into_boxed_str());
    let r = HandleRegistry {
        pins: vec![pin(raw)],
    };
    let mut m = Module::new("");
    m.records = vec![record(9, raw), record(10, raw)];
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        errors: vec![prior()],
        ..State::default()
    };
    state.run(&m, &r, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    let mut partial = false;
    let mut complete = false;
    let mut prior_and_new = false;
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
        let mut state = State {
            errors: vec![prior()],
            ..State::default()
        };
        assert_eq!(
            state.run(&m, &r, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.errors.first(), Some(&prior()));
        if !state.runtime.is_empty() && state.runtime.len() < raw.len() {
            partial = true;
            assert!(raw.starts_with(&state.runtime));
        }
        complete |= state.runtime == raw;
        prior_and_new |= state.errors.len() > 1;
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original runtime spelling stop"
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
    assert!(partial && complete && prior_and_new);
}
#[test]
fn complete_result_remains_owned_for_healthy_or_refused_original_caller_cleanup() {
    let m = fixture();
    let r = registry();
    let (_, _, bound) = run(&m, &r);
    for refuse in [false, true] {
        let mut o = Observer {
            cleanup_after: refuse.then_some(bound),
            ..Observer::default()
        };
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let output = validate_handle_runtime_spellings_observed(&m, &r, &mut s, site()).unwrap();
        assert_eq!(output.len(), 4);
        assert_eq!(calls.get(), bound);
        let result = retire_validation_errors_observed(output, &mut s, site());
        let end = calls.get();
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        } else {
            result.unwrap();
        }
        drop(s);
        if refuse {
            assert!(
                o.events[bound..end]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        } else {
            assert!(
                o.events[bound..end - 1]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
            assert_eq!(
                o.events[end - 1],
                ExecutionProgress {
                    phase: ExecutionPhase::Publication,
                    site: site(),
                    work: 0,
                    copy_bytes: 0
                }
            );
        }
    }
}
