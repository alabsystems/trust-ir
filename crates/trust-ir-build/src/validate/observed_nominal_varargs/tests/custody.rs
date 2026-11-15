// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_raw_fields_remain_owned_across_both_output_preallocation_cuts() {
    let raw = "λ\0尾".repeat(1000);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.error(Family::Handle, &raw, &mut work).unwrap();
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
            state.error(Family::Handle, &raw, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.location, raw);
        assert_eq!(state.detail, HANDLE);
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
fn interior_argument_stop_retains_prior_rows_and_partial_raw_fields_until_sticky_cleanup() {
    let (m, f) = fixture();
    let raw = "λ\0尾".repeat(700);
    let args = [v(1), v(2)];
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let values = build_function_value_types_observed(&f, &mut s, site()).unwrap();
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        errors: vec![prior()],
        ..State::default()
    };
    let start = calls.get();
    state
        .run(&args, 0, &values, Some(&nominal), &raw, &mut work)
        .unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    nominal.retire_observed(&mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut saw_partial = false;
    let mut saw_complete = false;
    let mut saw_prior_and_new = false;
    for cut in start + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            cleanup_after: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = build_function_value_types_observed(&f, &mut s, site()).unwrap();
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            errors: vec![prior()],
            ..State::default()
        };
        assert_eq!(
            state.run(&args, 0, &values, Some(&nominal), &raw, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.errors.first(), Some(&prior()));
        if !state.location.is_empty() && state.location.len() < raw.len() {
            saw_partial = true;
            assert!(raw.starts_with(&state.location));
        }
        saw_complete |= state.location == raw;
        saw_prior_and_new |= state.errors.len() > 1;
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original varargs stop"
        );
        drop(work);
        assert_eq!(
            nominal.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            values.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(saw_partial && saw_complete && saw_prior_and_new);
}
#[test]
fn successful_vector_remains_whole_until_caller_retirement_with_actual_terminal_semantics() {
    let (m, f) = fixture();
    let args = args();
    let (_, baseline, _, end) = run(&m, &f, &args, 0, "L", Mode::Present);
    assert_eq!(
        baseline.events[end - 1].copy_bytes,
        size_of::<Vec<ValidationError>>()
    );
    for refuse in [false, true] {
        let mut o = Observer {
            cleanup_after: refuse.then_some(end),
            ..Observer::default()
        };
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = build_function_value_types_observed(&f, &mut s, site()).unwrap();
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        let output = validate_nominal_varargs_observed(
            &args,
            0,
            &values,
            Some(&nominal),
            "L",
            &mut s,
            site(),
        )
        .unwrap();
        assert_eq!(calls.get(), end);
        assert_eq!(output.len(), 4);
        let result = retire_validation_errors_observed(output, &mut s, site());
        let retired = calls.get();
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        } else {
            result.unwrap();
        }
        let _ = nominal.retire_observed(&mut s, site());
        let _ = values.retire_observed(&mut s, site());
        drop(s);
        if refuse {
            assert!(
                o.events[end..retired]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        } else {
            assert!(
                o.events[end..retired - 1]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
            assert_eq!(
                o.events[retired - 1],
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
