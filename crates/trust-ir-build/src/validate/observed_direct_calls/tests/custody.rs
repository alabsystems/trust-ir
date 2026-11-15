// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_same_private_entry_cut_retains_child_and_prior_errors_until_explicit_full_drain() {
    let mut m = fixture();
    m.func_types[1].is_vararg = true;
    m.functions[0].producer = Some(Producer::Other("λ\0caller".into()));
    m.functions[1].producer = Some(Producer::Other("λ\ntarget".into()));
    let inst = call(&[0, 1, 2, 3]);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (catalog, values, nominal) = setup(&m, true, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &catalog,
            &m.functions[0],
            &inst,
            &values,
            nominal.as_ref(),
            BlockId::new(1),
            &mut Work {
                session: &mut s,
                site: site(),
            },
        )
        .unwrap();
    let end = calls.get();
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    dispose(catalog, values, nominal, &mut s);
    drop(s);
    let (mut pending, mut prior, mut text) = (false, false, false);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values, nominal) = setup(&m, true, &mut s);
        let mut state = State::default();
        assert_eq!(
            state.run(
                &catalog,
                &m.functions[0],
                &inst,
                &values,
                nominal.as_ref(),
                BlockId::new(1),
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        pending |= state.pending.capacity() != 0;
        prior |= !state.errors.is_empty();
        text |= state.name.capacity() != 0
            || state.expected.capacity() != 0
            || state.actual.capacity() != 0
            || state.caller.is_some()
            || state.callee.is_some();
        drain(
            &mut state,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        );
        assert!(empty(&state));
        dispose(catalog, values, nominal, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(pending && prior && text);
}
#[test]
fn full_type_display_children_are_owned_before_producer_and_output_reserve_fees() {
    let mut m = fixture();
    m.func_types[1].params[0] = Ty::Tuple(vec![h(), Ty::Bool]);
    let inst = call(&[0, 0]);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (catalog, values, nominal) = setup(&m, true, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &catalog,
            &m.functions[0],
            &inst,
            &values,
            nominal.as_ref(),
            BlockId::new(1),
            &mut Work {
                session: &mut s,
                site: site(),
            },
        )
        .unwrap();
    let end = calls.get();
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    dispose(catalog, values, nominal, &mut s);
    drop(s);
    let (mut expected, mut actual) = (false, false);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values, nominal) = setup(&m, true, &mut s);
        let mut state = State::default();
        assert_eq!(
            state.run(
                &catalog,
                &m.functions[0],
                &inst,
                &values,
                nominal.as_ref(),
                BlockId::new(1),
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        if !state.expected.is_empty() {
            assert_eq!(state.expected, m.func_types[1].params[0].to_string());
            expected = true;
        }
        if !state.actual.is_empty() {
            assert_eq!(state.actual, "bool");
            actual = true;
        }
        drain(
            &mut state,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        );
        assert!(empty(&state));
        dispose(catalog, values, nominal, &mut s);
    }
    assert!(expected && actual);
}
#[test]
fn pending_child_prior_output_partial_producer_and_all_fields_drain_after_sticky_stop() {
    let error = || ValidationError::CallArgCountMismatch {
        block: 1,
        callee: "complete target".repeat(100),
        expected: 2,
        actual: 0,
        caller_producer: Some("caller".repeat(300)),
        callee_producer: Some("target".repeat(300)),
    };
    let mut state = State {
        name: "pending name".repeat(300),
        expected: "expected full".repeat(300),
        actual: "actual full".repeat(300),
        caller: Some("partial quoted λ".repeat(300)),
        callee: Some("complete quoted λ".repeat(300)),
        pending: vec![error(), error()],
        errors: vec![error()],
    };
    let mut o = Observer {
        stop: Some(1),
        cleanup_after: Some(1),
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
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    assert!(empty(&state));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original direct call stop"
    );
    drop(s);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn final_whole_output_publication_refusal_retires_every_error_and_keeps_actual_healthy_terminal() {
    let m = fixture();
    let inst = call(&[0, 1, 1]);
    let (_, baseline, _, end) = run(&m, &inst, true);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, true, &mut s);
    assert_eq!(
        validate_direct_call_observed(
            &catalog,
            &m.functions[0],
            &inst,
            &values,
            nominal.as_ref(),
            BlockId::new(1),
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    dispose(catalog, values, nominal, &mut s);
    drop(s);
    assert_eq!(&o.events[..end], &baseline.events[..end]);
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        *baseline.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
