// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_later_partial_field_keeps_all_earlier_complete_rows_owned_until_sticky_drain() {
    let (mut m, r) = bad_fixture();
    m.globals.push(global("pinned", Some(address("pinned"))));
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &r, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    let mut prior = false;
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
            state.run(&m, &r, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        prior |= !state.errors.is_empty()
            && (!state.symbol.is_empty() || !state.other.is_empty() || !state.location.is_empty());
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original entrypoint stop"
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
    assert!(prior);
}
#[test]
fn every_constant_frontier_cut_keeps_borrowed_rows_and_partial_diagnostics_until_full_cleanup() {
    let (m, r) = fixture();
    let tree = Constant::Aggregate((0..16).map(|_| address("pinned")).collect());
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.location = "original raw location".into();
    state.tree(&tree, &r, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    let mut frontier = false;
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
        state.location = "original raw location".into();
        assert_eq!(
            state.tree(&tree, &r, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        frontier |= !state.stack.is_empty();
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
    assert!(frontier);
    assert_eq!(m.functions.len(), 1);
    assert!(matches!(&tree,Constant::Aggregate(rows)if rows.len()==16));
}
#[test]
fn sticky_cleanup_consumes_expected_nested_types_every_string_frontier_and_prior_errors() {
    let (_, r) = bad_fixture();
    let p = &r.pins[0];
    let e = &p.entry_points[0];
    // A separate healthy baseline only locates the same constructor endpoint.
    // Its result is fully retired under that baseline's own original session.
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let expected = p.func_ty_observed(e, &mut s, site()).unwrap();
    let start = calls.get();
    expected.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut cleanup = Observer {
        cleanup_after: Some(start),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut cleanup);
    let expected = p.func_ty_observed(e, &mut session, site()).unwrap();
    let tree = Constant::Aggregate(vec![address("pinned")]);
    let mut state = State {
        expected: Some(expected),
        expected_text: "expected λ\0".into(),
        actual: "actual λ\0".into(),
        piece: "piece".into(),
        render: "rendered child".into(),
        symbol: "symbol".into(),
        other: "global".into(),
        location: "location".into(),
        mismatches: 1,
        stack: vec![&tree],
        errors: vec![ValidationError::HandleEntryPointDefinedLocally {
            function: 0,
            symbol: "prior".into(),
        }],
    };
    // Construction and consuming cleanup use this very same actual session.
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(work);
    drop(session);
    assert_eq!(&cleanup.events[..start], &baseline.events[..start]);
    assert!(
        cleanup.events[start..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn healthy_full_output_has_explicit_original_caller_retirement_with_actual_zero_terminal_receipt() {
    let (mut m, r) = bad_fixture();
    m.globals.push(global("pinned", Some(address("pinned"))));
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_handle_entry_points_observed(&m, &r, &mut s, site()).unwrap();
    let begin = calls.get();
    assert_eq!(out.len(), 4);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    let end = calls.get();
    drop(s);
    assert!(
        o.events[begin..end - 1]
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
