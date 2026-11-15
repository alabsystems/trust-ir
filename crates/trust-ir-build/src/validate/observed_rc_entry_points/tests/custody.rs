// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_type_display_child_remains_owned_before_any_parent_copy_or_reserve() {
    let mut m = bad_fixture();
    m.func_types[0].params = vec![Ty::Tuple(vec![Ty::Bool, Ty::Ptr])];
    let complete = m.func_types[0].params[0].to_string();
    let (_, _, end) = run(&m);
    let mut found = false;
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
        let _ = state.run(&m, &mut work);
        if state.render == complete {
            found = true;
            assert!(state.render.capacity() > 0);
            assert!(state.piece.starts_with("signature ("));
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
    assert!(found);
}
#[test]
fn full_prior_diagnostics_and_partial_next_fields_remain_owned_at_later_refusals() {
    let mut m = bad_fixture();
    m.globals = vec![
        global("clean_inc", Some(address("clean_dec"))),
        global("data", Some(address("clean_inc"))),
    ];
    let (expected, _, end) = run(&m);
    let mut held = false;
    let mut partial = false;
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
        let _ = state.run(&m, &mut work);
        if !state.errors.is_empty() {
            held = true;
            assert_eq!(&state.errors[..], &expected[..state.errors.len()]);
            assert!(state.errors.capacity() > 0);
        }
        if !state.symbol.is_empty() || !state.other.is_empty() || !state.actual.is_empty() {
            partial = true;
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
    assert!(held && partial);
}
#[test]
fn every_private_body_cut_drains_owned_strings_borrowed_stack_capacity_and_all_prior_rows() {
    let mut m = bad_fixture();
    m.globals.push(global(
        "G",
        Some(Constant::Aggregate(vec![
            address("clean_inc"),
            address("clean_dec"),
        ])),
    ));
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&m, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert!(state.run(&m, &mut work).is_err());
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original RC stop"
        );
    }
}
#[test]
fn sticky_cleanup_still_drops_complete_pending_strings_stack_and_complete_error_payloads() {
    let mut m = bad_fixture();
    m.globals.push(global("G", Some(address("clean_dec"))));
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&m, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    let mut o = Observer {
        stop: Some(end + 1),
        cleanup_after: Some(end + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&m, &mut work).unwrap();
    assert_eq!(
        state.errors,
        super::super::super::validate_rc_entry_points(&m)
    );
    assert!(state.errors.capacity() > 0);
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original RC stop"
    );
    drop(work);
    drop(s);
    assert!(
        o.events[end + 1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
