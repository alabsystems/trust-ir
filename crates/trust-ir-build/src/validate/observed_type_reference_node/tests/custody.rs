// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_partial_location_is_held_with_prior_errors_until_original_retirement() {
    let m = Module::new("");
    let r = registry();
    let loc = "λ\0尾".repeat(1500);
    let ty = invalid();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        errors: vec![prior()],
        ..State::default()
    };
    state.node(&m, &r, &ty, &loc, &mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    let mut found = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            errors: vec![prior()],
            ..State::default()
        };
        assert_eq!(
            state.node(&m, &r, &ty, &loc, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if !state.location.is_empty() && state.location.len() < loc.len() {
            found = true;
            assert!(loc.starts_with(&state.location));
            assert_eq!(state.errors, vec![prior()]);
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    assert!(found);
}
#[test]
fn whole_untrusted_location_name_runtime_survive_both_output_preallocation_cuts() {
    let m = Module::new("");
    let r = registry();
    let loc = "raw λ\0尾".repeat(300);
    let name = "Name9_".repeat(300);
    let runtime = format!("r::{}", "Run8_".repeat(300));
    let ty = Ty::handle(&name, &runtime);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.node(&m, &r, &ty, &loc, &mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    for cut in [end - 1, end] {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.node(&m, &r, &ty, &loc, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.location, loc);
        assert_eq!(state.name, name);
        assert_eq!(state.runtime, runtime);
        assert!(state.errors.is_empty());
        if cut == end - 1 {
            assert_eq!(state.errors.capacity(), 0)
        } else {
            assert!(state.errors.capacity() > 0)
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
}
#[test]
fn full_static_detail_and_raw_location_stay_owned_until_last_transfer_fee() {
    let m = Module::new("");
    let r = registry();
    let ty = invalid();
    let loc = "whole λ\0tail";
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.node(&m, &r, &ty, loc, &mut w).unwrap();
    let cut = calls.get();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.node(&m, &r, &ty, loc, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.location, loc);
    assert_eq!(
        state.detail,
        "dialect type namespace must be nonempty ASCII letters, digits, or '_'"
    );
    assert!(state.errors.is_empty());
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
#[test]
fn sticky_cleanup_consumes_all_partial_raw_fields_and_prior_nested_diagnostics() {
    let mut state = State {
        location: "partial λ\0FULL".into(),
        detail: "partial 尾\0FULL".into(),
        name: "Name9_".repeat(400),
        runtime: "Runtime9_".repeat(400),
        errors: vec![prior(), prior()],
        census: NominalCensus {
            dialect: true,
            handle: true,
        },
    };
    let mut o = Observer {
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert!(w.session.first_refusal().is_some());
    drop(w);
    drop(s);
    assert!(o.events.len() > 20);
    assert!(
        o.events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
