// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::tests::{Observer, bad_fixture, drain, empty, site};
use super::*;
use trust_ir::interpret::InterpretOptions;
#[test]
fn complete_expected_and_display_children_stay_owned_across_both_output_allocation_cuts() {
    let (m, r) = bad_fixture();
    let f = &m.functions[0];
    let p = &r.pins[0];
    let e = &p.entry_points[0];
    let ordinary = super::super::super::validate_handle_entry_points(&m, &r);
    let ValidationError::HandleEntryPointSignatureMismatch {
        symbol,
        expected,
        actual,
        ..
    } = &ordinary[0]
    else {
        panic!("expected complete ordinary mismatch")
    };
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    state.expected = Some(p.func_ty_observed(e, &mut s, site()).unwrap());
    let begin = calls.get();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.check_function(&m, f, p, e, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    let mut before = false;
    let mut after = false;
    let mut child = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            cleanup_after: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        state.expected = Some(p.func_ty_observed(e, &mut s, site()).unwrap());
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.check_function(&m, f, p, e, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(state.expected.is_some());
        assert_eq!(state.expected.as_ref().unwrap().signature(), &p.func_ty(e));
        child |= !state.render.is_empty();
        if &state.symbol == symbol
            && &state.expected_text == expected
            && &state.actual == actual
            && state.errors.is_empty()
        {
            if state.errors.capacity() == 0 {
                before = true
            } else {
                after = true
            }
        }
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
    assert!(before && after && child);
}
