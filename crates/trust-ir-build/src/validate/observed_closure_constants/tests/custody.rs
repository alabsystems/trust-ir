// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn private_end(m: &Module) -> usize {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.run(m, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    empty(&state);
    end
}
fn private_tree_end(m: &Module) -> usize {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let g = &m.globals[0];
    state
        .tree(
            m,
            g.initializer.as_ref().unwrap(),
            &g.ty,
            m.pointer_bits(),
            &mut work,
        )
        .unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    empty(&state);
    end
}
#[test]
fn real_current_and_suspended_borrowed_tree_rows_stay_owned_until_original_drain() {
    let m = fixture();
    let end = private_tree_end(&m);
    let (mut current, mut pending) = (false, false);
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
        assert_eq!(
            state.tree(
                &m,
                m.globals[0].initializer.as_ref().unwrap(),
                &m.globals[0].ty,
                m.pointer_bits(),
                &mut work
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        current |= state.current.is_some();
        pending |= !state.pending.is_empty();
        if let Some(item) = state.current {
            assert!(matches!(
                item.ty,
                Ty::Closure(_) | Ty::Bool | Ty::Vector(_, _) | Ty::U64 | Ty::Unit
            ));
        }
        drain(&mut state, &mut work);
        empty(&state);
    }
    assert!(current && pending);
}
#[test]
fn complete_child_shape_and_type_strings_plus_prior_arity_error_are_parent_held() {
    let m = rich_bad();
    let end = private_end(&m);
    let expected = symbol().shape_label();
    let mut held = false;
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
        assert_eq!(
            state.run(&m, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        held |= state.errors.len() == 1
            && state.expected == "bool"
            && state.actual == expected
            && state.detail == state.location;
        drain(&mut state, &mut work);
        empty(&state);
    }
    assert!(held);
}
#[test]
fn final_empty_and_nonempty_result_cannot_escape_original_publication_refusal() {
    for m in [fixture(), rich_bad()] {
        let (_, _, end) = run(&m);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_closure_constants_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn complete_successful_error_disposal_keeps_healthy_terminal_and_sticky_original_cause() {
    let m = rich_bad();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_closure_constants_observed(&m, &mut s, site()).unwrap();
    let end = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    drop(s);
    assert_eq!(
        *o.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
    let mut o = Observer {
        stop: Some(end + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_closure_constants_observed(&m, &mut s, site()).unwrap();
    assert_eq!(
        retire_validation_errors_observed(out, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original closure-constant stop"
    );
}
