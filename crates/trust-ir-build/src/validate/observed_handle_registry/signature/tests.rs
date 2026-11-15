// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::tests::{Observer, entry, pin, site};
use super::*;
use trust_ir::interpret::InterpretOptions;
fn fresh_state() -> State {
    State {
        signature: FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        },
        pending: None,
        name: String::new(),
        runtime: String::new(),
    }
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    work.retire_types(&mut state.signature.params);
    work.retire_types(&mut state.signature.returns);
}
fn empty(state: &State) -> bool {
    state.pending.is_none()
        && state.name.capacity() == 0
        && state.runtime.capacity() == 0
        && state.signature.params.capacity() == 0
        && state.signature.returns.capacity() == 0
}
#[test]
fn complete_scalar_child_stays_pending_before_and_after_parent_vector_allocation_refusal() {
    let p = pin(vec![]);
    let source = Ty::Tuple(vec![Ty::Bool, Ty::handle("Name", "Runtime")]);
    let e = entry("S", vec![PinnedTy::Scalar(source.clone())], vec![]);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = fresh_state();
    state.slots(&p, e.params, Side::Params, &mut work).unwrap();
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
        let mut state = fresh_state();
        assert_eq!(
            state.slots(&p, e.params, Side::Params, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        if state.pending.as_ref() == Some(&source) && state.signature.params.is_empty() {
            if state.signature.params.capacity() == 0 {
                before = true;
            } else {
                after = true;
            }
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
    assert!(before && after);
}
#[test]
fn complete_handle_strings_and_then_whole_boxed_type_are_held_until_parent_transfer() {
    let mut p = pin(vec![]);
    p.name = "λ\0rawName";
    p.runtime = "raw::尾\nRuntime";
    let e = entry("H", vec![PinnedTy::Handle], vec![]);
    let expected = p.handle_ty();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = fresh_state();
    state.slots(&p, e.params, Side::Params, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    let mut before_box = false;
    let mut before_output = false;
    let mut after_output = false;
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
        let mut state = fresh_state();
        assert_eq!(
            state.slots(&p, e.params, Side::Params, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        let event = baseline.events[cut - 1];
        if event.phase == ExecutionPhase::Validation
            && event.work == 1
            && event.copy_bytes == size_of::<HandleTy>() + size_of::<Ty>() + size_of::<Option<Ty>>()
        {
            // Completing the final runtime copy also leaves both strings
            // complete. Identify the actual Box admission, then require that
            // it still owns both complete strings before any allocation.
            before_box = true;
            assert!(state.pending.is_none());
            assert_eq!(state.name, p.name);
            assert_eq!(state.runtime, p.runtime);
        }
        if state.pending.as_ref() == Some(&expected) && state.signature.params.is_empty() {
            assert!(state.name.is_empty() && state.runtime.is_empty());
            if state.signature.params.capacity() == 0 {
                before_output = true;
            } else {
                after_output = true;
            }
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
    assert!(before_box && before_output && after_output);
}
#[test]
fn every_return_slot_cut_retains_prior_owned_parameters_and_all_partial_return_state() {
    let p = pin(vec![]);
    let e = entry(
        "R",
        vec![],
        vec![
            PinnedTy::Handle,
            PinnedTy::Scalar(Ty::Tuple(vec![Ty::Bool, Ty::U8])),
        ],
    );
    let prior = Ty::handle("Prior", "raw::Prior");
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = fresh_state();
    state.signature.params.push(prior.clone());
    state
        .slots(&p, e.returns, Side::Returns, &mut work)
        .unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    let mut complete_return = false;
    let mut pending_return = false;
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
        let mut state = fresh_state();
        state.signature.params.push(prior.clone());
        assert_eq!(
            state.slots(&p, e.returns, Side::Returns, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.signature.params, vec![prior.clone()]);
        complete_return |= !state.signature.returns.is_empty();
        pending_return |= state.pending.is_some();
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original registry-inner stop"
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
    assert!(complete_return && pending_return);
}
#[test]
fn sticky_cleanup_consumes_all_nested_parameters_returns_pending_type_and_raw_fields() {
    let mut state = fresh_state();
    state.signature.params = vec![Ty::Tuple(vec![Ty::handle("P", "r::P"), Ty::Bool])];
    state.signature.returns = vec![Ty::Ref(Box::new(Ty::handle("R", "r::R")))];
    state.pending = Some(Ty::Tuple(vec![Ty::handle("C", "r::C")]));
    state.name = "partial λ\0FULL".into();
    state.runtime = "partial 尾\0FULL".into();
    let mut o = Observer {
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.complete_retirement(),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(work);
    drop(s);
    assert!(
        o.events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events.len() > 30);
}
