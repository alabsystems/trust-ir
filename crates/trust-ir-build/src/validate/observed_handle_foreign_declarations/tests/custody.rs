// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_handle_child_and_all_fields_remain_owned_across_parent_allocation_cuts() {
    let (m, r) = fixture();
    let f = &m.functions[0];
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let begin = calls.get();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state
        .function(&m, f, &r, &nominal, ImportPolicy::Refuse, &mut work)
        .unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    nominal.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut child = false;
    let mut before = false;
    let mut after = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.function(&m, f, &r, &nominal, ImportPolicy::Refuse, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        if !state.handles.is_empty() && state.name.is_empty() {
            child = true;
        }
        if state.name == f.name
            && !state.handles.is_empty()
            && !state.detail.is_empty()
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
        drop(work);
        let _ = nominal.retire_observed(&mut s, site());
    }
    assert!(child && before && after);
}
#[test]
fn earlier_complete_rows_remain_owned_during_every_later_partial_field_and_refused_transfer() {
    let (m, r) = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let begin = calls.get();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state
        .run(&m, &r, &nominal, ImportPolicy::Refuse, &mut work)
        .unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    nominal.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut prior = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            cleanup_after: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.run(&m, &r, &nominal, ImportPolicy::Refuse, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        prior |= !state.errors.is_empty()
            && (!state.detail.is_empty() || !state.handles.is_empty() || !state.name.is_empty());
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original foreign stop"
        );
        drop(work);
        let _ = nominal.retire_observed(&mut s, site());
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
fn sticky_cleanup_exhausts_every_partial_field_and_nested_prior_error_without_accepting_output() {
    let mut state = State {
        name: "name λ\0".into(),
        handles: "full handles 尾".into(),
        detail: "full detail\0".into(),
        errors: vec![ValidationError::HandleForeignDeclaration {
            function: 0,
            name: "prior name".into(),
            handle: "prior full handle".into(),
            detail: "prior full detail".into(),
        }],
    };
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
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(work);
    drop(s);
    assert!(
        o.events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn healthy_returned_vector_stays_original_custodied_until_full_explicit_caller_retirement() {
    let (m, r) = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let out = validate_handle_foreign_declarations_observed(
        &m,
        &r,
        &nominal,
        ImportPolicy::Refuse,
        &mut s,
        site(),
    )
    .unwrap();
    let begin = calls.get();
    assert_eq!(out.len(), 2);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    let end = calls.get();
    nominal.retire_observed(&mut s, site()).unwrap();
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
#[test]
fn actual_any_query_stops_at_first_handle_without_walking_later_return_slots() {
    let m = Module::new("");
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let first = FuncTy::unrecorded(vec![Ty::handle("Name", "rt::Name")], vec![Ty::Bool], false);
    let second = FuncTy::unrecorded(
        first.params.clone(),
        vec![Ty::Tuple(vec![Ty::Bool; 1024]); 256],
        false,
    );
    let state = State::default();
    let begin = calls.get();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(state.reaches_handle(&first, &nominal, &mut work).unwrap());
    let middle = calls.get();
    assert!(state.reaches_handle(&second, &nominal, &mut work).unwrap());
    let end = calls.get();
    drop(work);
    nominal.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert_eq!(&o.events[begin..middle], &o.events[middle..end]);
}
