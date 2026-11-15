// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn binding_trace(m: &Module) -> (Observer, usize) {
    let machine = &m.spec_modules[0];
    let property = &machine.temporal[0];
    let p = &m.proof_obligations[0];
    let (name, binding) = &p.formula.as_ref().unwrap().bindings[0];
    let mut state = seeded();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state
        .binding(p, name, binding, 0, true, Some((machine, property)), &mut w)
        .unwrap();
    let end = calls.get();
    let mut expected = vec![prior()];
    expected.extend(ordinary(m));
    assert_eq!(state.errors, expected);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    drop(w);
    drop(s);
    (o, end)
}
fn child_bound(m: &Module, debug: bool) -> (Observer, usize) {
    let machine = &m.spec_modules[0];
    let p = &m.proof_obligations[0];
    let (name, binding) = &p.formula.as_ref().unwrap().bindings[0];
    let mut state = seeded();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    // Identical real State.binding prefix through the selected actual child,
    // excluding no wrapper header and relying on no global ABI-size ordinal.
    w.admit(1, size_of::<usize>()).unwrap();
    let variable = w.at(&machine.vars, 0).unwrap().unwrap();
    w.admit(1, size_of::<Option<String>>()).unwrap();
    assert!(state.sort.is_none());
    state.sort = variable
        .effective_sort_mismatch_observed(&binding.sort, w.session, w.site)
        .unwrap();
    if debug {
        w.admit(1, size_of::<bool>()).unwrap();
        assert!(state.sort.is_some());
        state.prefix(name, 0, true, &mut w).unwrap();
        w.text(" (", &mut state.detail).unwrap();
        w.quoted(&variable.name, &mut state.detail).unwrap();
        w.text(") at sort ", &mut state.detail).unwrap();
        w.admit(1, size_of::<String>()).unwrap();
        assert_eq!(state.debug.capacity(), 0);
        state.debug = binding.sort.debug_observed(w.session, w.site).unwrap();
    }
    let bound = calls.get();
    drain(&mut state, &mut w);
    assert!(empty(&state));
    drop(w);
    drop(s);
    (o, bound)
}
#[test]
fn full_effective_sort_child_is_retained_before_the_first_post_return_callback() {
    let m = fixture();
    let (prefix, bound) = child_bound(&m, false);
    let (base, _) = binding_trace(&m);
    assert_eq!(&prefix.events[..bound], &base.events[..bound]);
    let stop = bound + 1;
    let mut state = seeded();
    let mut o = Observer {
        stop: Some(stop),
        cleanup_after: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let p = &m.proof_obligations[0];
    let (name, binding) = &p.formula.as_ref().unwrap().bindings[0];
    assert_eq!(
        state.binding(
            p,
            name,
            binding,
            0,
            true,
            Some((&m.spec_modules[0], &m.spec_modules[0].temporal[0])),
            &mut w
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.sort, Some("Int".into()));
    assert!(state.detail.is_empty());
    assert_eq!(state.errors, vec![prior()]);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original spec-surface stop"
    );
}
#[test]
fn complete_binding_debug_child_and_declared_sort_coexist_with_partial_detail_at_refusal() {
    let mut m = fixture();
    m.proof_obligations[0].formula.as_mut().unwrap().bindings[0]
        .1
        .sort = nested();
    let (prefix, bound) = child_bound(&m, true);
    let (base, _) = binding_trace(&m);
    assert_eq!(&prefix.events[..bound], &base.events[..bound]);
    let stop = bound + 1;
    let p = &m.proof_obligations[0];
    let (name, binding) = &p.formula.as_ref().unwrap().bindings[0];
    let mut state = seeded();
    let mut o = Observer {
        stop: Some(stop),
        cleanup_after: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        state.binding(
            p,
            name,
            binding,
            0,
            true,
            Some((&m.spec_modules[0], &m.spec_modules[0].temporal[0])),
            &mut w
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.debug, format!("{:?}", binding.sort));
    assert_eq!(state.sort, Some("Int".into()));
    assert_eq!(
        state.detail,
        "binds \"y\" to SpecVarNext 0 (\"x\") at sort "
    );
    assert_eq!(state.errors, vec![prior()]);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn interior_name_formatting_stop_keeps_the_owned_sort_whole_and_detail_prefix_until_drain() {
    let mut m = fixture();
    m.proof_obligations[0].formula.as_mut().unwrap().bindings[0].0 = "λ\n".repeat(400);
    let (_, bound) = child_bound(&m, false);
    let (base, end) = binding_trace(&m);
    let stop = bound + 100;
    assert!(stop < end);
    assert_eq!(base.events[stop - 1].phase, ExecutionPhase::Validation);
    let expected = match &ordinary(&m)[0] {
        ValidationError::InvalidObligationBinding { detail, .. } => detail.clone(),
        _ => panic!("wrong variant"),
    };
    let p = &m.proof_obligations[0];
    let (name, binding) = &p.formula.as_ref().unwrap().bindings[0];
    let mut state = seeded();
    let mut o = Observer {
        stop: Some(stop),
        cleanup_after: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        state.binding(
            p,
            name,
            binding,
            0,
            true,
            Some((&m.spec_modules[0], &m.spec_modules[0].temporal[0])),
            &mut w
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.sort, Some("Int".into()));
    assert!(!state.detail.is_empty());
    assert!(state.detail.len() < expected.len());
    assert!(expected.starts_with(&state.detail));
    assert_eq!(state.errors, vec![prior()]);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    drop(w);
    drop(s);
    assert!(
        o.events[stop..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn a_later_real_row_refusal_preserves_every_prior_diagnostic_until_complete_sticky_cleanup() {
    let m = fixture();
    let p = &m.proof_obligations[0];
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let bound;
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = seeded();
        state.row(&m, p, &mut w).unwrap();
        bound = calls.get();
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    let stop = bound + 1;
    let mut o = Observer {
        stop: Some(stop),
        cleanup_after: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    state.row(&m, p, &mut w).unwrap();
    let expected = state.errors.clone();
    let mut exact = vec![prior()];
    exact.extend(ordinary(&m));
    assert_eq!(expected, exact);
    assert_eq!(
        state.row(&m, p, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, expected);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original spec-surface stop"
    );
}
#[test]
fn actual_output_reserve_and_transport_cutoffs_hold_all_pending_fields_and_owned_prefix() {
    let m = fixture();
    let p = &m.proof_obligations[0];
    let emitting = || State {
        machine: "raw machine λ\0TAIL".into(),
        temporal: "raw temporal 尾\0TAIL".into(),
        detail: "whole reason λ\0TAIL".into(),
        sort: Some("whole declared sort".into()),
        debug: "whole child Debug".into(),
        errors: vec![prior()],
    };
    let mut base = Observer::default();
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = emitting();
        assert_eq!(state.errors.len(), state.errors.capacity());
        state.emit(p, &mut w).unwrap();
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    assert_eq!((base.events[0].work, base.events[0].copy_bytes), (1, 0));
    assert_eq!(
        (base.events[1].work, base.events[1].copy_bytes),
        (4, 4 * size_of::<ValidationError>())
    );
    assert_eq!(
        (base.events[2].work, base.events[2].copy_bytes),
        (1, size_of::<ValidationError>() + size_of::<String>())
    );
    for stop in [2, 3] {
        let mut state = emitting();
        let before = state.errors.capacity();
        let mut o = Observer {
            stop: Some(stop),
            cleanup_after: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.emit(p, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.machine, "raw machine λ\0TAIL");
        assert_eq!(state.temporal, "raw temporal 尾\0TAIL");
        assert_eq!(state.detail, "whole reason λ\0TAIL");
        assert_eq!(state.sort, Some("whole declared sort".into()));
        assert_eq!(state.debug, "whole child Debug");
        assert_eq!(state.errors, vec![prior()]);
        if stop == 2 {
            assert_eq!(state.errors.capacity(), before);
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
    }
}
#[test]
fn actual_unresolved_reference_keeps_complete_first_raw_name_before_second_name_copy() {
    let p = obligation(9, ObligationKind::Liveness);
    let spec = SpecObligationRef::new("machineλ\0FULL".repeat(200), "temporal尾\0FULL".repeat(200));
    let reason = "no SpecModule of this module carries that machine name";
    let mut prefix = Observer::default();
    let calls = prefix.calls.clone();
    let bound;
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut prefix);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = seeded();
        w.text(&spec.machine, &mut state.machine).unwrap();
        bound = calls.get();
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    let mut base = Observer::default();
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = seeded();
        state.reference(&p, &spec, reason, &mut w).unwrap();
        assert_eq!(
            state.errors[1],
            ValidationError::UnresolvedObligationSpecRef {
                obligation: 9,
                machine: spec.machine.clone(),
                temporal: spec.temporal.clone(),
                reason
            }
        );
        drain(&mut state, &mut w);
    }
    assert_eq!(&prefix.events[..bound], &base.events[..bound]);
    let stop = bound + 1;
    let mut o = Observer {
        stop: Some(stop),
        cleanup_after: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    assert_eq!(
        state.reference(&p, &spec, reason, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.machine, spec.machine);
    assert!(state.temporal.is_empty());
    assert_eq!(state.errors, vec![prior()]);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn partial_second_raw_reference_name_and_complete_first_name_stay_owned_through_refusal() {
    let p = obligation(9, ObligationKind::Liveness);
    let spec = SpecObligationRef::new("rawM", "λ".repeat(1200));
    let reason = "the machine name is ambiguous in this module";
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let bound;
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = seeded();
        w.text(&spec.machine, &mut state.machine).unwrap();
        bound = calls.get();
        drain(&mut state, &mut w);
    }
    let stop = bound + 5;
    let mut o = Observer {
        stop: Some(stop),
        cleanup_after: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    assert_eq!(
        state.reference(&p, &spec, reason, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.machine, spec.machine);
    assert_eq!(state.temporal, &spec.temporal[..1024]);
    assert_eq!(state.errors, vec![prior()]);
    let first = w.session.first_refusal().unwrap().progress;
    assert_eq!((first.work, first.copy_bytes), (1, size_of::<usize>()));
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(w.session.first_refusal().unwrap().progress, first);
    drop(w);
    drop(s);
    assert_eq!(&o.events[..bound], &base.events[..bound]);
    assert_eq!(
        (o.events[bound + 2].work, o.events[bound + 2].copy_bytes),
        (1024, 1024)
    );
    assert_eq!(
        (o.events[bound + 3].work, o.events[bound + 3].copy_bytes),
        (1024, 1024)
    );
    assert!(
        o.events[stop..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
