// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::proof::clause_typing::{
    clause_sort_admits_observed, resolve_clause_place_borrowed_observed,
};
fn render_fixture() -> Module {
    let mut m = fixture();
    m.func_types[0].params = vec![Ty::Tuple(vec![Ty::U8; 600])];
    set(
        &mut m,
        ClausePlace::Param { index: 0 },
        ClauseSort::Datatype {
            name: "D".repeat(3000),
            constructors: vec![],
        },
    );
    m
}
fn typed_trace(m: &Module) -> (Observer, usize) {
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
        .typing(m, &m.functions[0], p, name, binding, &mut w)
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
fn render_bound(m: &Module, ty_child: bool) -> (Observer, usize) {
    let function = &m.functions[0];
    let (name, binding) = &m.proof_obligations[0].formula.as_ref().unwrap().bindings[0];
    let mut state = seeded();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    // Exact real typing::check Param prefix; compare its trace against that
    // real entry before choosing the next callback, never a global size hit.
    w.admit(11, size_of::<ClausePlace>() + size_of::<Option<&Ty>>())
        .unwrap();
    let ty =
        resolve_clause_place_borrowed_observed(m, function.id, &binding.place, w.session, w.site)
            .unwrap()
            .unwrap();
    w.admit(4, size_of::<Option<u32>>()).unwrap();
    assert!(!clause_sort_admits_observed(&binding.sort, ty, None, w.session, w.site).unwrap());
    w.admit(1, 0).unwrap();
    assert_eq!(state.detail.capacity(), 0);
    w.text("binding ", &mut state.detail).unwrap();
    w.quoted(name, &mut state.detail).unwrap();
    w.text(" has sort ", &mut state.detail).unwrap();
    w.admit(1, size_of::<Option<String>>()).unwrap();
    assert!(state.render.is_none());
    state.render = Some(binding.sort.debug_observed(w.session, w.site).unwrap());
    if ty_child {
        w.admit(1, size_of::<Option<&str>>()).unwrap();
        w.text(state.render.as_deref().unwrap(), &mut state.detail)
            .unwrap();
        w.step(size_of::<Option<String>>().saturating_add(1));
        if let Some(text) = state.render.take() {
            w.flat(text);
        }
        w.admit(1, 0).unwrap();
        w.text(" but ", &mut state.detail).unwrap();
        place_text(binding.place, &mut state.detail, &mut w).unwrap();
        w.text(" is ", &mut state.detail).unwrap();
        w.admit(1, size_of::<Option<String>>()).unwrap();
        assert!(state.render.is_none());
        state.render = Some(ty.display_observed(w.session, w.site).unwrap());
    }
    let bound = calls.get();
    drain(&mut state, &mut w);
    assert!(empty(&state));
    drop(w);
    drop(s);
    (o, bound)
}
#[test]
fn actual_complete_inferred_map_is_owned_before_first_lookup_can_refuse() {
    let mut m = fixture();
    set(&mut m, ClausePlace::Value(v(5)), ClauseSort::Int);
    let function = &m.functions[0];
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
        w.admit(11, size_of::<ClausePlace>() + size_of::<Option<&Ty>>())
            .unwrap();
        w.admit(1, size_of::<bool>()).unwrap();
        assert!(!function.blocks.is_empty());
        assert!(scan::defined(function, v(5), &mut w).unwrap());
        w.admit(1, size_of::<Option<ObservedValueTypes>>()).unwrap();
        assert!(state.values.is_none());
        state.values =
            Some(build_module_value_types_observed(function, &m, w.session, w.site).unwrap());
        bound = calls.get();
        assert_eq!(
            state
                .values
                .as_ref()
                .unwrap()
                .get_observed(v(4), w.session, w.site)
                .unwrap(),
            Some(&Ty::U32)
        );
        assert_eq!(
            state
                .values
                .as_ref()
                .unwrap()
                .get_observed(v(5), w.session, w.site)
                .unwrap(),
            Some(&Ty::Bool)
        );
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    let (base, _) = typed_trace(&m);
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
    let p = &m.proof_obligations[0];
    let (name, binding) = &p.formula.as_ref().unwrap().bindings[0];
    assert_eq!(
        state.typing(&m, function, p, name, binding, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.values.is_some());
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
        "original obligation-binding stop"
    );
}
#[test]
fn complete_sort_debug_child_remains_owned_before_the_first_copy_callback() {
    let m = render_fixture();
    let (prefix, bound) = render_bound(&m, false);
    let (base, _) = typed_trace(&m);
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
    let p = &m.proof_obligations[0];
    let (name, binding) = &p.formula.as_ref().unwrap().bindings[0];
    assert_eq!(
        state.typing(&m, &m.functions[0], p, name, binding, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.render, Some(format!("{:?}", binding.sort)));
    assert_eq!(state.detail, "binding \"x\" has sort ");
    assert_eq!(state.errors, vec![prior()]);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn complete_type_display_child_coexists_with_whole_sort_prefix_until_refusal_cleanup() {
    let m = render_fixture();
    let (prefix, bound) = render_bound(&m, true);
    let (base, _) = typed_trace(&m);
    assert_eq!(&prefix.events[..bound], &base.events[..bound]);
    let stop = bound + 1;
    let p = &m.proof_obligations[0];
    let (name, binding) = &p.formula.as_ref().unwrap().bindings[0];
    let ty = &m.func_types[0].params[0];
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
        state.typing(&m, &m.functions[0], p, name, binding, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.render, Some(ty.to_string()));
    assert_eq!(
        state.detail,
        format!("binding \"x\" has sort {:?} but Param 0 is ", binding.sort)
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
fn partial_diagnostic_copy_keeps_full_returned_render_and_all_prior_output_in_custody() {
    let m = render_fixture();
    let (_, bound) = render_bound(&m, false);
    let (base, end) = typed_trace(&m);
    let copied = base.events[bound..end]
        .iter()
        .position(|e| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .unwrap()
        + bound;
    let stop = copied + 2;
    assert_eq!(
        (base.events[stop - 1].work, base.events[stop - 1].copy_bytes),
        (1, size_of::<usize>())
    );
    let p = &m.proof_obligations[0];
    let (name, binding) = &p.formula.as_ref().unwrap().bindings[0];
    let full = format!("{:?}", binding.sort);
    assert!(full.len() > 2048);
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
        state.typing(&m, &m.functions[0], p, name, binding, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.render, Some(full.clone()));
    assert_eq!(
        state.detail,
        format!("binding \"x\" has sort {}", &full[..1024])
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
fn output_reserve_and_transport_cutoffs_retain_pending_text_render_and_complete_prefix() {
    let p = obligation();
    let pending = || State {
        detail: "complete diagnostic λ\0TAIL".into(),
        render: Some("complete child render 尾\0TAIL".into()),
        errors: vec![prior()],
        ..State::default()
    };
    let mut base = Observer::default();
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = pending();
        assert_eq!(state.errors.len(), state.errors.capacity());
        state.emit(&p, &mut w).unwrap();
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
        let mut state = pending();
        let capacity = state.errors.capacity();
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
            state.emit(&p, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.detail, "complete diagnostic λ\0TAIL");
        assert_eq!(state.render, Some("complete child render 尾\0TAIL".into()));
        assert_eq!(state.errors, vec![prior()]);
        if stop == 2 {
            assert_eq!(state.errors.capacity(), capacity);
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
fn actual_map_retirement_refusal_consumes_every_owned_row_without_releasing_prior_diagnostics() {
    let m = fixture();
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
        state.values = Some(
            build_module_value_types_observed(&m.functions[0], &m, w.session, w.site).unwrap(),
        );
        bound = calls.get();
        state.clear_values(&mut w).unwrap();
        assert!(state.values.is_none());
        drain(&mut state, &mut w);
    }
    let stop = bound + 1;
    assert_eq!(
        base.events[stop - 1].phase,
        ExecutionPhase::ScratchRetirement
    );
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
    state.values =
        Some(build_module_value_types_observed(&m.functions[0], &m, w.session, w.site).unwrap());
    assert_eq!(
        state.clear_values(&mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.values.is_none());
    assert_eq!(state.errors, vec![prior()]);
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original obligation-binding stop"
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
fn later_row_stop_preserves_prior_real_type_diagnostic_after_its_full_map_was_retired() {
    let mut m = fixture();
    set(&mut m, ClausePlace::Value(v(5)), ClauseSort::Int);
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
        state.clear_values(&mut w).unwrap();
        bound = calls.get();
        drain(&mut state, &mut w);
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
    state.clear_values(&mut w).unwrap();
    let mut expected = vec![prior()];
    expected.extend(ordinary(&m));
    assert_eq!(state.errors, expected);
    assert!(state.values.is_none());
    assert_eq!(
        state.row(&m, p, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, expected);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original obligation-binding stop"
    );
}
