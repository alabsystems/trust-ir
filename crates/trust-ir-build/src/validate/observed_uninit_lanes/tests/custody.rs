// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn detail_trace(ty: &Ty, value: &Constant) -> (Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    state.constant_detail(ty, value, &mut w).unwrap();
    assert_eq!(
        state.actual,
        format!("{ty} constant {value} carries uninit outside a direct lane")
    );
    let bound = calls.get();
    drain(&mut state, &mut w);
    assert!(empty(&state));
    drop(w);
    drop(s);
    (o, bound)
}
fn child_bound(ty: &Ty, value: &Constant, constant_child: bool) -> (Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    // Same actual constant_detail prefix through the selected real child.
    w.admit(1, size_of::<Option<String>>()).unwrap();
    assert!(state.render.is_none());
    state.render = Some(ty.display_observed(w.session, w.site).unwrap());
    if constant_child {
        state.copy_render(&mut w).unwrap();
        w.text(" constant ", &mut state.actual).unwrap();
        w.admit(1, size_of::<Option<String>>()).unwrap();
        state.render = Some(value.display_observed(w.session, w.site).unwrap());
    }
    let bound = calls.get();
    drain(&mut state, &mut w);
    assert!(empty(&state));
    drop(w);
    drop(s);
    (o, bound)
}
#[test]
fn complete_type_and_constant_child_returns_are_owned_before_first_parent_copy_refusal() {
    let ty = Ty::Tuple(vec![Ty::U8; 300]);
    let value = Constant::Aggregate(vec![Constant::Float(1.25), Constant::Uninit]);
    for constant_child in [false, true] {
        let (prefix, bound) = child_bound(&ty, &value, constant_child);
        let (base, _) = detail_trace(&ty, &value);
        assert_eq!(&prefix.events[..bound], &base.events[..bound]);
        let stop = bound + 1;
        let mut o = Observer {
            stop: Some(stop),
            cleanup: true,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = seeded();
        assert_eq!(
            state.constant_detail(&ty, &value, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            state.render,
            Some(if constant_child {
                value.to_string()
            } else {
                ty.to_string()
            })
        );
        assert_eq!(
            state.actual,
            if constant_child {
                format!("{ty} constant ")
            } else {
                String::new()
            }
        );
        assert_eq!(state.errors, vec![prior()]);
        drain(&mut state, &mut w);
        assert!(empty(&state));
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "uninit original stop"
        );
    }
}
#[test]
fn partial_constant_copy_retains_the_full_child_text_prior_output_and_exact_prefix_until_drain() {
    let ty = Ty::U8;
    let value = Constant::Aggregate(vec![
        Constant::SymbolAddr {
            symbol: "λ".repeat(1500),
            addend: 0,
        },
        Constant::Uninit,
    ]);
    let (_, bound) = child_bound(&ty, &value, true);
    let (base, end) = detail_trace(&ty, &value);
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
    let mut o = Observer {
        stop: Some(stop),
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    assert_eq!(
        state.constant_detail(&ty, &value, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    let full = value.to_string();
    let mut boundary = 1024;
    while !full.is_char_boundary(boundary) {
        boundary -= 1;
    }
    assert_eq!(state.render, Some(full.clone()));
    assert_eq!(state.actual, format!("u8 constant {}", &full[..boundary]));
    assert_eq!(state.errors, vec![prior()]);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn traversal_reserve_refusal_keeps_the_pending_full_sibling_iterator_before_allocation() {
    let value = Constant::Aggregate(vec![Constant::Int(1), Constant::Uninit]);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert!(state.preorder(&value, &mut w).unwrap());
    state.retire_frames(&mut w);
    drop(w);
    drop(s);
    let stop = base
        .events
        .iter()
        .position(|e| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ConstantChildren<'_>>()
        })
        .unwrap()
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    assert_eq!(
        state.preorder(&value, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.frames.capacity(), 0);
    assert_eq!(state.pending.as_ref().unwrap().len(), 1);
    assert_eq!(state.errors, vec![prior()]);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn already_suspended_stack_and_pending_child_are_drained_even_after_repeated_cleanup_refusals() {
    let mut value = Constant::Int(1);
    for _ in 0..40 {
        value = Constant::Aggregate(vec![value, Constant::Int(2)]);
    }
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert!(!state.preorder(&value, &mut w).unwrap());
    state.retire_frames(&mut w);
    drop(w);
    drop(s);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 18
                && e.copy_bytes == size_of::<Option<ConstantChildren<'_>>>()
        })
        .nth(20)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    assert_eq!(
        state.preorder(&value, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.frames.len() >= 19);
    assert_eq!(state.errors, vec![prior()]);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "uninit original stop"
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
fn diagnostic_reserve_and_transport_refusals_keep_all_three_full_fields_and_prior_errors() {
    let pending = || State {
        location: "whole location λ\0TAIL".into(),
        actual: "whole actual 尾\0TAIL".into(),
        render: Some("full child".into()),
        errors: vec![prior()],
        ..State::default()
    };
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = pending();
    state.emit(&mut w).unwrap();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    let reserve = base
        .events
        .iter()
        .position(|e| {
            e.phase == ExecutionPhase::Validation
                && e.work == 4
                && e.copy_bytes == 4 * size_of::<ValidationError>()
        })
        .unwrap()
        + 1;
    let transport = base
        .events
        .iter()
        .position(|e| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>() + 3 * size_of::<String>()
        })
        .unwrap()
        + 1;
    for stop in [reserve, transport] {
        let mut o = Observer {
            stop: Some(stop),
            cleanup: true,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = pending();
        let before = state.errors.capacity();
        assert_eq!(
            state.emit(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.location, "whole location λ\0TAIL");
        assert_eq!(state.expected, EXPECTED);
        assert_eq!(state.actual, "whole actual 尾\0TAIL");
        assert_eq!(state.render, Some("full child".into()));
        assert_eq!(state.errors, vec![prior()]);
        if stop == reserve {
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
fn later_global_refusal_keeps_every_prior_full_error_until_same_owner_drain() {
    let mut m = Module::new("");
    m.globals.push(global("first", Some(Constant::Uninit)));
    m.globals
        .push(global(&"λ".repeat(2000), Some(Constant::Uninit)));
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    state.walk(&m, &mut w).unwrap();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    let stop = base
        .events
        .iter()
        .position(|e| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .unwrap()
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    assert_eq!(
        state.walk(&m, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    let mut expected = vec![prior()];
    expected.push(ordinary(&m).remove(0));
    assert_eq!(state.errors, expected);
    assert!(state.location.starts_with("global '"));
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn deep_unary_splats_need_no_heap_traversal_stack_and_stop_on_the_first_uninit() {
    let mut value = Constant::Uninit;
    for _ in 0..10_000 {
        value = Constant::Splat {
            elem: Box::new(value),
            len: u64::MAX,
        };
    }
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert!(state.preorder(&value, &mut w).unwrap());
    assert_eq!(state.frames.capacity(), 0);
    assert!(state.pending.is_none());
    drain(&mut state, &mut w);
    assert!(empty(&state));
    drop(state);
    drop(w);
    drop(s);
    // The test owns its borrowed input and consumes the deep fixture iteratively.
    loop {
        match value {
            Constant::Splat { elem, .. } => value = *elem,
            Constant::Uninit => break,
            _ => panic!("changed fixture"),
        }
    }
}
