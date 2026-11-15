// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
const PREFIX: &str = "a drop of the trivially droppable type ";
const WHY: &str = "retained full reason λ\0TAIL";
const TYPE: &str = "retained child type 尾\0TAIL";
fn empty_function() -> Function {
    let mut m = module(vec![]);
    m.functions.remove(0)
}
fn child_bound(ty: &Ty) -> (Observer, usize) {
    let mut state = seeded();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    // Same observed prefix as type_reason; assertions establish its empty guards.
    w.admit(2, size_of::<String>() + size_of::<TypeRule>())
        .unwrap();
    assert_eq!(state.ty.capacity(), 0);
    assert_eq!(state.reason.capacity(), 0);
    state.ty = ty.display_observed(w.session, w.site).unwrap();
    let bound = calls.get();
    let out = state.finish(Ok(()), &mut w).unwrap();
    assert_eq!(out, vec![prior()]);
    assert!(empty(&state));
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    (o, bound)
}
fn type_trace(ty: &Ty) -> (Observer, usize) {
    let mut state = seeded();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.type_reason(ty, TypeRule::Trivial, &mut w).unwrap();
    let bound = calls.get();
    assert_eq!(state.reason, type_reason(ty, false));
    assert_eq!(state.ty.capacity(), 0);
    let out = state.finish(Ok(()), &mut w).unwrap();
    assert_eq!(out, vec![prior()]);
    assert!(empty(&state));
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    (o, bound)
}
fn emitting() -> State {
    State {
        ty: TYPE.into(),
        reason: WHY.into(),
        errors: vec![prior()],
        ..State::default()
    }
}
fn emit_trace(function: &Function) -> (Observer, usize, usize) {
    let mut state = emitting();
    assert_eq!(state.errors.len(), state.errors.capacity());
    let images = state.errors.len() * 2 + 1 + state.errors.capacity();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.emit(function, 7, &mut w).unwrap();
    let bound = calls.get();
    let out = state.finish(Ok(()), &mut w).unwrap();
    assert_eq!(out, vec![prior(), error(&function.name, 7, WHY)]);
    assert!(empty(&state));
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    (o, bound, images)
}
#[test]
fn complete_type_child_string_is_retained_before_the_first_reason_callback() {
    let ty = Ty::Tuple(vec![Ty::U8; 600]);
    let full = ty.to_string();
    let (prefix, begin) = child_bound(&ty);
    let (base, _) = type_trace(&ty);
    assert_eq!(&prefix.events[..begin], &base.events[..begin]);
    let stop = begin + 1;
    let mut state = seeded();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let result = state.type_reason(&ty, TypeRule::Trivial, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.ty, full);
    assert_eq!(state.reason.capacity(), 0);
    assert_eq!(state.errors, vec![prior()]);
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    assert_eq!(
        state.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
}
#[test]
fn partial_reason_and_full_returned_type_coexist_with_prior_errors_at_an_interior_copy_stop() {
    let ty = Ty::Tuple(vec![Ty::U8; 600]);
    let full = ty.to_string();
    assert!(full.len() > 2048);
    let (_, begin) = child_bound(&ty);
    let (base, end) = type_trace(&ty);
    // Restrict to reason rendering AFTER the exact child return. Its prefix
    // makes allocation work larger than 1024; the first 1024 event is real copy.
    let copied = base.events[begin..end]
        .iter()
        .position(|e| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .unwrap()
        + begin;
    let stop = copied + 2;
    assert_eq!(
        (base.events[stop - 1].work, base.events[stop - 1].copy_bytes),
        (1, size_of::<usize>())
    );
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
    let result = state.type_reason(&ty, TypeRule::Trivial, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.ty, full);
    assert_eq!(state.reason, format!("{PREFIX}{}", &full[..1024]));
    assert_eq!(state.errors, vec![prior()]);
    assert_eq!(
        state.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
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
fn actual_partial_unicode_function_name_preserves_full_reason_type_and_prior_output() {
    let mut f = empty_function();
    f.name = "é".repeat(1600);
    let (base, end, _) = emit_trace(&f);
    let windows = base.events[..end]
        .windows(3)
        .enumerate()
        .filter(|(_, es)| {
            es[0].phase == ExecutionPhase::Validation
                && es[0].work == 1024
                && es[0].copy_bytes == 1024
                && es[1] == es[0]
                && es[2].work == 1
                && es[2].copy_bytes == size_of::<usize>()
        })
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    assert_eq!(windows.len(), 1);
    let stop = windows[0] + 3;
    let mut state = emitting();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let result = state.emit(&f, 7, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.name, &f.name[..1024]);
    assert_eq!(state.ty, TYPE);
    assert_eq!(state.reason, WHY);
    assert_eq!(state.errors, vec![prior()]);
    assert_eq!(
        state.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn output_allocation_and_header_transport_stops_keep_all_owned_strings_and_prefix() {
    let f = empty_function();
    let (base, end, images) = emit_trace(&f);
    let fees = base.events[..end]
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == images
                && e.copy_bytes == images * size_of::<ValidationError>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(fees.len(), 1);
    let reserve = fees[0];
    assert_eq!(
        (
            base.events[reserve - 2].work,
            base.events[reserve - 2].copy_bytes
        ),
        (1, 0)
    );
    assert_eq!(
        (base.events[reserve].work, base.events[reserve].copy_bytes),
        (
            3,
            size_of::<ValidationError>() + 2 * size_of::<String>() + size_of::<u32>()
        )
    );
    for stop in [reserve, reserve + 1] {
        let mut state = emitting();
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
        let result = state.emit(&f, 7, &mut w);
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        assert_eq!(state.name, f.name);
        assert_eq!(state.ty, TYPE);
        assert_eq!(state.reason, WHY);
        assert_eq!(state.errors, vec![prior()]);
        assert_eq!(
            state.finish(result, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(empty(&state));
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original drop-site stop"
        );
        drop(w);
        drop(s);
        assert!(
            o.events[stop..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_finish_callback_including_publication_consumes_all_slots_despite_sticky_cleanup_refusals()
{
    let make = || State {
        ty: TYPE.into(),
        reason: WHY.into(),
        name: "partial name λ\0TAIL".into(),
        errors: vec![
            prior(),
            error(
                "second full name 尾",
                u32::MAX,
                "second full reason λ\0TAIL",
            ),
        ],
    };
    let mut state = make();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let out = state.finish(Ok(()), &mut w).unwrap();
    let bound = calls.get();
    assert!(empty(&state));
    assert_eq!(
        out,
        vec![
            prior(),
            error(
                "second full name 尾",
                u32::MAX,
                "second full reason λ\0TAIL"
            )
        ]
    );
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    assert_eq!(base.events[bound - 1].phase, ExecutionPhase::Publication);
    for stop in 1..=bound {
        let mut state = make();
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
            state.finish(Ok(()), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(empty(&state));
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original drop-site stop"
        );
        drop(w);
        drop(s);
        assert_eq!(&o.events[..stop], &base.events[..stop]);
        assert!(
            o.events[stop..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    // Flat String cleanup prices header/drop, not an invented byte walk.
}
