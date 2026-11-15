// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
const PREFIX: &str = "the key ";
const TYPE: &str = "retained child type λ\0FULLTAIL";
const WHY: &str = "complete pending reason 尾\0FULLTAIL";
fn child_bound(ty: &Ty) -> (Observer, usize) {
    let mut state = seeded();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    // Same observed prefix of key_reason through its actual display child.
    w.text(PREFIX, &mut state.reason).unwrap();
    w.admit(1, size_of::<String>()).unwrap();
    assert_eq!(state.ty.capacity(), 0);
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
fn key_trace(ty: &Ty) -> (Observer, usize) {
    let mut state = seeded();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.key_reason(ty, KeyRule::Trivial, &mut w).unwrap();
    let end = calls.get();
    assert_eq!(state.reason, key_text(ty, false));
    assert_eq!(state.ty.capacity(), 0);
    let out = state.finish(Ok(()), &mut w).unwrap();
    assert_eq!(out, vec![prior()]);
    assert!(empty(&state));
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    (o, end)
}
fn emitting() -> State {
    State {
        ty: TYPE.into(),
        reason: WHY.into(),
        errors: vec![prior()],
    }
}
fn emit_trace() -> Observer {
    let mut state = emitting();
    assert_eq!(state.errors.len(), state.errors.capacity());
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.emit(usize::MAX, u32::MAX, &mut w).unwrap();
    let out = state.finish(Ok(()), &mut w).unwrap();
    assert_eq!(out, vec![prior(), error(usize::MAX, u32::MAX, WHY)]);
    assert!(empty(&state));
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    o
}
#[test]
fn complete_type_child_return_is_owned_before_the_first_append_callback() {
    let ty = Ty::Tuple(vec![Ty::U8; 600]);
    let full = ty.to_string();
    let (prefix, begin) = child_bound(&ty);
    let (base, _) = key_trace(&ty);
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
    let result = state.key_reason(&ty, KeyRule::Trivial, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.ty, full);
    assert_eq!(state.reason, PREFIX);
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
fn a_partial_reason_retains_the_full_type_child_and_prior_error_until_same_owner_cleanup() {
    let ty = Ty::Tuple(vec![Ty::U8; 600]);
    let full = ty.to_string();
    assert!(full.len() > 2048);
    let (_, begin) = child_bound(&ty);
    let (base, end) = key_trace(&ty);
    // After the exact child return, the existing nonempty prefix makes the
    // growth charge larger than 1024; the first 1024 event is actual text copy.
    let copy = base.events[begin..end]
        .iter()
        .position(|e| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .unwrap()
        + begin;
    let stop = copy + 2;
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
    let result = state.key_reason(&ty, KeyRule::Trivial, &mut w);
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
fn partial_actual_raw_function_name_is_retained_before_signature_types_are_visited() {
    let f = function(7, &"é".repeat(1600), true);
    let signature = FuncTy::unrecorded(vec![Ty::Tuple(vec![Ty::U8; 600])], vec![Ty::Unit], true);
    let mut state = seeded();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.signature_reason(&f, &signature, &mut w).unwrap();
    let end = calls.get();
    assert_eq!(state.reason, signature_text(&f, &signature));
    let out = state.finish(Ok(()), &mut w).unwrap();
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    // No type child precedes the name; its nonempty quote prefix makes the
    // first 1024 event in this narrow signature renderer an actual name copy.
    let copied = base.events[..end]
        .iter()
        .position(|e| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .unwrap();
    let stop = copied + 2;
    assert_eq!(
        (base.events[stop - 1].work, base.events[stop - 1].copy_bytes),
        (1, size_of::<usize>())
    );
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
    let result = state.signature_reason(&f, &signature, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.reason, format!("the glue '{}", &f.name[..1024]));
    assert_eq!(state.ty.capacity(), 0);
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
fn error_reserve_and_transport_refusals_hold_whole_child_reason_and_prior_prefix() {
    let base = emit_trace();
    let start = emitting();
    assert_eq!(start.errors.len(), start.errors.capacity());
    let images = start.errors.len() * 2 + 1 + start.errors.capacity();
    assert_eq!(
        (
            base.events[0].phase,
            base.events[0].work,
            base.events[0].copy_bytes
        ),
        (ExecutionPhase::Validation, 1, 0)
    );
    assert_eq!(
        (base.events[1].work, base.events[1].copy_bytes),
        (images, images * size_of::<ValidationError>())
    );
    assert_eq!(
        (base.events[2].work, base.events[2].copy_bytes),
        (2, size_of::<ValidationError>() + size_of::<String>())
    );
    for stop in [2, 3] {
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
        let result = state.emit(usize::MAX, u32::MAX, &mut w);
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
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
            "original glue-table stop"
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
fn every_finish_callback_and_final_publication_consumes_all_owned_text_and_prior_rows() {
    let make = || State {
        ty: TYPE.into(),
        reason: WHY.into(),
        errors: vec![
            prior(),
            error(usize::MAX, u32::MAX, "second full reason 尾\0TAIL"),
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
            error(usize::MAX, u32::MAX, "second full reason 尾\0TAIL")
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
            "original glue-table stop"
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
    // Flat String retirement is its actual header/drop contract, not a byte walk.
}
