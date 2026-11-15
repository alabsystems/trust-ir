// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_cast_callback_refuses_without_partial_diagnostics_or_renewed_fuel() {
    for (op, src, dst, actual) in [
        (CastOp::Trunc, Ty::Bool, Ty::U128, Ty::Ptr),
        (
            CastOp::Bitcast,
            Ty::Vector(Box::new(Ty::Bool), 8),
            Ty::U8,
            handle(),
        ),
        (
            CastOp::PtrToPtr,
            Ty::Ref(Box::new(handle())),
            Ty::Ptr,
            Ty::U8,
        ),
    ] {
        let entries = rows(actual);
        let values = values(&entries);
        let (_, baseline) = run(op, &src, &dst, &entries, v(0), MODES[0]);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                validate_cast_operands_observed(
                    7,
                    op,
                    &src,
                    &dst,
                    v(0),
                    &values,
                    MODES[0],
                    &mut session,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "original cast stop");
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn two_casts_share_original_cumulative_work_copy_caps_and_cannot_resume() {
    let entries = rows(Ty::Ptr);
    let values = values(&entries);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for _ in 0..2 {
        validate_cast_operands_observed(
            7,
            CastOp::Trunc,
            &Ty::Bool,
            &Ty::U128,
            v(0),
            &values,
            MODES[0],
            &mut session,
            site(),
        )
        .unwrap();
    }
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        validate_cast_operands_observed(
            7,
            CastOp::Trunc,
            &Ty::Bool,
            &Ty::U128,
            v(0),
            &values,
            MODES[0],
            &mut session,
            site(),
        )
        .unwrap();
        let mut original_progress = None;
        for _ in 0..2 {
            assert_eq!(
                validate_cast_operands_observed(
                    7,
                    CastOp::Trunc,
                    &Ty::Bool,
                    &Ty::U128,
                    v(0),
                    &values,
                    MODES[0],
                    &mut session,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            let progress = session.first_refusal().unwrap().progress;
            if let Some(first) = original_progress {
                assert_eq!(progress, first);
            } else {
                original_progress = Some(progress);
            }
        }
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
    }
}
#[test]
fn diagnostic_preallocation_refusal_retains_all_five_strings_for_explicit_cleanup() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        op: "op".into(),
        src: "src".into(),
        dst: "dst".into(),
        actual: "actual".into(),
        reason: "reason".into(),
        errors: Vec::new(),
    };
    assert_eq!(
        state.commit(7, Diagnostic::Layout, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        (
            &*state.op,
            &*state.src,
            &*state.dst,
            &*state.actual,
            &*state.reason
        ),
        ("op", "src", "dst", "actual", "reason")
    );
    assert_eq!(state.errors.capacity(), 0);
    retire(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn pending_strings_and_completed_diagnostics_remain_retained_at_every_later_stop() {
    let values = values(&rows(Ty::Ptr));
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    check_fixture(&mut state, &values, &mut work).unwrap();
    retire(&mut state, &mut work);
    let (mut pending, mut completed) = (false, false);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        if check_fixture(&mut state, &values, &mut work).is_err() {
            pending |= state.op.capacity()
                + state.src.capacity()
                + state.actual.capacity()
                + state.reason.capacity()
                > 0;
            completed |= !state.errors.is_empty();
        }
        retire(&mut state, &mut work);
        assert!(empty(&state));
    }
    assert!(pending && completed);
}
#[test]
fn final_publication_refusal_drains_completed_output_with_generic_nested_retirement() {
    let entries = rows(Ty::Ptr);
    let values = values(&entries);
    let (_, baseline) = run(
        CastOp::Trunc,
        &Ty::Bool,
        &Ty::U128,
        &entries,
        v(0),
        MODES[0],
    );
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_cast_operands_observed(
            7,
            CastOp::Trunc,
            &Ty::Bool,
            &Ty::U128,
            v(0),
            &values,
            MODES[0],
            &mut session,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > stop + 20);
    assert!(
        observer.events[stop..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn original_cleanup_refusal_finishes_private_strings_and_all_completed_errors() {
    let values = values(&rows(Ty::Ptr));
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        cleanup_stop: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    check_fixture(&mut state, &values, &mut work).unwrap();
    assert_eq!(state.errors.len(), 2);
    arm.set(true);
    state.retire_scratch(&mut work);
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    retire(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original cast cleanup"
    );
}
#[test]
fn found_handle_still_requires_full_remaining_inline_scan_under_original_budget() {
    let src = Ty::Tuple(vec![handle(), Ty::Tuple(vec![Ty::U32; 5000])]);
    let values = values(&[]);
    let mut observer = Observer {
        work_cap: Some(500),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_cast_operands_observed(
            7,
            CastOp::FPToSI,
            &src,
            &Ty::I32,
            v(99),
            &values,
            MODES[0],
            &mut session,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert!(observer.events.len() < 500);
}
#[test]
fn actual_bool_and_width_inner_descent_refuse_interiorly_without_semantic_none() {
    for boolean in [false, true] {
        let src = vector(if boolean { Ty::Bool } else { Ty::U32 }, 3000, 2);
        let values = values(&[]);
        let mut observer = Observer {
            work_cap: Some(100),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        let result = if boolean {
            state.compatibility(7, CastOp::Bitcast, &src, &Ty::U32, MODES[0], &mut work)
        } else {
            state.operand_and_width(7, CastOp::Trunc, &src, &Ty::U8, v(99), &values, &mut work)
        };
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        retire(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(work.session.first_refusal().unwrap().cause, "work");
        assert_eq!(
            src.retire_observed(work.session, work.site),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn bounded_unicode_pending_text_stops_after_prefix_and_retains_it_until_retirement() {
    let source = "λ".repeat(10_000);
    let mut observer = Observer {
        work_cap: Some(5000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        work.text(&source, &mut state.reason),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(!state.reason.is_empty() && state.reason.len() < source.len());
    assert!(source.starts_with(&state.reason));
    retire(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn retained_allocated_empty_spelling_is_not_overwritten_before_cleanup() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        actual: String::with_capacity(8),
        ..State::default()
    };
    assert_eq!(
        state.ready(&mut work),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(
        work.spelling(&Ty::U8, &mut state.actual),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(state.actual.capacity() >= 8);
    retire(&mut state, &mut work);
    assert!(empty(&state));
}
