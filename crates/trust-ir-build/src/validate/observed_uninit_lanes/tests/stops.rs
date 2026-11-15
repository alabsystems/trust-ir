// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_public_callback_preserves_first_cause_and_returns_no_partial_vector() {
    let mut global_bad = Module::new("");
    global_bad.globals.push(global("g", Some(Constant::Uninit)));
    for m in [
        Module::new(""),
        fixture(
            Ty::Tuple(vec![Ty::U8]),
            Constant::Aggregate(vec![Constant::Uninit]),
        ),
        fixture(
            Ty::U8,
            Constant::Aggregate(vec![Constant::Float(1.25), Constant::Uninit]),
        ),
        global_bad,
    ] {
        let (_, base, bound) = run(&m);
        for stop in 1..=bound {
            let mut o = Observer {
                stop: Some(stop),
                cleanup: true,
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_module_uninit_lanes_observed(&m, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "uninit original stop");
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert!(
                o.events[stop..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn work_copy_and_successful_caller_retirement_cumulate_without_fuel_or_owner_reset() {
    let m = fixture(Ty::U8, Constant::Uninit);
    let (_, base, _) = run(&m);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_module_uninit_lanes_observed(&m, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert!(s.first_refusal().is_none());
        assert_eq!(
            validate_module_uninit_lanes_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_uninit_lanes_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn original_instruction_coordinates_and_zero_execution_fuel_survive_float_children_and_cleanup() {
    let m = fixture(
        Ty::U8,
        Constant::Aggregate(vec![Constant::Float(-1.25), Constant::Uninit]),
    );
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let out = validate_module_uninit_lanes_observed(&m, &mut s, site()).unwrap();
    assert_eq!(out, ordinary(&m));
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn final_publication_refuses_after_all_scratch_retirement_and_preserves_complete_error_custody() {
    for m in [Module::new(""), fixture(Ty::U8, Constant::Uninit)] {
        let (_, base, bound) = run(&m);
        let mut o = Observer {
            stop: Some(bound),
            cleanup: true,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_uninit_lanes_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[bound - 1]);
        assert!(
            o.events[bound..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn actual_borrowed_preorder_can_refuse_inside_late_siblings_before_any_boolean_publication() {
    let value = Constant::Aggregate(vec![Constant::Int(1); 300]);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert!(!state.mentions(&value, &mut w).unwrap());
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<bool>()
        })
        .nth(200)
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
        state.mentions(&value, &mut w),
        Err(ObservedValueError::AdmissionRefused)
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
fn initial_copy_and_preexisting_sticky_refusal_never_enter_constant_or_formatter_work() {
    let m = fixture(Ty::U8, Constant::Uninit);
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_uninit_lanes_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        validate_module_uninit_lanes_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    drop(s);
    assert_eq!(o.events.len(), 1);
}
