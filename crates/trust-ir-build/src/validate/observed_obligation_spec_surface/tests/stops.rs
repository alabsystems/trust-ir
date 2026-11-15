// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_empty_valid_and_three_error_callback_preserves_first_cause_and_no_partial_output() {
    let mut valid = fixture();
    valid.proof_obligations[0].formula = None;
    let mut unresolved = fixture();
    unresolved.proof_obligations[0].kind = ObligationKind::MemorySafety;
    for m in [Module::new(""), valid, fixture(), unresolved] {
        let (_, base, bound) = run(&m);
        for stop in 1..=bound {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_module_obligation_spec_surface_observed(&m, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original spec-surface stop"
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert!(
                o.events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn original_cumulative_work_and_copy_include_successful_caller_disposal_without_reset() {
    let m = fixture();
    let (_, base, _) = run(&m);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_module_obligation_spec_surface_observed(&m, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert!(s.first_refusal().is_none());
        assert_eq!(
            validate_module_obligation_spec_surface_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_obligation_spec_surface_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn original_instruction_site_and_zero_fuel_hold_across_children_publication_and_cleanup() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let out = validate_module_obligation_spec_surface_observed(&m, &mut s, site()).unwrap();
    assert_eq!(out, ordinary(&m));
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn outer_final_publication_refuses_both_empty_and_complete_nonempty_vectors() {
    for m in [Module::new(""), fixture()] {
        let (_, base, bound) = run(&m);
        let mut o = Observer {
            stop: Some(bound),
            cleanup_after: Some(bound),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_obligation_spec_surface_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[bound - 1]);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original spec-surface stop"
        );
        assert!(
            o.events[bound..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn long_named_machine_resolution_can_stop_inside_the_actual_second_comparison_chunk() {
    let name = "λ".repeat(3000);
    let mut m = fixture();
    m.spec_modules[0].name = name.clone();
    m.proof_obligations[0].spec = Some(SpecObligationRef::new(name, "T"));
    m.proof_obligations[0].formula = None;
    let (_, base, bound) = run(&m);
    let stop = base.events[..bound]
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 0
        })
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_obligation_spec_surface_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
    assert!(
        !o.events[..stop]
            .iter()
            .any(|e| e.phase == ExecutionPhase::Publication)
    );
}
#[test]
fn actual_effective_sort_legacy_interior_refusal_is_not_an_unknown_or_matching_binding() {
    let mut m = fixture();
    m.spec_modules[0].vars[0] = SpecVar::new("x", "1".repeat(2000) + ".." + &"2".repeat(2000));
    m.proof_obligations[0].formula = Some(formula(vec![(
        "x",
        ClausePlace::SpecVar { index: 0 },
        ClauseSort::Bool,
    )]));
    let (_, base, bound) = run(&m);
    let stop = base.events[..bound]
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<Option<&u8>>()
        })
        .nth(100)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_obligation_spec_surface_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original spec-surface stop"
    );
}
#[test]
fn initial_copy_and_sticky_refusal_prevent_any_source_or_child_entry() {
    let m = fixture();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_obligation_spec_surface_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        validate_module_obligation_spec_surface_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    drop(s);
    assert_eq!(o.events.len(), 1);
}
