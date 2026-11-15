// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_public_callback_refuses_without_a_partial_prefix_or_accepting_namespace() {
    let mut valid = Module::new("");
    valid
        .proof_obligations
        .push(custom(1, "trust.vc", "ignored"));
    for m in [Module::new(""), valid, fixture()] {
        let (_, base, bound) = run(&m);
        for stop in 1..=bound {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_module_proof_obligation_header_observed(&m, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original obligation-header stop"
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            drop(s);
            assert!(
                o.events[stop..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_work_and_copy_include_caller_error_disposal_without_replenishing_a_second_call() {
    let m = fixture();
    let (_, base, _) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_module_proof_obligation_header_observed(&m, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert!(s.first_refusal().is_none());
        assert_eq!(
            validate_module_proof_obligation_header_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_proof_obligation_header_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn original_instruction_coordinates_and_zero_fuel_hold_through_all_scans_and_retirement() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let out = validate_module_proof_obligation_header_observed(&m, &mut s, site()).unwrap();
    assert_eq!(
        out,
        super::super::super::validate_proof_obligation_integrity(&m)
    );
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn outer_final_publication_refuses_empty_or_full_diagnostics_after_sticky_cleanup() {
    for m in [Module::new(""), fixture()] {
        let (_, base, bound) = run(&m);
        let mut o = Observer {
            stop: Some(bound),
            cleanup_after: Some(bound),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_proof_obligation_header_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[bound - 1]);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original obligation-header stop"
        );
        drop(s);
        assert!(
            o.events[bound..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn initial_copy_and_existing_sticky_refusal_never_enter_duplicate_or_namespace_work() {
    let m = fixture();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_proof_obligation_header_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        validate_module_proof_obligation_header_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    drop(s);
    assert_eq!(o.events.len(), 1);
}
