// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_definition_registry_decimal_copy_and_publication_callback_is_refusable() {
    let m = fixture();
    let r = registry();
    let (_, baseline, bound) = run(&m, &r);
    for cut in 1..=bound {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_handle_runtime_spellings_observed(&m, &r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original runtime spelling stop"
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn actual_runtime_comparison_can_refuse_between_middle_bounded_chunks() {
    let raw: &'static str = Box::leak("RuntimeN".repeat(600).into_boxed_str());
    let r = HandleRegistry {
        pins: vec![pin(raw)],
    };
    let mut m = Module::new("");
    m.records = vec![record(0, raw)];
    let (_, baseline, _) = run(&m, &r);
    let cut = baseline
        .events
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
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_handle_runtime_spellings_observed(&m, &r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
}
#[test]
fn repeated_namespace_passes_and_caller_error_retirement_share_original_cumulative_caps() {
    let m = fixture();
    let r = registry();
    let (_, baseline, _) = run(&m, &r);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes + 1);
        } else {
            o.work_cap = Some(baseline.work + 1);
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let output = validate_handle_runtime_spellings_observed(&m, &r, &mut s, site()).unwrap();
        retire_validation_errors_observed(output, &mut s, site()).unwrap();
        assert_eq!(
            validate_handle_runtime_spellings_observed(&m, &r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn original_site_zero_fuel_preexisting_cause_and_final_vector_refusal_remain_typed() {
    let m = fixture();
    let r = registry();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let output = validate_handle_runtime_spellings_observed(&m, &r, &mut s, site()).unwrap();
    retire_validation_errors_observed(output, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        validate_handle_runtime_spellings_observed(&m, &r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original runtime spelling stop"
    );
    let (_, baseline, bound) = run(&m, &r);
    let mut o = Observer {
        stop: Some(bound),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        baseline.events[bound - 1].copy_bytes,
        size_of::<Vec<ValidationError>>()
    );
    assert_eq!(
        validate_handle_runtime_spellings_observed(&m, &r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
