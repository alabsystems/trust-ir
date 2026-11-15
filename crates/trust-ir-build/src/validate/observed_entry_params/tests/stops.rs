// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_entry_lookup_equality_display_and_publication_callback_refuses() {
    let (m, f) = mismatch();
    let (_, baseline, end) = run(&m, &f);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_entry_params_observed(&m, &f, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original entry parameter stop"
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
fn repeated_comparison_and_display_share_original_cumulative_work_and_copy() {
    let (m, f) = mismatch();
    let (_, baseline, end) = run(&m, &f);
    for copy in [false, true] {
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let first = validate_entry_params_observed(&m, &f, &mut s, site()).unwrap();
        assert_eq!(
            validate_entry_params_observed(&m, &f, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_validation_errors_observed(first, &mut s, site());
    }
}
#[test]
fn zero_fuel_and_first_cause_stick_to_the_original_request_site() {
    let (m, f) = mismatch();
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let out = validate_entry_params_observed(&m, &f, &mut s, site()).unwrap();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
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
        validate_entry_params_observed(&m, &f, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original entry parameter stop"
    );
}
#[test]
fn late_display_refusal_and_cleanup_refusals_never_publish_shorter_lists() {
    let (m, f) = mismatch();
    let (_, _, end) = run(&m, &f);
    let cut = end - 2;
    let mut o = Observer {
        stop: Some(cut),
        cleanup_after: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_entry_params_observed(&m, &f, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original entry parameter stop"
    );
    drop(s);
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
