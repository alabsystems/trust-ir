// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_digest_string_comparison_growth_error_and_output_callback_preserves_prefix() {
    let i = bad();
    let (base, end) = run(&i);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(call(&i, &mut s), Err(ObservedValueError::AdmissionRefused));
        assert_eq!(s.first_refusal().unwrap().cause, "binding stop");
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn exact_bill_and_prior_partial_debit_share_original_cumulative_work_and_copy() {
    let i = bad();
    let (base, end) = run(&i);
    for copy in [false, true] {
        let cap = base.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        for prior in [false, true] {
            let mut o = Observer {
                work_cap: (!copy).then_some(cap),
                byte_cap: copy.then_some(cap),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            if prior {
                s.admit(ExecutionProgress {
                    phase: ExecutionPhase::Validation,
                    site: site(),
                    work: usize::from(!copy),
                    copy_bytes: usize::from(copy),
                })
                .unwrap();
                assert_eq!(call(&i, &mut s), Err(ObservedValueError::AdmissionRefused));
            } else {
                let out = call(&i, &mut s).unwrap();
                assert_eq!(call(&i, &mut s), Err(ObservedValueError::AdmissionRefused));
                let _ = retire_validation_errors_observed(out, &mut s, site());
            }
            assert_eq!(
                s.first_refusal().unwrap().cause,
                if copy { "copy" } else { "work" }
            );
        }
    }
}
#[test]
fn zero_fuel_and_preexisting_sticky_cause_are_preserved_without_new_owner() {
    let i = bad();
    let mut o = Observer::default();
    let mut opts = InterpretOptions::default();
    opts.fuel = 0;
    let mut s = ObservedSession::new(opts, &mut o);
    let out = call(&i, &mut s).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    drop(s);
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
    assert_eq!(call(&i, &mut s), Err(ObservedValueError::AdmissionRefused));
    assert_eq!(s.first_refusal().unwrap().cause, "binding stop");
}
