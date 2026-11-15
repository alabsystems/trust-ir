// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_lookup_identity_drop_equality_error_and_publication_callback_refuses() {
    let m = fixture();
    let a = input(&m);
    for g in [Group::Contexts, Group::References, Group::Discharged] {
        let (base, end) = run(&a, g);
        for cut in 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                call(&a, g, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "consumer stop");
            drop(s);
            assert_eq!(&o.events[..cut], &base.events[..cut]);
            assert!(
                o.events[cut..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn repeated_actual_consumers_share_original_cumulative_work_and_copy() {
    let m = fixture();
    let a = input(&m);
    for g in [Group::Contexts, Group::References, Group::Discharged] {
        let (base, end) = run(&a, g);
        for copy in [false, true] {
            let cap = base.events[..end]
                .iter()
                .map(|e| if copy { e.copy_bytes } else { e.work })
                .sum();
            let mut o = Observer {
                work_cap: (!copy).then_some(cap),
                byte_cap: copy.then_some(cap),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let out = call(&a, g, &mut s).unwrap();
            assert_eq!(
                call(&a, g, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                if copy { "copy" } else { "work" }
            );
            let _ = retire_validation_errors_observed(out, &mut s, site());
        }
    }
}
#[test]
fn source_identity_zero_fuel_and_sticky_original_first_cause_never_become_authority() {
    let m = fixture();
    let a = input(&m);
    let foreign = m.clone();
    let mut o = Observer::default();
    let mut opts = InterpretOptions::default();
    opts.fuel = 0;
    let mut s = ObservedSession::new(opts, &mut o);
    assert_eq!(
        a.contexts(&foreign, &mut s, site()),
        Err(ObservedValueError::InvalidRange)
    );
    let out = call(&a, Group::Contexts, &mut s).unwrap();
    assert_eq!(out, oracle(&a, Group::Contexts));
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
    assert_eq!(
        call(&a, Group::Contexts, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "consumer stop");
}
