// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_callback_in_all_policies_preserves_exact_prefix_and_sticky_refusal() {
    let m = refused_local();
    let a = input(&m);
    let auth = AuthenticatedImports::default();
    for policy in [
        ImportPolicy::Structural,
        ImportPolicy::Refuse,
        ImportPolicy::Authenticated(&auth),
    ] {
        let (base, end) = run(&a, policy);
        for cut in 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                call(&a, policy, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "inherit stop");
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
fn cumulative_full_consumer_bills_reuse_the_same_original_work_and_copy_owner() {
    let m = fixture();
    let a = input(&m);
    let auth = authenticated(&m, Some(SiteOutcome::Refused("reason".into())));
    for policy in [ImportPolicy::Refuse, ImportPolicy::Authenticated(&auth)] {
        let (base, end) = run(&a, policy);
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
            let out = call(&a, policy, &mut s).unwrap();
            assert_eq!(
                call(&a, policy, &mut s),
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
fn prior_partial_work_and_copy_debits_are_never_erased_by_nested_consumers() {
    let m = fixture();
    let a = input(&m);
    let (base, end) = run(&a, ImportPolicy::Refuse);
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
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: usize::from(!copy),
            copy_bytes: usize::from(copy),
        })
        .unwrap();
        assert_eq!(
            call(&a, ImportPolicy::Refuse, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn zero_fuel_foreign_source_and_sticky_first_cause_keep_exact_original_session() {
    let m = fixture();
    let a = input(&m);
    let foreign = m.clone();
    let mut o = Observer::default();
    let mut opts = InterpretOptions::default();
    opts.fuel = 0;
    let mut s = ObservedSession::new(opts, &mut o);
    assert_eq!(
        a.inherited_errors(&foreign, ImportPolicy::Refuse, &mut s, site()),
        Err(ObservedValueError::InvalidRange)
    );
    let out = call(&a, ImportPolicy::Refuse, &mut s).unwrap();
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
        call(&a, ImportPolicy::Refuse, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "inherit stop");
}
