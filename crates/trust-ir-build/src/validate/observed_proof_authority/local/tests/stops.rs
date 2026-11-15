// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_callback_in_accepted_coverage_site_and_formula_paths_preserves_prefix_and_first_cause()
 {
    let mut cases = vec![fixture(), coverage_fixture()];
    let mut m = fixture();
    m.proof_obligations[1].site = Some(ObligationSite::new(FuncId::new(7), BlockId::new(2), 3));
    cases.push(m);
    let mut m = fixture();
    m.proof_obligations[1].formula.as_mut().unwrap().bindings[0]
        .1
        .place = ClausePlace::Unwind;
    cases.push(m);
    for m in cases {
        let a = input(&m);
        let (base, end) = run(&a, 1);
        for cut in 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert!(matches!(
                call(&a, 1, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            ));
            assert_eq!(s.first_refusal().unwrap().cause, "local stop");
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
fn repeated_actual_calls_spend_original_cumulative_work_and_copy_without_refilling() {
    let m = coverage_fixture();
    let a = input(&m);
    let (base, end) = run(&a, 1);
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
        let out = call(&a, 1, &mut s).unwrap();
        assert!(matches!(
            call(&a, 1, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        let _ = out.retire_observed(&mut s, site());
    }
}
#[test]
fn prior_partial_original_debit_is_included_in_the_exact_success_bill() {
    let m = coverage_fixture();
    let a = input(&m);
    let (base, end) = run(&a, 1);
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
        assert!(matches!(
            call(&a, 1, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        ));
    }
}
#[test]
fn zero_fuel_source_binding_and_preexisting_sticky_cause_do_not_become_semantic_admission() {
    let m = fixture();
    let a = input(&m);
    let foreign = m.clone();
    let mut o = Observer::default();
    let mut opts = InterpretOptions::default();
    opts.fuel = 0;
    let mut s = ObservedSession::new(opts, &mut o);
    assert!(matches!(
        a.local_inheritance(&foreign, &m.proof_certificates[1], &mut s, site()),
        Err(ObservedValueError::InvalidRange)
    ));
    let out = call(&a, 1, &mut s).unwrap();
    assert_eq!(normalized(&out), (1, None));
    assert_eq!(s.remaining_fuel(), 0);
    out.retire_observed(&mut s, site()).unwrap();
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
    assert!(matches!(
        call(&a, 1, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(s.first_refusal().unwrap().cause, "local stop");
}
