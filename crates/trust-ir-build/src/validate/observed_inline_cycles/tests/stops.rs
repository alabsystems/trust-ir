// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_graph_tarjan_sort_description_cleanup_and_publication_callback_refuses() {
    let m = cycle();
    let (_, baseline, end) = run(&m);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(call(&m, &mut s), Err(ObservedValueError::AdmissionRefused));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original inline cycle stop"
        );
        assert_eq!(
            s.first_refusal().unwrap().progress,
            baseline.events[cut - 1]
        );
        assert_eq!(call(&m, &mut s), Err(ObservedValueError::AdmissionRefused));
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
fn second_whole_cycle_pass_cannot_renew_the_original_work_or_copy_allowance() {
    let m = cycle();
    let (_, baseline, end) = run(&m);
    for copy in [false, true] {
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer {
            work_cap: (!copy).then_some(cap),
            byte_cap: copy.then_some(cap),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = call(&m, &mut s).unwrap();
        assert_eq!(out, ordinary(&m));
        assert_eq!(call(&m, &mut s), Err(ObservedValueError::AdmissionRefused));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
    }
}
#[test]
fn actual_middle_work_and_copy_one_short_keep_the_exact_original_record_and_first_cause() {
    let m = cycle();
    let (_, baseline, end) = run(&m);
    let cut = baseline.events[..end]
        .iter()
        .enumerate()
        .filter(|(_, event)| {
            event.phase == ExecutionPhase::Validation && event.work > 0 && event.copy_bytes > 0
        })
        .min_by_key(|(i, _)| i.abs_diff(end / 2))
        .unwrap()
        .0;
    let record = baseline.events[cut];
    for copy in [false, true] {
        let total: usize = baseline.events[..=cut]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        assert!(total > 0 && if copy { record.copy_bytes } else { record.work } > 0);
        let mut o = Observer {
            work_cap: (!copy).then_some(total - 1),
            byte_cap: copy.then_some(total - 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(call(&m, &mut s), Err(ObservedValueError::AdmissionRefused));
        assert_eq!(s.first_refusal().unwrap().progress, record);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        assert_eq!(call(&m, &mut s), Err(ObservedValueError::AdmissionRefused));
        drop(s);
        assert_eq!(&o.events[..=cut], &baseline.events[..=cut]);
        assert!(
            o.events[cut + 1..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn zero_fuel_and_preexisting_original_stop_never_become_empty_success_or_new_owner() {
    let m = cycle();
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut opt = InterpretOptions::default();
    opt.fuel = 0;
    let mut s = ObservedSession::new(opt, &mut o);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 31,
        copy_bytes: 7,
    };
    assert!(s.admit(first).is_err());
    assert_eq!(call(&m, &mut s), Err(ObservedValueError::AdmissionRefused));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original inline cycle stop"
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert_eq!(o.events, vec![first]);
}
