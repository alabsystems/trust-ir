// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module, rule: Rule) {
    let (_, baseline, end) = run(m, rule);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            call(m, rule, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original module-tail stop"
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
fn every_actual_cast_query_error_type_display_merge_retirement_and_publication_callback_refuses() {
    every(&fixture(), Rule::Casts);
    every(&custom(), Rule::Casts);
}
#[test]
fn every_actual_function_node_fact_row_reserve_move_and_publication_callback_refuses() {
    every(&fixture(), Rule::Facts);
}
#[test]
fn repeated_whole_passes_share_original_cumulative_work_and_copy_caps() {
    let m = fixture();
    for rule in [Rule::Casts, Rule::Facts] {
        let (_, baseline, end) = run(&m, rule);
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
            let out = call(&m, rule, &mut s).unwrap();
            assert_eq!(
                call(&m, rule, &mut s),
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
fn original_zero_fuel_and_preexisting_stop_are_never_replaced_by_new_grants_or_empty_success() {
    let m = fixture();
    for rule in [Rule::Casts, Rule::Facts] {
        let mut o = Observer::default();
        let mut options = InterpretOptions::default();
        options.fuel = 0;
        let mut s = ObservedSession::new(options, &mut o);
        let out = call(&m, rule, &mut s).unwrap();
        assert_eq!(out, original(&m, rule));
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
            call(&m, rule, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original module-tail stop"
        );
    }
}
