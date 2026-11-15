// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_lookup_equality_attributes_format_constants_cleanup_and_publication_callback_refuses()
 {
    let mut m = bad_fixture();
    m.globals.push(global(
        "raw λ",
        Some(Constant::Aggregate(vec![
            address("clean_inc"),
            address("clean_dec"),
        ])),
    ));
    let (_, baseline, end) = run(&m);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_rc_entry_points_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original RC stop");
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
fn cumulative_original_work_and_copy_refuse_repeated_complete_diagnostics() {
    let m = bad_fixture();
    let (_, baseline, end) = run(&m);
    for copy in [false, true] {
        let limit = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum::<usize>();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(limit)
        } else {
            o.work_cap = Some(limit)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let first = validate_rc_entry_points_observed(&m, &mut s, site()).unwrap();
        assert_eq!(
            validate_rc_entry_points_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_validation_errors_observed(first, &mut s, site());
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn first_refusal_survives_all_later_cleanup_refusals_without_replacement() {
    let m = bad_fixture();
    let (_, _, end) = run(&m);
    let cut = end / 2;
    assert!(cut > 1);
    let mut o = Observer {
        stop: Some(cut),
        cleanup_after: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_rc_entry_points_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original RC stop");
    assert_eq!(
        validate_rc_entry_points_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original RC stop");
}
#[test]
fn zero_instruction_fuel_and_original_request_site_are_preserved_without_recapture() {
    let m = bad_fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let out = validate_rc_entry_points_observed(&m, &mut s, site()).unwrap();
    assert_eq!(out, super::super::super::validate_rc_entry_points(&m));
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn successful_complete_error_result_has_explicit_original_caller_retirement_and_real_terminal_receipt()
 {
    let m = bad_fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_rc_entry_points_observed(&m, &mut s, site()).unwrap();
    assert_eq!(out.len(), 2);
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    let end = calls.get();
    drop(s);
    assert!(
        o.events[begin..end - 1]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        o.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
