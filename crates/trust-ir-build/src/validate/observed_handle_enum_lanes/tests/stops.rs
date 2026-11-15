// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_query_comparison_copy_retirement_and_full_publication_callback_refuses() {
    for semantic in [false, true] {
        let mut m = fixture();
        if semantic {
            m.enums[0].variants[0].fields[1] = semantic_ty();
        }
        let (_, baseline, begin, end) = run(&m);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (table, nominal) = setup(&m, &mut s);
            assert_eq!(
                validate_handle_enum_layouts_observed(&table, &nominal, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original handle-lane stop"
            );
            dispose(table, nominal, &mut s);
            drop(s);
            assert_eq!(&o.events[..cut], &baseline.events[..cut]);
            assert!(
                o.events[cut..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn repeated_complete_queries_and_diagnostics_share_original_cumulative_work_and_copy() {
    let m = fixture();
    let (_, baseline, _, end) = run(&m);
    for copy in [false, true] {
        let limit = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum::<usize>();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(limit + 1)
        } else {
            o.work_cap = Some(limit + 1)
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal) = setup(&m, &mut s);
        let out = validate_handle_enum_layouts_observed(&table, &nominal, &mut s, site()).unwrap();
        assert_eq!(
            validate_handle_enum_layouts_observed(&table, &nominal, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
        dispose(table, nominal, &mut s);
    }
}
#[test]
fn zero_execution_fuel_original_request_site_and_preexisting_stop_are_not_recaptured() {
    let m = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let (table, nominal) = setup(&m, &mut s);
    let out = validate_handle_enum_layouts_observed(&table, &nominal, &mut s, site()).unwrap();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    dispose(table, nominal, &mut s);
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let (_, _, begin, _) = run(&m);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = setup(&m, &mut s);
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
        validate_handle_enum_layouts_observed(&table, &nominal, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original handle-lane stop"
    );
    dispose(table, nominal, &mut s);
}
#[test]
fn successful_full_diagnostic_result_has_original_consuming_caller_retirement_and_zero_terminal_receipt()
 {
    let m = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = setup(&m, &mut s);
    let out = validate_handle_enum_layouts_observed(&table, &nominal, &mut s, site()).unwrap();
    assert_eq!(out.len(), 1);
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    let end = calls.get();
    dispose(table, nominal, &mut s);
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
