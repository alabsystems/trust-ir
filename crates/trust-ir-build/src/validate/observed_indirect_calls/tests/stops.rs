// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_constructor_and_query_callback_refuses_and_retires_context() {
    for m in [fixture(), closure()] {
        let (_, baseline, begin, end) = run(&m);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (catalog, values, nominal) = setup(&m, &mut s);
            match ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()) {
                Err(e) => assert_eq!(e, ObservedValueError::AdmissionRefused),
                Ok(mut c) => {
                    assert_eq!(
                        c.validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site()),
                        Err(ObservedValueError::AdmissionRefused)
                    );
                    assert!(c.closures.is_none() && c.pointers.is_none());
                    assert_eq!(
                        c.retire_observed(&mut s, site()),
                        Err(ObservedValueError::AdmissionRefused)
                    );
                }
            }
            assert_eq!(s.first_refusal().unwrap().cause, "original indirect stop");
            dispose(catalog, values, nominal, &mut s);
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
fn long_name_type_and_prior_diagnostics_every_callback_keeps_first_cause() {
    let mut m = fixture();
    m.functions[0].name = "é🦀caller".repeat(300);
    m.functions[1].name = "中target".repeat(300);
    m.functions[1].calling_conv = CallingConv::Fast;
    m.functions[1].ty = FuncTyId::new(2);
    m.functions[0].blocks[0].body[1].inst = call(10, 1, &[1, 0]);
    let (e, baseline, begin, end) = run(&m);
    assert_eq!(e.len(), 4);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values, nominal) = setup(&m, &mut s);
        if let Ok(mut c) = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()) {
            assert_eq!(
                c.validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert!(c.closures.is_none() && c.pointers.is_none());
        }
        assert_eq!(s.first_refusal().unwrap().cause, "original indirect stop");
        dispose(catalog, values, nominal, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
}
#[test]
fn repeated_cached_edges_share_original_cumulative_work_and_copy() {
    let m = fixture();
    let (_, baseline, _, end) = run(&m);
    for copy in [false, true] {
        let total = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(total)
        } else {
            o.work_cap = Some(total)
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values, nominal) = setup(&m, &mut s);
        let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
        let out = c
            .validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site())
            .unwrap();
        assert!(out.is_empty());
        assert_eq!(
            c.validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(c.closures.is_none() && c.pointers.is_none());
        dispose(catalog, values, nominal, &mut s);
    }
}
#[test]
fn zero_instruction_fuel_and_original_site_survive_actual_pointer_resolution() {
    let m = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
    let out = c
        .validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site())
        .unwrap();
    assert!(out.is_empty());
    assert_eq!(s.remaining_fuel(), 0);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    c.retire_observed(&mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
}
#[test]
fn invalid_physical_coordinates_are_operational_and_drain_all_actual_caches() {
    let m = fixture();
    for (function, block, index) in [(usize::MAX, 0, 0), (0, usize::MAX, 0), (0, 0, usize::MAX)] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values, nominal) = setup(&m, &mut s);
        match ObservedIndirectCalls::new_observed(&catalog, function, &mut s, site()) {
            Err(e) => {
                assert_eq!(function, usize::MAX);
                assert_eq!(e, ObservedValueError::InvalidRange)
            }
            Ok(mut c) => {
                assert_eq!(
                    c.validate_at_observed(block, index, &values, Some(&nominal), &mut s, site()),
                    Err(ObservedValueError::InvalidRange)
                );
                assert!(c.closures.is_none() && c.pointers.is_none());
            }
        }
        dispose(catalog, values, nominal, &mut s);
    }
}
#[test]
fn preexisting_refusal_at_first_query_header_still_consumes_all_context_children() {
    let m = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    // Obtain the exact constructor endpoint, not a guessed equal-size event.
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
    let end = calls.get();
    c.retire_observed(&mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
    drop(s);
    let mut o = Observer {
        stop: Some(end + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
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
        c.validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(c.closures.is_none() && c.pointers.is_none());
    dispose(catalog, values, nominal, &mut s);
}
