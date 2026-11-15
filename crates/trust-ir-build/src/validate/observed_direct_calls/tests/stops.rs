// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_real_catalog_varargs_merge_diagnostic_and_publication_callback_refuses() {
    let mut m = fixture();
    m.func_types[1].is_vararg = true;
    let inst = call(&[0, 1, 2, 3]);
    let (_, baseline, begin, end) = run(&m, &inst, true);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values, nominal) = setup(&m, true, &mut s);
        assert_eq!(
            validate_direct_call_observed(
                &catalog,
                &m.functions[0],
                &inst,
                &values,
                nominal.as_ref(),
                BlockId::new(1),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original direct call stop"
        );
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
#[test]
fn repeated_direct_calls_share_original_cumulative_work_and_copy_not_fresh_grants() {
    let m = fixture();
    let inst = call(&[0, 1, 1]);
    let (_, baseline, _, end) = run(&m, &inst, true);
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
        let (catalog, values, nominal) = setup(&m, true, &mut s);
        let first = validate_direct_call_observed(
            &catalog,
            &m.functions[0],
            &inst,
            &values,
            nominal.as_ref(),
            BlockId::new(1),
            &mut s,
            site(),
        )
        .unwrap();
        assert_eq!(
            validate_direct_call_observed(
                &catalog,
                &m.functions[0],
                &inst,
                &values,
                nominal.as_ref(),
                BlockId::new(1),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_validation_errors_observed(first, &mut s, site());
        dispose(catalog, values, nominal, &mut s);
    }
}
#[test]
fn zero_fuel_original_query_site_and_preexisting_first_refusal_are_not_renewed() {
    let m = fixture();
    let inst = call(&[1, 0]);
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let (catalog, values, nominal) = setup(&m, true, &mut s);
    let out = validate_direct_call_observed(
        &catalog,
        &m.functions[0],
        &inst,
        &values,
        nominal.as_ref(),
        BlockId::new(1),
        &mut s,
        site(),
    )
    .unwrap();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    let (_, _, begin, _) = run(&m, &inst, true);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, true, &mut s);
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
        validate_direct_call_observed(
            &catalog,
            &m.functions[0],
            &inst,
            &values,
            nominal.as_ref(),
            BlockId::new(1),
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original direct call stop"
    );
    dispose(catalog, values, nominal, &mut s);
}
#[test]
fn operational_callee_lookup_stop_is_not_callee_absence_or_shorter_diagnostics() {
    let m = fixture();
    let inst = call(&[0, 1, 1]);
    let (_, _, begin, _) = run(&m, &inst, true);
    let cut = begin + 3;
    let mut o = Observer {
        stop: Some(cut),
        cleanup_after: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, true, &mut s);
    assert_eq!(
        validate_direct_call_observed(
            &catalog,
            &m.functions[0],
            &inst,
            &values,
            nominal.as_ref(),
            BlockId::new(1),
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original direct call stop"
    );
    dispose(catalog, values, nominal, &mut s);
    drop(s);
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
