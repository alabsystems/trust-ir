// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module) {
    let (_, baseline, begin, end) = run(m);
    let layouts = m.layout_table();
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(m, &mut s);
        assert_eq!(
            validate_exhaustive_switch_cases_observed(
                &layouts,
                &m.functions[0],
                &values,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original enum-coverage stop"
        );
        let _ = values.retire_observed(&mut s, site());
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
fn every_definition_provenance_assignment_mask_membership_inhabitance_and_publication_callback_refuses()
 {
    every(&fixture());
    every(&signed());
}
#[test]
fn every_full_literal_and_late_unicode_missing_variant_diagnostic_callback_refuses() {
    let mut m = fixture();
    m.enums[0].variants[1].name = "é🦀".repeat(200);
    m.functions[0].blocks[0].body[1] = switch(
        1,
        vec![Constant::Record(vec![("tag".into(), Constant::Int(9))])],
    );
    every(&m);
}
#[test]
fn repeated_complete_checks_share_original_cumulative_work_and_copy_caps() {
    let m = fixture();
    let (_, baseline, _, end) = run(&m);
    let layouts = m.layout_table();
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
        let values = setup(&m, &mut s);
        let out = validate_exhaustive_switch_cases_observed(
            &layouts,
            &m.functions[0],
            &values,
            &mut s,
            site(),
        )
        .unwrap();
        assert_eq!(
            validate_exhaustive_switch_cases_observed(
                &layouts,
                &m.functions[0],
                &values,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
        let _ = values.retire_observed(&mut s, site());
    }
}
#[test]
fn original_zero_fuel_and_existing_refusal_never_become_unknown_origin_success() {
    let m = fixture();
    let layouts = m.layout_table();
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let values = setup(&m, &mut s);
    let out = validate_exhaustive_switch_cases_observed(
        &layouts,
        &m.functions[0],
        &values,
        &mut s,
        site(),
    )
    .unwrap();
    assert_eq!(out, original(&m));
    assert_eq!(s.remaining_fuel(), 0);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        interrupt: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(&m, &mut s);
    arm.set(true);
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
        validate_exhaustive_switch_cases_observed(
            &layouts,
            &m.functions[0],
            &values,
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    let _ = values.retire_observed(&mut s, site());
}
