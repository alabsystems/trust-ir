// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module) {
    let (_, baseline, begin, end) = run(m, 0, None);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (layouts, catalog, census, nominal) = setup(m, &mut s);
        assert_eq!(
            validate_cross_function_observed(
                &layouts,
                &catalog,
                0,
                census,
                nominal.as_ref(),
                None,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original cross-function stop"
        );
        dispose(layouts, catalog, nominal, &mut s);
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
fn every_original_map_context_rule_aggregation_cleanup_and_publication_callback_refuses() {
    every(&fixture());
}
#[test]
fn every_interior_complete_mismatch_and_late_batch_callback_refuses_without_shorter_success() {
    let mut m = fixture();
    replace(
        &mut m,
        vec![Inst::Call {
            callee: FuncId::new(9),
            args: vec![v(0), v(2)],
        }],
    );
    every(&m);
}
#[test]
fn same_complete_pass_repetitions_share_original_cumulative_work_and_copy_caps() {
    let m = fixture();
    let (_, baseline, _, end) = run(&m, 0, None);
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
        let (layouts, catalog, census, nominal) = setup(&m, &mut s);
        let out = validate_cross_function_observed(
            &layouts,
            &catalog,
            0,
            census,
            nominal.as_ref(),
            None,
            &mut s,
            site(),
        )
        .unwrap();
        assert_eq!(
            validate_cross_function_observed(
                &layouts,
                &catalog,
                0,
                census,
                nominal.as_ref(),
                None,
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
        dispose(layouts, catalog, nominal, &mut s);
    }
}
#[test]
fn original_zero_fuel_is_preserved_and_preexisting_sticky_refusal_is_never_absence() {
    let m = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        interrupt: Some(arm.clone()),
        ..Observer::default()
    };
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let (layouts, catalog, census, nominal) = setup(&m, &mut s);
    let out = validate_cross_function_observed(
        &layouts,
        &catalog,
        0,
        census,
        nominal.as_ref(),
        None,
        &mut s,
        site(),
    )
    .unwrap();
    assert_eq!(out, original::run(&m, 0, None));
    assert_eq!(s.remaining_fuel(), 0);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
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
        validate_cross_function_observed(
            &layouts,
            &catalog,
            0,
            census,
            nominal.as_ref(),
            None,
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    dispose(layouts, catalog, nominal, &mut s);
}
#[test]
fn final_whole_output_publication_refusal_keeps_all_cleanup_in_original_owner() {
    let m = broad();
    let (_, _, _, end) = run(&m, 0, None);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (layouts, catalog, census, nominal) = setup(&m, &mut s);
    assert_eq!(
        validate_cross_function_observed(
            &layouts,
            &catalog,
            0,
            census,
            nominal.as_ref(),
            None,
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original cross-function stop"
    );
    dispose(layouts, catalog, nominal, &mut s);
}
