// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn all_cuts(m: &Module) {
    let (_, baseline, end) = run(m);
    assert!(end > 1);
    for cut in 1..=end {
        let mut o = Observer::default();
        o.stop.set(Some(cut));
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(
            InterpretOptions {
                fuel: 17,
                ..InterpretOptions::default()
            },
            &mut o,
        );
        assert_eq!(
            validate_module_refinements_observed(m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let progress = s.first_refusal().unwrap().progress;
        let cause = s.first_refusal().unwrap().cause;
        assert_eq!(progress, baseline.events[cut - 1]);
        assert_eq!(cause, "original refinement stop");
        assert_eq!(s.remaining_fuel(), 17);
        let after = calls.get();
        assert_eq!(
            validate_module_refinements_observed(m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(calls.get(), after);
        assert_eq!(s.first_refusal().unwrap().progress, progress);
        assert_eq!(s.first_refusal().unwrap().cause, cause);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
        );
    }
}
#[test]
fn every_callback_keeps_exact_accepted_prefix_first_cause_and_sticky_cleanup_for_real_full_calls() {
    all_cuts(&calls());
}
#[test]
fn every_callback_keeps_partial_raw_table_diagnostic_custody() {
    let mut m = module();
    m.universes.push(Universe::Members(vec![Constant::Bytes {
        data: vec![0, 255, 39],
        utf8: false,
    }]));
    all_cuts(&m);
}
#[test]
fn cumulative_work_includes_prior_real_admission_and_complete_final_publication() {
    let m = small();
    let (_, baseline, end) = run(&m);
    let bill = baseline.events[..end].iter().map(|e| e.work).sum::<usize>();
    assert!(bill > 1);
    let mut o = Observer {
        work_cap: Some(bill + 17 - 1),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 3,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    s.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 17,
        copy_bytes: 19,
    })
    .unwrap();
    assert_eq!(
        validate_module_refinements_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(s.first_refusal().unwrap().cause, "work");
    assert_eq!(first, baseline.events[end - 1]);
    assert_eq!(s.remaining_fuel(), 3);
    let n = calls.get();
    assert!(validate_module_refinements_observed(&m, &mut s, site()).is_err());
    assert_eq!(calls.get(), n);
    assert_eq!(s.first_refusal().unwrap().progress, first);
}
#[test]
fn cumulative_copy_includes_prior_real_admission_and_never_refunds_any_successful_child() {
    let m = small();
    let (_, baseline, end) = run(&m);
    let bill = baseline.events[..end]
        .iter()
        .map(|e| e.copy_bytes)
        .sum::<usize>();
    assert!(bill > 1);
    let mut o = Observer {
        copy_cap: Some(bill + 19 - 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    s.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 17,
        copy_bytes: 19,
    })
    .unwrap();
    assert_eq!(
        validate_module_refinements_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "copy");
    assert_eq!(
        s.first_refusal().unwrap().progress,
        baseline.events[end - 1]
    );
}
#[test]
fn literal_zero_work_and_copy_reject_before_state_allocation_without_restarting_owner() {
    for copy in [false, true] {
        let mut o = if copy {
            Observer {
                copy_cap: Some(0),
                ..Observer::default()
            }
        } else {
            Observer {
                work_cap: Some(0),
                ..Observer::default()
            }
        };
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut o,
        );
        assert_eq!(
            validate_module_refinements_observed(&small(), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(calls.get(), 1);
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(first.phase, ExecutionPhase::Validation);
        assert!(first.copy_bytes > 0);
        assert_eq!(s.remaining_fuel(), 0);
        assert!(validate_module_refinements_observed(&small(), &mut s, site()).is_err());
        assert_eq!(calls.get(), 1);
    }
}
#[test]
fn zero_instruction_fuel_is_preserved_by_the_complete_structural_constituent() {
    let m = small();
    let expected = ordinary(&m);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let out = validate_module_refinements_observed(&m, &mut s, site()).unwrap();
    assert_eq!(out, expected);
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn preexisting_original_refusal_prevents_all_table_and_child_activity() {
    let mut o = Observer::default();
    o.stop.set(Some(1));
    let count = o.calls.clone();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 9,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let original = ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 7,
        copy_bytes: 13,
    };
    assert!(s.admit(original).is_err());
    assert!(validate_module_refinements_observed(&calls(), &mut s, site()).is_err());
    assert_eq!(count.get(), 1);
    assert_eq!(s.first_refusal().unwrap().progress, original);
    assert_eq!(s.remaining_fuel(), 9);
}
#[test]
fn scratch_retirement_refusal_withholds_even_the_complete_healthy_diagnostic_vector() {
    let m = small();
    let (_, baseline, end) = run(&m);
    let cut = baseline.events[..end]
        .iter()
        .rposition(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    let mut o = Observer::default();
    o.stop.set(Some(cut));
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_refinements_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original refinement stop");
    assert_eq!(
        s.first_refusal().unwrap().progress,
        baseline.events[cut - 1]
    );
}
#[test]
fn every_callback_keeps_actual_named_enum_refusal_batch_and_later_implied_acceptance_owned() {
    let mut m = module();
    m.enums.push(enumeration(vec![r(2), r(1)]));
    m.functions.push(function(
        10,
        0,
        vec![(v(0), r(5)), (v(1), Ty::Enum(EnumId::new(17)))],
        vec![node(
            Inst::InsertField {
                ty: Ty::Enum(EnumId::new(17)),
                aggregate: v(1),
                field: 1,
                value: v(0),
            },
            &[],
        )],
    ));
    all_cuts(&m);
}
