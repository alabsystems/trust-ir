// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module) {
    let (_, baseline, end) = run(m);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_closure_constants_observed(m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original closure-constant stop"
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
fn every_actual_module_tree_value_shape_string_growth_and_publication_callback_refuses() {
    every(&fixture());
    every(&rich_bad());
}
#[test]
fn actual_deep_borrowed_constant_continuations_have_interruptible_interior_work() {
    let mut m = fixture();
    m.closure_types[0].captures = vec![c(0), Ty::Bool];
    let mut value = closure(vec![]);
    for _ in 0..12 {
        value = closure(vec![value, Constant::Bool(true)]);
    }
    m.globals[0].initializer = Some(value);
    assert_eq!(run(&m).0.len(), 1);
    every(&m);
}
#[test]
fn repeated_whole_passes_share_both_original_cumulative_work_and_copy_caps() {
    let m = rich_bad();
    let (_, baseline, end) = run(&m);
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
        let out = validate_closure_constants_observed(&m, &mut s, site()).unwrap();
        assert_eq!(
            validate_closure_constants_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_stop_preserve_original_owner_site_and_cause() {
    let m = fixture();
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let out = validate_closure_constants_observed(&m, &mut s, site()).unwrap();
    assert!(out.is_empty());
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
        validate_closure_constants_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original closure-constant stop"
    );
}
#[test]
fn unrelated_record_names_and_byte_contents_are_not_fake_source_observation_credit() {
    let mut traces = Vec::new();
    for wide in [false, true] {
        let mut m = fixture();
        m.globals[0].ty = Ty::Unit;
        m.globals[0].initializer = Some(Constant::Record(vec![(
            if wide { "é".repeat(4000) } else { "s".into() },
            Constant::Bytes {
                data: vec![0; if wide { 100000 } else { 0 }],
                utf8: wide,
            },
        )]));
        let (e, o, end) = run(&m);
        assert!(e.is_empty());
        traces.push(o.events[..end].to_vec());
    }
    assert_eq!(traces[0], traces[1]);
}
#[test]
fn original_missing_closure_definition_and_wrong_shape_lanes_cannot_swallow_operational_stop() {
    let mut m = fixture();
    m.closure_types.clear();
    every(&m);
    let mut m = fixture();
    captures(&mut m)[1] = Constant::Vector(vec![Constant::Int(0), Constant::Int(256)]);
    every(&m);
}
