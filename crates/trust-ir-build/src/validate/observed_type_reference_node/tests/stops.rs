// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_nominal_lexical_diagnostic_copy_and_publication_callback_remains_refusable() {
    let m = Module::new("");
    let r = registry();
    let ty = invalid();
    let (_, baseline, bound) = run(&m, &r, &ty, "raw λ\0location");
    for cut in 1..=bound {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_type_reference_node_observed(&m, &r, &ty, "raw λ\0location", &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
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
fn valid_and_dangling_direct_reference_paths_do_not_convert_stop_into_an_answer() {
    let m = targets();
    let r = registry();
    for ty in [
        Ty::Bool,
        Ty::Struct(StructId::new(0)),
        Ty::Enum(EnumId::new(99)),
    ] {
        let (_, _, bound) = run(&m, &r, &ty, "L");
        for cut in 1..=bound {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_type_reference_node_observed(&m, &r, &ty, "L", &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        }
    }
}
#[test]
fn successive_nodes_and_explicit_caller_cleanup_share_original_cumulative_caps() {
    let m = Module::new("");
    let r = registry();
    let ty = untrusted();
    let (_, baseline, _) = run(&m, &r, &ty, "L");
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes + 1)
        } else {
            o.work_cap = Some(baseline.work + 1)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (out, _) =
            validate_type_reference_node_observed(&m, &r, &ty, "L", &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert_eq!(
            validate_type_reference_node_observed(&m, &r, &ty, "L", &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn actual_long_registry_identity_comparison_can_stop_in_a_middle_chunk() {
    let name: &'static str = Box::leak("N".repeat(4096).into_boxed_str());
    let runtime: &'static str = Box::leak("R".repeat(4096).into_boxed_str());
    let r = HandleRegistry {
        pins: vec![HandleRuntimePin {
            name,
            runtime,
            calling_conv: trust_ir::CallingConv::C,
            entry_points: &[],
        }],
    };
    let ty = Ty::handle(name, runtime);
    let m = Module::new("");
    let (_, baseline, _) = run(&m, &r, &ty, "L");
    let cut = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 0
        })
        .nth(2)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_type_reference_node_observed(&m, &r, &ty, "L", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
}
#[test]
fn final_tuple_publication_must_admit_both_all_errors_and_census() {
    let m = Module::new("");
    let r = registry();
    let ty = untrusted();
    let (_, baseline, bound) = run(&m, &r, &ty, "L");
    assert_eq!(
        baseline.events[bound - 1].copy_bytes,
        size_of::<(Vec<ValidationError>, NominalCensus)>()
    );
    let mut o = Observer {
        stop: Some(bound),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_type_reference_node_observed(&m, &r, &ty, "L", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events.len() > bound);
}
#[test]
fn exact_original_site_zero_fuel_and_preexisting_first_cause_are_preserved() {
    let m = Module::new("");
    let r = registry();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let (out, census) =
        validate_type_reference_node_observed(&m, &r, &invalid(), "L", &mut s, site()).unwrap();
    assert!(census.dialect);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
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
        validate_type_reference_node_observed(&m, &r, &invalid(), "L", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original type-reference stop"
    );
}
#[test]
fn scratch_retirement_refusal_never_publishes_even_an_empty_census_result() {
    let m = Module::new("");
    let r = registry();
    let mut o = Observer {
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_type_reference_node_observed(&m, &r, &Ty::Bool, "L", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(s.first_refusal().is_some());
    drop(s);
    assert!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .count()
            >= 8
    );
}
