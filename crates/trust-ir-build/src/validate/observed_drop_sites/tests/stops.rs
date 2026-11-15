// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_public_callback_refuses_without_partial_diagnostics() {
    for m in [Module::new("empty"), mixed()] {
        let (_, base, bound) = run(&m);
        for stop in 1..=bound {
            let mut o = Observer {
                stop: Some(stop),
                cleanup_after: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_module_drop_sites_observed(&m, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert_eq!(s.first_refusal().unwrap().cause, "original drop-site stop");
            drop(s);
            assert_eq!(&o.events[..stop], &base.events[..stop]);
            assert!(
                o.events[stop..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_original_work_and_copy_caps_cover_children_output_and_caller_disposal() {
    let m = mixed();
    let (_, base, _) = run(&m);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_module_drop_sites_observed(&m, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_drop_sites_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_drop_sites_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn exact_instruction_site_and_zero_fuel_survive_all_children_and_retirement() {
    let m = mixed();
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(1),
        block: BlockId::new(2),
        instruction_index: usize::MAX,
    });
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let out = validate_module_drop_sites_observed(&m, &mut s, exact).unwrap();
    assert_eq!(out, super::super::super::validate_drop_sites(&m));
    retire_validation_errors_observed(out, &mut s, exact).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == exact));
}
#[test]
fn actual_final_outer_publication_can_refuse_empty_and_nonempty_results() {
    for m in [Module::new("empty"), mixed()] {
        let (_, base, bound) = run(&m);
        let mut o = Observer {
            stop: Some(bound),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_drop_sites_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[bound - 1]);
        assert_eq!(
            s.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
    }
}
#[test]
fn first_header_refusal_precedes_owned_state_and_index_construction() {
    let m = mixed();
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_drop_sites_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(o.events.len(), 1);
    assert_eq!(
        (o.events[0].phase, o.events[0].work, o.events[0].copy_bytes),
        (
            ExecutionPhase::Validation,
            1,
            size_of::<State>()
                + size_of::<Work<'_, '_, Observer>>()
                + size_of::<ObservedDropGlueIndex<'_>>()
        )
    );
}
