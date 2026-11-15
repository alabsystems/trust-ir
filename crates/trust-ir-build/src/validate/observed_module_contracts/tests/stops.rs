// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

#[test]
fn every_actual_whole_loop_callback_refuses_without_partial_output() {
    for m in [Module::new("empty"), fixture()] {
        let (_, base, bound) = run(&m, ImportPolicy::Structural);
        for stop in 1..=bound {
            let mut o = Observer {
                stop: Some(stop),
                cleanup_after: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_module_function_contracts_observed(
                    &m,
                    ImportPolicy::Structural,
                    &mut s,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original module-contract stop"
            );
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
fn original_work_and_copy_caps_include_child_merges_and_caller_disposal() {
    let m = fixture();
    let (_, base, _) = run(&m, ImportPolicy::Refuse);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let errors =
            validate_module_function_contracts_observed(&m, ImportPolicy::Refuse, &mut s, site())
                .unwrap();
        retire_validation_errors_observed(errors, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_function_contracts_observed(&m, ImportPolicy::Refuse, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_function_contracts_observed(&m, ImportPolicy::Refuse, &mut s, site()),
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
fn supplied_instruction_site_and_zero_instruction_fuel_cover_the_whole_loop() {
    let m = fixture();
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(11),
        block: BlockId::new(12),
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
    let errors =
        validate_module_function_contracts_observed(&m, ImportPolicy::Structural, &mut s, exact)
            .unwrap();
    assert_eq!(errors, oracle(&m, ImportPolicy::Structural));
    retire_validation_errors_observed(errors, &mut s, exact).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == exact));
}
#[test]
fn final_outer_publication_refusal_returns_neither_empty_nor_nonempty_diagnostics() {
    for m in [Module::new("empty"), fixture()] {
        let (_, base, bound) = run(&m, ImportPolicy::Structural);
        assert_eq!(base.events[bound - 1].phase, ExecutionPhase::Publication);
        let mut o = Observer {
            stop: Some(bound),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_function_contracts_observed(
                &m,
                ImportPolicy::Structural,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[bound - 1]);
        drop(s);
        assert!(
            o.events[bound..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn first_header_refusal_happens_before_any_owned_state_or_child_construction() {
    let m = fixture();
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_function_contracts_observed(&m, ImportPolicy::Structural, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert_eq!(o.events.len(), 1);
    assert_eq!(
        (o.events[0].phase, o.events[0].work, o.events[0].copy_bytes),
        (
            ExecutionPhase::Validation,
            1,
            size_of::<State>() + size_of::<Work<'_, '_, Observer>>()
        )
    );
}
