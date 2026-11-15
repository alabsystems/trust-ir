// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(g: Group) {
    let m = module(&[9, 1, 9, 1, 9]);
    let catalog = ModuleFunctionCatalog::new(&m);
    let (_, base, end) = run(&m, g);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            call(&m, &catalog, g, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original module IDs");
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_actual_struct_prefix_read_comparison_growth_transport_and_publication_refuses() {
    every(Group::Structs);
}
#[test]
fn every_actual_catalog_cursor_return_transport_and_copy_retirement_refuses() {
    every(Group::Functions);
}
#[test]
fn one_original_cumulative_work_and_copy_budget_covers_whole_group_and_retry() {
    let m = module(&[9, 1, 9, 1, 9]);
    let catalog = ModuleFunctionCatalog::new(&m);
    for g in [Group::Structs, Group::Functions] {
        let (_, base, end) = run(&m, g);
        for copy in [false, true] {
            let cap = base.events[..end]
                .iter()
                .map(|e| if copy { e.copy_bytes } else { e.work })
                .sum();
            let mut o = Observer {
                work_cap: (!copy).then_some(cap),
                byte_cap: copy.then_some(cap),
                ..Default::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let first = call(&m, &catalog, g, &mut s).unwrap();
            assert_eq!(
                call(&m, &catalog, g, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                if copy { "copy" } else { "work" }
            );
            let _ = retire_validation_errors_observed(first, &mut s, site());
        }
    }
}
#[test]
fn zero_instruction_fuel_and_original_interrupt_are_never_replaced() {
    let m = module(&[3, 3]);
    for g in [Group::Structs, Group::Functions] {
        let catalog = ModuleFunctionCatalog::new(&m);
        let mut o = Observer::default();
        let mut options = InterpretOptions::default();
        options.fuel = 0;
        let mut s = ObservedSession::new(options, &mut o);
        let errors = call(&m, &catalog, g, &mut s).unwrap();
        assert_eq!(s.remaining_fuel(), 0);
        retire_validation_errors_observed(errors, &mut s, site()).unwrap();
        let mut o = Observer {
            arm: Some(Rc::new(Cell::new(true))),
            ..Default::default()
        };
        let mut s = ObservedSession::new(options, &mut o);
        assert_eq!(
            call(&m, &catalog, g, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original module IDs");
    }
}
