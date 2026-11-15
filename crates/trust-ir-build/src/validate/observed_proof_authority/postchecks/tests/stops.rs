// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_callback_for_graph_cycle_island_names_and_content_refuses_with_exact_prefix() {
    let mut i = cycle_fixture();
    i.islands = fixture().islands;
    i.rows = fixture().rows;
    let (base, end) = run(&i);
    let catalog = ModuleFunctionCatalog::new(&i.module);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            call(&i, &catalog, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "postcheck stop");
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
fn exact_single_call_work_and_copy_cap_pass_then_a_second_call_spends_same_original_owner() {
    let i = fixture();
    let (base, end) = run(&i);
    let catalog = ModuleFunctionCatalog::new(&i.module);
    for copy in [false, true] {
        let cap = base.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer {
            work_cap: (!copy).then_some(cap),
            byte_cap: copy.then_some(cap),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = call(&i, &catalog, &mut s).unwrap();
        assert_eq!(
            call(&i, &catalog, &mut s),
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
fn prior_original_work_and_copy_debits_reduce_actual_postcheck_capacity() {
    let i = fixture();
    let (base, end) = run(&i);
    let catalog = ModuleFunctionCatalog::new(&i.module);
    for copy in [false, true] {
        let cap = base.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer {
            work_cap: (!copy).then_some(cap),
            byte_cap: copy.then_some(cap),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: usize::from(!copy),
            copy_bytes: usize::from(copy),
        })
        .unwrap();
        assert_eq!(
            call(&i, &catalog, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn zero_fuel_is_preserved_and_foreign_catalog_never_substitutes_for_actual_source() {
    let i = fixture();
    let foreign = i.module.clone();
    let catalog = ModuleFunctionCatalog::new(&foreign);
    let mut o = Observer::default();
    let mut opts = InterpretOptions::default();
    opts.fuel = 0;
    let mut s = ObservedSession::new(opts, &mut o);
    assert_eq!(
        call(&i, &catalog, &mut s),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(s.remaining_fuel(), 0);
    let catalog = ModuleFunctionCatalog::new(&i.module);
    let out = call(&i, &catalog, &mut s).unwrap();
    assert_eq!(out, oracle(&i, &catalog));
    assert_eq!(s.remaining_fuel(), 0);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
}
#[test]
fn preexisting_first_refusal_suppresses_all_later_postchecks_and_normal_publication() {
    let i = fixture();
    let catalog = ModuleFunctionCatalog::new(&i.module);
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
        call(&i, &catalog, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "postcheck stop");
    drop(s);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn exact_full_result_publication_refusal_retires_all_prior_diagnostics_and_content() {
    let i = fixture();
    let (base, end) = run(&i);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let catalog = ModuleFunctionCatalog::new(&i.module);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        call(&i, &catalog, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert!(!o.events[end..].is_empty());
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
