// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module, name: &str) {
    let (_, baseline) = run(m, name);
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(m);
    for cut in 1..=baseline.events.len() {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            exercise(m, &layouts, &functions, name, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original symbol stop");
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
fn every_actual_constructor_row_chunk_count_result_and_retirement_callback_refuses() {
    every(&fixture(), "target");
    every(&fixture(), "weak");
    let mut m = fixture();
    let name = "é🦀".repeat(450);
    m.globals[1].name = name.clone();
    m.functions[1].name = name.clone();
    every(&m, &name);
}
#[test]
fn repeated_queries_cannot_reset_either_original_cumulative_budget() {
    let m = fixture();
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    let mut baseline = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let ctx = ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
    assert!(
        ctx.target_global_observed("target", &mut s, site())
            .unwrap()
            .is_ok()
    );
    drop(s);
    for copy in [false, true] {
        let mut o = Observer::default();
        let cap = baseline
            .events
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let ctx =
            ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
        assert!(
            ctx.target_global_observed("target", &mut s, site())
                .unwrap()
                .is_ok()
        );
        assert_eq!(
            ctx.target_global_observed("target", &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        assert_eq!(
            ctx.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_refusal_keep_original_owner() {
    let m = fixture();
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    assert_eq!(
        exercise(&m, &layouts, &functions, "target", &mut s).unwrap(),
        expected(&m, &layouts, "target")
    );
    assert_eq!(s.remaining_fuel(), 0);
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
    assert!(matches!(
        ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(s.first_refusal().unwrap().cause, "original symbol stop");
    drop(s);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn late_actual_name_matches_and_absence_scan_every_source_row() {
    let mut m = fixture();
    m.globals.clear();
    m.functions.clear();
    for n in 0..17 {
        m.globals.push(global(&format!("unused{n}")));
        m.functions.push(function(n, &format!("unused{n}")));
    }
    m.globals.push(global("late"));
    every(&m, "late");
    every(&m, "absent");
    let (_, o) = run(&m, "absent");
    assert!(o.events.len() > m.globals.len() + m.functions.len());
}
