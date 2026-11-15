// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_empty_and_nonempty_public_callback_refuses_without_partial_output() {
    for m in [Module::new("empty"), fixture()] {
        let (_, base, end) = run(&m);
        for stop in 1..=end {
            let mut o = Observer {
                stop: Some(stop),
                cleanup_after: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_module_obligation_sites_observed(&m, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original obligation-site stop"
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
fn original_cumulative_work_and_copy_include_whole_rows_and_caller_disposal() {
    let m = fixture();
    let (_, base, _) = run(&m);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_module_obligation_sites_observed(&m, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_obligation_sites_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_obligation_sites_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn zero_fuel_and_original_instruction_site_are_preserved_through_all_lookup_and_cleanup() {
    let m = fixture();
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
    let out = validate_module_obligation_sites_observed(&m, &mut s, exact).unwrap();
    assert_eq!(out, ordinary(&m));
    retire_validation_errors_observed(out, &mut s, exact).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == exact));
}
#[test]
fn final_publication_can_refuse_both_empty_and_nonempty_diagnostics() {
    for m in [Module::new("empty"), fixture()] {
        let (_, base, end) = run(&m);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_obligation_sites_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
        assert_eq!(
            s.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
    }
}
#[test]
fn actual_long_function_resolution_can_refuse_interior_before_any_result_publication() {
    let mut m = Module::new("lookup");
    for id in 0..256 {
        m.functions.push(function(id, 0, Inst::Unreachable));
    }
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(
        matches!(w.resolve(&m,FuncId::new(255)).unwrap(),Resolution::Unique(f) if f.id.index()==255)
    );
    drop(w);
    drop(s);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 2
                && e.copy_bytes == 2 * size_of::<FuncId>() + size_of::<Option<&Function>>()
        })
        .nth(100)
        .unwrap()
        .0
        + 1;
    assert!(
        base.events[..stop]
            .iter()
            .all(|e| e.phase != ExecutionPhase::Publication)
    );
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(matches!(
        w.resolve(&m, FuncId::new(255)),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
