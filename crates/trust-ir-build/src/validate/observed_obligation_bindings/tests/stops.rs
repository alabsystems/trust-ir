// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_public_callback_including_ssa_map_construction_refuses_without_partial_output() {
    let mut world = fixture();
    set(&mut world, ClausePlace::World, ClauseSort::Bool);
    let mut ssa = fixture();
    set(&mut ssa, ClausePlace::Value(v(5)), ClauseSort::Int);
    for m in [Module::new(""), world, fixture(), ssa] {
        let (_, base, bound) = run(&m);
        for stop in 1..=bound {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_module_obligation_bindings_observed(&m, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original obligation-binding stop"
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert!(
                o.events[stop..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn original_cumulative_work_and_copy_include_map_and_caller_retirement_before_second_call() {
    let mut m = fixture();
    set(&mut m, ClausePlace::Value(v(5)), ClauseSort::Int);
    let (_, base, _) = run(&m);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_module_obligation_bindings_observed(&m, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert!(s.first_refusal().is_none());
        assert_eq!(
            validate_module_obligation_bindings_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_obligation_bindings_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn exact_original_instruction_coordinates_and_zero_fuel_survive_every_actual_child_and_cleanup() {
    let mut m = fixture();
    set(&mut m, ClausePlace::Value(v(5)), ClauseSort::Int);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let out = validate_module_obligation_bindings_observed(&m, &mut s, site()).unwrap();
    assert_eq!(out, ordinary(&m));
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn final_outer_publication_refuses_after_complete_map_retirement_and_holds_all_prior_errors() {
    let mut m = fixture();
    set(&mut m, ClausePlace::Value(v(5)), ClauseSort::Int);
    for m in [Module::new(""), m] {
        let (_, base, bound) = run(&m);
        let mut o = Observer {
            stop: Some(bound),
            cleanup_after: Some(bound),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_obligation_bindings_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original obligation-binding stop"
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
fn actual_long_blank_and_duplicate_name_work_can_refuse_before_publishing_a_name_answer() {
    for duplicate in [false, true] {
        let mut m = fixture();
        let text = if duplicate {
            "λ".repeat(3000)
        } else {
            "\u{2003}".repeat(2000)
        };
        m.proof_obligations[0].formula = Some(formula(vec![(
            text.as_str(),
            ClausePlace::World,
            ClauseSort::Bool,
        )]));
        if duplicate {
            let b = m.proof_obligations[0].formula.as_ref().unwrap().bindings[0].clone();
            m.proof_obligations[0]
                .formula
                .as_mut()
                .unwrap()
                .bindings
                .push(b);
        }
        let (_, base, bound) = run(&m);
        let stop = base.events[..bound]
            .iter()
            .enumerate()
            .filter(|(_, e)| {
                e.phase == ExecutionPhase::Validation
                    && if duplicate {
                        e.work == 1024 && e.copy_bytes == 0
                    } else {
                        e.work == 8 * u32::BITS as usize && e.copy_bytes == size_of::<bool>()
                    }
            })
            .nth(if duplicate { 1 } else { 100 })
            .unwrap()
            .0
            + 1;
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_obligation_bindings_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original obligation-binding stop"
        );
    }
}
#[test]
fn actual_definition_census_cannot_publish_an_earlier_match_when_its_remaining_source_walk_stops() {
    let mut m = fixture();
    for id in 100..400 {
        m.functions[0].blocks[0]
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }).with_results([v(id)]));
    }
    let function = &m.functions[0];
    let mut base = Observer::default();
    let bound;
    {
        let calls = base.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert!(scan::defined(function, v(4), &mut w).unwrap());
        bound = calls.get();
    }
    let stop = base.events[..bound]
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == 2 * size_of::<u32>()
        })
        .nth(200)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        scan::defined(function, v(4), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn initial_copy_and_preexisting_sticky_refusal_never_enter_scope_or_type_map_work() {
    let m = fixture();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_obligation_bindings_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        validate_module_obligation_bindings_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    drop(s);
    assert_eq!(o.events.len(), 1);
}
