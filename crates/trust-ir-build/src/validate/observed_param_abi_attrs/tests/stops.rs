// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::filter_next,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_callback_stops_with_original_cause_without_partial_acceptance() {
    let m = fixture();
    let (_, base) = run(&m);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_param_abi_attrs_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original parameter ABI stop"
        );
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn original_work_and_copy_limits_cumulate_across_full_calls() {
    let m = fixture();
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_module_param_abi_attrs_observed(&m, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_param_abi_attrs_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_param_abi_attrs_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn complete_pending_name_survives_both_error_reserve_and_header_move_refusals() {
    let mut m = fixture();
    m.functions[0].attrs.params = vec![attrs(true, false)];
    let base = private_trace(&m);
    let cuts = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(cuts.len(), 2);
    for (n, stop) in cuts.into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.run(&m, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.name, m.functions[0].name);
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn later_output_refusal_keeps_prior_complete_diagnostics_and_pending_full_name() {
    let m = fixture();
    let base = private_trace(&m);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .next_back()
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&m, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, validate_param_abi_attrs(&m)[..5]);
    assert_eq!(state.name, m.functions[0].name);
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn actual_interior_utf8_copy_stops_before_the_remaining_name_tail_is_copied() {
    let mut m = fixture();
    m.functions[0].name = "λ".repeat(3000);
    m.functions[0].attrs.params = vec![attrs(true, false)];
    let base = private_trace(&m);
    let hits = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(hits[1], hits[0] + 1);
    let stop = hits[2];
    let mut o = Observer {
        stop: Some(stop),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&m, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.name, "λ".repeat(512));
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn sticky_cleanup_consumes_pending_name_and_all_prior_diagnostics_before_publication() {
    let m = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &mut work).unwrap();
    state.name = "pending".repeat(1000);
    arm.set(true);
    assert_eq!(
        state.finish(Ok(()), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn preexisting_stop_refuses_before_any_new_signature_or_attribute_walk() {
    let m = fixture();
    let mut o = Observer {
        stop: Some(1),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 1,
        copy_bytes: 0,
    };
    assert!(s.admit(first).is_err());
    assert_eq!(
        validate_module_param_abi_attrs_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(o.events, vec![first]);
}
#[test]
fn supplied_instruction_site_and_zero_fuel_do_not_create_a_new_owner_or_execution_budget() {
    let m = fixture();
    let exact = ExecutionSite::Instruction(trust_ir::interpret::InstructionSite {
        function: FuncId::new(3),
        block: BlockId::new(4),
        instruction_index: 5,
    });
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..Default::default()
        },
        &mut o,
    );
    assert_eq!(
        validate_module_param_abi_attrs_observed(&m, &mut s, exact).unwrap(),
        validate_param_abi_attrs(&m)
    );
    assert_eq!(s.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}
