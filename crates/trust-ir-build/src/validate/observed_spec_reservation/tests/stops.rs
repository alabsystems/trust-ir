// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::filter_next,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_callback_in_both_stages_refuses_without_shorter_success_or_changed_first_cause() {
    let mut m = offenders();
    m.name = " \u{3000} ".into();
    for stage in [Stage::Name, Stage::Reserved] {
        let (_, base) = run(&m, stage);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Default::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                call(&m, stage, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original spec reservation stop"
            );
            assert!(
                o.events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn work_and_copy_limits_accumulate_across_calls_in_the_original_session() {
    let mut m = offenders();
    m.name = " ".into();
    for stage in [Stage::Name, Stage::Reserved] {
        let (_, base) = run(&m, stage);
        for bytes in [false, true] {
            let mut o = Observer {
                work_cap: (!bytes).then_some(base.work),
                byte_cap: bytes.then_some(base.bytes),
                ..Default::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            call(&m, stage, &mut s).unwrap();
            assert_eq!(
                call(&m, stage, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            let first = s.first_refusal().unwrap().progress;
            assert_eq!(
                call(&m, stage, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, first);
        }
    }
}
#[test]
fn actual_long_decimal_scan_can_stop_interior_before_any_diagnostic_allocation() {
    let mut m = fixture();
    let key = "fn:".to_owned() + &"9".repeat(3000);
    rows(&mut m, &[&key]);
    let base = private_trace(&m);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.phase == ExecutionPhase::Validation && e.work == 1 && e.copy_bytes == 1)
        .nth(100)
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
    assert_eq!(state.name.capacity(), 0);
    assert_eq!(state.detail.capacity(), 0);
    assert!(state.errors.is_empty());
    assert_eq!(
        work.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn actual_prior_key_comparison_can_stop_with_the_first_complete_error_still_retained() {
    let mut m = fixture();
    let key = "fn:".to_owned() + &"9".repeat(3000);
    rows(&mut m, &[&key, &key]);
    let base = private_trace(&m);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.phase == ExecutionPhase::Validation && e.work == 1 && e.copy_bytes == 2)
        .nth(100)
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
    assert_eq!(state.errors.len(), 1);
    assert!(detail(&state.errors[0]).contains("does not parse"));
    assert_eq!(state.name.capacity(), 0);
    assert_eq!(state.detail.capacity(), 0);
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn full_pending_name_and_detail_survive_distinct_output_reserve_and_move() {
    let mut m = fixture();
    m.spec_modules[0].name = TRUST_INTERNAL_SPEC_PREFIX.to_owned() + "unknown";
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
        assert_eq!(state.name, m.spec_modules[0].name);
        assert!(state.detail.ends_with("compiler-internal disclosure"));
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn later_shape_output_move_keeps_prior_complete_errors_and_pending_origin_text() {
    let m = offenders();
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
    assert_eq!(state.errors, reserved_spec_module_errors(&m)[..2]);
    assert_eq!(state.name, m.spec_modules[0].name);
    assert!(state.detail.ends_with("origin `external(λ'\norigin)`"));
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn bounded_raw_name_copy_keeps_its_actual_prefix_on_interior_stop() {
    let mut m = fixture();
    m.spec_modules[0].name = TRUST_INTERNAL_SPEC_PREFIX.to_owned() + &"x".repeat(3000);
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
    assert_eq!(state.name, &m.spec_modules[0].name[..1024]);
    assert_eq!(state.detail.capacity(), 0);
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn sticky_retirement_consumes_pending_name_detail_and_all_completed_errors() {
    let m = offenders();
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
    state.detail = "detail".repeat(1000);
    arm.set(true);
    assert_eq!(
        state.finish(Ok(()), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn preexisting_stop_prevents_both_name_and_namespace_input_walks() {
    let m = offenders();
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
    for stage in [Stage::Name, Stage::Reserved] {
        assert_eq!(
            call(&m, stage, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
    }
    assert_eq!(o.events, vec![first]);
}
#[test]
fn supplied_instruction_site_and_zero_fuel_are_shared_across_both_constituents() {
    let m = offenders();
    let exact = ExecutionSite::Instruction(trust_ir::interpret::InstructionSite {
        function: FuncId::new(1),
        block: BlockId::new(3),
        instruction_index: 8,
    });
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..Default::default()
        },
        &mut o,
    );
    assert!(
        validate_module_name_observed(&m, &mut s, exact)
            .unwrap()
            .is_empty()
    );
    assert_eq!(
        validate_reserved_spec_module_names_observed(&m, &mut s, exact).unwrap(),
        reserved_spec_module_errors(&m)
    );
    assert_eq!(s.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}
