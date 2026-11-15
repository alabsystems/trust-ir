// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_callback_preserves_first_refusal_and_never_returns_a_shorter_success() {
    let m = fixture();
    let (_, base) = run(&m);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_always_memory_struct_passing_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn work_and_copy_grants_cumulate_across_full_calls_without_reset() {
    let m = fixture();
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_module_always_memory_struct_passing_observed(&m, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_always_memory_struct_passing_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_always_memory_struct_passing_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn full_returned_type_display_is_retained_before_the_first_output_reserve() {
    let mut m = fixture();
    m.func_types[0] =
        trust_ir::FuncTy::unrecorded(vec![Ty::Tuple(vec![Ty::U8; 1000])], vec![], false);
    let base = private_trace(&m);
    let stop = base
        .events
        .windows(2)
        .enumerate()
        .find(|(_, p)| {
            p[0].phase == ExecutionPhase::Publication
                && p[0].work == 1
                && p[0].copy_bytes == size_of::<String>()
                && p[1].phase == ExecutionPhase::Validation
                && p[1].work == 1
                && p[1].copy_bytes == 0
        })
        .unwrap()
        .0
        + 2;
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
    assert_eq!(state.slot, "parameter 0");
    assert_eq!(
        state.tytext.as_deref(),
        Some(m.func_types[0].params[0].to_string().as_str())
    );
    assert!(state.errors.is_empty());
    assert_eq!(state.errors.capacity(), 0);
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn complete_slot_and_type_survive_distinct_output_growth_and_header_move() {
    let mut m = fixture();
    m.func_types[0] = trust_ir::FuncTy::unrecorded(vec![Ty::Tuple(vec![])], vec![], false);
    let base = private_trace(&m);
    let cuts = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && ((e.work == 1 && e.copy_bytes == size_of::<ValidationError>())
                    || (e.work == 2
                        && e.copy_bytes == size_of::<ValidationError>() + size_of::<u32>()))
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
        assert_eq!(state.slot, "parameter 0");
        assert!(state.tytext.is_some());
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn type_display_interior_can_refuse_with_pending_slot_without_partial_type_escape() {
    let mut m = fixture();
    m.func_types[0] =
        trust_ir::FuncTy::unrecorded(vec![Ty::Tuple(vec![Ty::U8; 1000])], vec![], false);
    let base = private_trace(&m);
    // The actual TypeDisplay dispatcher charges41 before visiting each node.
    // Cut after thirty completed type nodes, not at an estimated wrapper cost.
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.phase == ExecutionPhase::Validation && e.work == 41 && e.copy_bytes == 0)
        .nth(30)
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
    assert_eq!(state.slot, "parameter 0");
    assert!(state.tytext.is_none());
    assert!(state.errors.is_empty());
    assert_eq!(
        work.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn sticky_cleanup_consumes_full_pending_type_slot_and_all_prior_diagnostics() {
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
    state.slot = "pending slot".repeat(1000);
    state.tytext = Some("pending type".repeat(1000));
    arm.set(true);
    assert_eq!(
        state.finish(Ok(()), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn preexisting_stop_prevents_policy_and_function_type_walks() {
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
        validate_module_always_memory_struct_passing_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(o.events, vec![first]);
}
#[test]
fn supplied_instruction_site_and_zero_fuel_are_preserved_through_predicate_and_display() {
    let m = fixture();
    let exact = ExecutionSite::Instruction(trust_ir::interpret::InstructionSite {
        function: FuncId::new(3),
        block: BlockId::new(2),
        instruction_index: 1,
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
        validate_module_always_memory_struct_passing_observed(&m, &mut s, exact).unwrap(),
        validate_always_memory_struct_passing(&m)
    );
    assert_eq!(s.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}
