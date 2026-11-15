// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::field_reassign_with_default,
    clippy::filter_next,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_callback_refuses_without_a_shorter_successful_repr_list() {
    let m = fixture();
    let (_, base) = run(&m);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_struct_abi_repr_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert_eq!(s.first_refusal().unwrap().cause, "original struct ABI stop");
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cumulative_original_work_and_copy_grants_are_never_restarted() {
    let m = fixture();
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_module_struct_abi_repr_observed(&m, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_struct_abi_repr_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_struct_abi_repr_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn actual_returned_arc_and_error_are_owned_at_the_first_query_snapshot_cut() {
    for ty in [Ty::Unit, Ty::Struct(StructId::new(999))] {
        let m = Module::new("query custody");
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        state.table = Some(LayoutTable::new_observed(&m, work.session, work.site).unwrap());
        state.query(&ty, &mut work).unwrap();
        drain(&mut state, &mut work);
        let stop = o
            .events
            .iter()
            .rposition(|e| {
                e.phase == ExecutionPhase::Validation
                    && e.work == 7
                    && e.copy_bytes == size_of::<bool>()
            })
            .unwrap()
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
        state.table = Some(LayoutTable::new_observed(&m, work.session, work.site).unwrap());
        assert_eq!(
            state.query(&ty, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.shape.is_some(), matches!(ty, Ty::Unit));
        assert_eq!(state.error.is_some(), !matches!(ty, Ty::Unit));
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn output_reserve_and_header_move_are_distinct_identical_private_entry_cuts() {
    let mut m = fixture();
    m.structs.truncate(1);
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
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn later_repr_error_move_refusal_retains_the_complete_first_physical_diagnostic() {
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
    assert_eq!(state.errors, oracle(&m)[..1]);
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn sticky_retirement_still_consumes_real_arc_error_and_all_completed_diagnostics() {
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
    state.shape = Some(
        state
            .table
            .as_ref()
            .unwrap()
            .ty_layout_observed(&Ty::Unit, work.session, work.site)
            .unwrap()
            .unwrap(),
    );
    state.error = Some(LayoutError::TargetScalarLayoutUnavailable {
        triple: "pending".repeat(1000),
    });
    arm.set(true);
    assert_eq!(
        state.finish(Ok(()), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn preexisting_refusal_prevents_even_the_new_table_constructor() {
    let m = fixture();
    let mut o = Observer {
        stop: Some(1),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 4,
        copy_bytes: 0,
    };
    assert!(s.admit(first).is_err());
    assert_eq!(
        validate_module_struct_abi_repr_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(o.events, vec![first]);
}
#[test]
fn supplied_instruction_site_and_zero_execution_fuel_survive_the_entire_repr_walk() {
    let m = fixture();
    let exact = ExecutionSite::Instruction(trust_ir::interpret::InstructionSite {
        function: FuncId::new(8),
        block: BlockId::new(9),
        instruction_index: 3,
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
        validate_module_struct_abi_repr_observed(&m, &mut s, exact).unwrap(),
        oracle(&m)
    );
    assert_eq!(s.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}
