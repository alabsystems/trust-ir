// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_public_callback_refuses_without_partial_result_and_preserves_first_cause() {
    let (m, e, d) = compact();
    let (_, base) = run(&m, &e, &d);
    for stop in 1..=base.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            call(&m, &e, &d, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original field stop"
        );
        assert_eq!(
            session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn original_work_and_copy_budgets_cumulate_across_calls_without_a_fresh_grant() {
    let (m, e, d) = compact();
    let (_, base) = run(&m, &e, &d);
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        call(&m, &e, &d, &mut session).unwrap();
        assert_eq!(
            call(&m, &e, &d, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            call(&m, &e, &d, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn initial_header_and_final_output_publication_refuse_before_any_partial_escape() {
    let (m, e, d) = compact();
    let (_, base) = run(&m, &e, &d);
    for stop in [1, base.events.len()] {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            call(&m, &e, &d, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
        if stop == 1 {
            assert_eq!(observer.events.len(), 1);
        } else {
            assert_eq!(observer.events[stop - 1].phase, ExecutionPhase::Publication);
            assert!(observer.events.len() > stop);
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn a_preexisting_original_refusal_prevents_all_component_walks_and_callbacks() {
    let (m, e, d) = compact();
    let mut observer = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 17,
        copy_bytes: 0,
    };
    assert!(session.admit(first).is_err());
    assert_eq!(
        call(&m, &e, &d, &mut session),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().progress, first);
    assert_eq!(observer.events, vec![first]);
}
#[test]
fn original_instruction_coordinates_and_zero_execution_fuel_remain_unchanged() {
    let (m, e, d) = compact();
    let exact = ExecutionSite::Instruction(trust_ir::interpret::InstructionSite {
        function: FuncId::new(7),
        block: BlockId::new(9),
        instruction_index: 32,
    });
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut observer,
    );
    let out = validate_enum_layout_fields_observed(&m, &e, &d, &mut session, exact).unwrap();
    assert_eq!(out, original::run(&m, &e, &d));
    assert_eq!(session.remaining_fuel(), 0);
    assert!(observer.events.iter().all(|e| e.site == exact));
}
#[test]
fn interior_actual_field_query_can_stop_with_complete_arc_still_in_custody() {
    let (m, mut e, mut d) = fixture();
    e.variants[0].fields = vec![Ty::U8; 20];
    d.size = 20;
    d.align = 1;
    d.variant_field_offsets = vec![(0..20).collect()];
    let base = private_trace(&m, &e, &d);
    let summaries: Vec<_> = base
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Publication
                && pair[0].work == 0
                && pair[0].copy_bytes == 0
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 6
                && pair[1].copy_bytes == size_of::<Summary>()
        })
        .map(|(i, _)| i + 2)
        .collect();
    assert_eq!(summaries.len(), 40);
    let stop = summaries[7];
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&m, &e, &d, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.shape.is_some());
    assert!(state.error.is_none());
    assert!(state.errors.is_empty());
    assert!(state.ranges.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn actual_quadratic_pair_interior_is_admitted_with_all_gathered_ranges_retained() {
    let (m, mut e, mut d) = fixture();
    e.variants[0].fields = vec![Ty::Unit; 30];
    d.size = 0;
    d.align = 1;
    d.variant_field_offsets = vec![vec![0; 30]];
    let base = private_trace(&m, &e, &d);
    let pairs: Vec<_> = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 16
                && e.copy_bytes == 4 * size_of::<u64>()
        })
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(pairs.len(), 30 * 29 / 2);
    let stop = pairs[200];
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&m, &e, &d, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.ranges.len(), 30);
    assert!(state.shape.is_none());
    assert!(state.error.is_none());
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn typed_private_state_failure_is_not_published_as_an_empty_accepting_list() {
    let (m, e, d) = compact();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        table: Some(LayoutTable::new_observed(&m, work.session, work.site).unwrap()),
        expected: "retained".repeat(1000),
        ..State::default()
    };
    assert_eq!(
        state.run(&m, &e, &d, &mut work),
        Err(ObservedValueError::InvalidRange)
    );
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert!(work.session.first_refusal().is_none());
    // Generic consuming cleanup can publish only its terminal zero-cost receipt.
    assert!(
        !observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::Publication
                && e.copy_bytes == size_of::<Vec<ValidationError>>())
    );
}
