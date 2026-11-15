// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_real_ssa_construction_query_operand_retirement_and_publication_event_can_stop() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    for (index, expected) in baseline.events.into_iter().enumerate() {
        let mut observer = Observer {
            stop: Some(index + 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_ssa_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, expected);
        assert_eq!(session.first_refusal().unwrap().cause, "original stop");
        assert!(
            observer
                .events
                .iter()
                .skip(index + 1)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn original_cumulative_work_and_bytes_include_full_prerequisites_and_repeated_ssa_calls() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work),
            byte_cap: bytes.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_ssa_observed(&f, &mut session, site()).unwrap(),
            ordinary(&f)
        );
        assert_eq!(
            validate_function_ssa_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn definition_growth_is_refused_before_first_owned_index_allocation() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    assert_eq!(
        state.define(0, BlockId::new(0), None, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        (state.definitions.len(), state.definitions.capacity()),
        (0, 0)
    );
    assert!(state.errors.is_empty());
    state.retire_scratch(&mut work);
}
fn direct(state: &mut Checking, f: &Function, work: &mut Work<'_, '_, Observer>) -> R {
    state.collect(f, work)?;
    state.dominators = Some(DominatorTree::new_observed(f, work.session, work.site)?);
    state.uses(f, work)?;
    state.merge(work)
}
#[test]
fn actual_returned_operand_vector_and_complete_tree_stay_owned_across_later_refusal() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    direct(&mut state, &f, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let mut saw_owned = false;
    // Identical direct entry points for baseline/replay: no public wrapper
    // header offset is reused to select a private constituent event.
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = Checking::default();
        let result = direct(&mut state, &f, &mut work);
        if result.is_err() && !state.operands.is_empty() && state.dominators.is_some() {
            saw_owned = true;
        }
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert!(state.dominators.is_none());
        assert_eq!((state.operands.len(), state.operands.capacity()), (0, 0));
        assert!(
            state.definitions.is_empty()
                && state.missing.is_empty()
                && state.dominance.is_empty()
                && state.errors.is_empty()
        );
    }
    assert!(saw_owned);
}
#[test]
fn final_outer_publication_refusal_occurs_after_all_analysis_scratch_retired() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    let mut observer = Observer {
        stop: Some(baseline.events.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_ssa_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > baseline.events.len() + 4);
    assert!(
        observer
            .events
            .iter()
            .skip(baseline.events.len())
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
