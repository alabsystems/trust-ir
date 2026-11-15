// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_policy_event_refuses_and_retains_original_cause_through_owned_cleanup() {
    let f = fixture();
    for case in [Case::Memory, Case::Havoc] {
        let (_, baseline) = observed(&f, case);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                run(&f, case, &mut session),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "original stop");
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_work_and_requested_bytes_span_both_distinct_annotation_constituents() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for case in [Case::Memory, Case::Havoc] {
        run(&f, case, &mut session).unwrap();
    }
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        run(&f, Case::Memory, &mut session).unwrap();
        assert_eq!(
            run(&f, Case::Havoc, &mut session),
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
fn diagnostic_string_storage_refusal_precedes_first_owned_allocation() {
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
        state.role_text(3, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        (
            state.text.capacity(),
            state.roles.capacity(),
            state.errors.capacity()
        ),
        (0, 0, 0)
    );
    state.retire_scratch(&mut work);
}
#[test]
fn partial_name_roles_and_complete_pending_memory_error_stay_in_custody_on_stop() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    state.memory(&f, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let (mut partial_name, mut roles, mut pending) = (false, false, false);
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
        let result = state.memory(&f, &mut work);
        partial_name |= !state.name.is_empty() && state.name.len() < f.name.len();
        roles |= !state.roles.is_empty();
        if let Some(ValidationError::ConflictingFunctionMemoryRoles { func_name, roles }) =
            &state.pending
        {
            assert!(result.is_err());
            assert_eq!(func_name, &f.name);
            assert_eq!(roles.len(), 2);
            pending = true;
        }
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert!(state.pending.is_none() && state.roles.is_empty() && state.errors.is_empty());
        assert!(state.text.is_empty() && state.name.is_empty());
    }
    assert!(partial_name && roles && pending);
}
#[test]
fn wide_annotation_list_stops_inside_actual_role_scan_without_partial_acceptance() {
    let mut f = function(vec![]);
    f.proofs = vec![ProofAnnotation::Tainted; 50_000];
    let mut observer = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        run(&f, Case::Memory, &mut session),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert!(observer.events.len() < 100);
}
#[test]
fn final_publication_refusal_has_nonvacuous_nested_string_and_vector_retirement() {
    let f = fixture();
    for case in [Case::Memory, Case::Havoc] {
        let (_, baseline) = observed(&f, case);
        let mut observer = Observer {
            stop: Some(baseline.events.len()),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            run(&f, case, &mut session),
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
}
