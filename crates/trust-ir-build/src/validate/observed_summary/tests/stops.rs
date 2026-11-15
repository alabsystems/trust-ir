// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_whole_summary_callback_refuses_without_a_partial_diagnostic_vector() {
    // Both full nonempty stage output and every empty-child buffer route.
    for (m, f, s) in [mixed(), fixture()] {
        let (_, base) = run(&m, &f, &s, ImportPolicy::Structural);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_function_summary_observed(
                    &m,
                    &f,
                    &s,
                    ImportPolicy::Structural,
                    &mut owner,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                owner.first_refusal().unwrap().progress,
                base.events[stop - 1]
            );
            assert_eq!(
                owner.first_refusal().unwrap().cause,
                "original whole-summary stop"
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
fn cumulative_work_and_copy_caps_span_every_constituent_and_repeated_whole_calls() {
    let (m, f, s) = mixed();
    let (_, base) = run(&m, &f, &s, ImportPolicy::Structural);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_function_summary_observed(
            &m,
            &f,
            &s,
            ImportPolicy::Structural,
            &mut owner,
            site(),
        )
        .unwrap();
        assert_eq!(
            validate_function_summary_observed(
                &m,
                &f,
                &s,
                ImportPolicy::Structural,
                &mut owner,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = owner.first_refusal().unwrap().progress;
        assert_eq!(
            validate_function_summary_observed(
                &m,
                &f,
                &s,
                ImportPolicy::Structural,
                &mut owner,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(owner.first_refusal().unwrap().progress, first);
        assert_eq!(owner.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn first_header_refusal_prevents_every_child_and_all_scratch_allocation() {
    let (m, f, s) = mixed();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_function_summary_observed(
            &m,
            &f,
            &s,
            ImportPolicy::Structural,
            &mut owner,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(o.events.len(), 1);
}
#[test]
fn rejected_final_publication_consumes_all_complete_stage_outputs() {
    let (m, f, s) = mixed();
    let (_, base) = run(&m, &f, &s, ImportPolicy::Structural);
    let mut o = Observer {
        stop: Some(base.events.len()),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_function_summary_observed(
            &m,
            &f,
            &s,
            ImportPolicy::Structural,
            &mut owner,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        owner.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(o.events.len() > base.events.len());
    assert!(
        o.events
            .iter()
            .skip(base.events.len())
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
