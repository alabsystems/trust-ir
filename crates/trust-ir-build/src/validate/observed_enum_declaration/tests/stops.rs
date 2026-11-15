// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_public_callback_refuses_with_the_original_site_and_first_cause() {
    let mut m = fixture();
    m.enums[0].variants[0].field_names.push("x".into());
    let (_, base) = run(&m, 0);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_enum_declaration_observed(&m, 0, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original enum declaration stop"
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
fn work_and_copy_budgets_accumulate_across_calls_without_owner_or_fuel_reset() {
    let m = fixture();
    let (_, base) = run(&m, 0);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_enum_declaration_observed(&m, 0, &mut s, site()).unwrap();
        assert_eq!(
            validate_enum_declaration_observed(&m, 0, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_enum_declaration_observed(&m, 0, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn owning_discriminant_result_is_in_state_before_its_first_fallible_snapshot() {
    let m = fixture();
    let base = private_trace(&m, 0);
    let stop = base
        .events
        .iter()
        .position(|e| {
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
    assert_eq!(
        state.run(&m, 0, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.values, vec![0, 1]);
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn complete_three_strings_survive_distinct_output_reserve_and_move_cuts() {
    let mut m = fixture();
    m.enums[0].variants[0].field_names.push("x".into());
    let base = private_trace(&m, 0);
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
            state.run(&m, 0, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.location, "enum.7 (fullλ'\nname) variant 0 (A)");
        assert_eq!(state.expected, "field_names empty or exactly 0 entries");
        assert_eq!(state.actual, "1 field names");
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn actual_long_name_copy_can_refuse_with_the_earlier_utf8_prefix_still_owned() {
    let mut m = fixture();
    m.enums[0].name = "λ".repeat(3000);
    m.enums[0].variants[0].field_names.push("x".into());
    let base = private_trace(&m, 0);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .nth(1)
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
        state.run(&m, 0, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.location.starts_with("enum.7 ("));
    assert!(state.location.contains(&"λ".repeat(512)));
    assert!(state.location.len() < m.enums[0].name.len());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn cleanup_refusal_drains_all_values_text_and_completed_diagnostics_before_publication() {
    let mut m = fixture();
    m.enums[0].variants[0].field_names.push("x".into());
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
    state.run(&m, 0, &mut work).unwrap();
    state.location = "partial".repeat(1000);
    state.values = vec![0; 1000];
    arm.set(true);
    assert_eq!(
        state.finish(Ok(()), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn preexisting_stop_refuses_before_any_input_read_and_preserves_original_record() {
    let m = fixture();
    let mut o = Observer {
        stop: Some(1),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 7,
        copy_bytes: 0,
    };
    assert!(s.admit(first).is_err());
    assert_eq!(
        validate_enum_declaration_observed(&m, 0, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(o.events, vec![first]);
}
