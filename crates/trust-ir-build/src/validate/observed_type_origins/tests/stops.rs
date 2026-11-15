// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_key_compare_render_copy_growth_cleanup_and_publication_callback_refuses() {
    let m = fixture();
    let (_, base) = run(&m);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_type_origins_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original origin stop");
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
fn original_work_and_copy_cumulate_across_complete_calls_without_reset() {
    let m = fixture();
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_type_origins_observed(&m, &mut s, site())
                .unwrap()
                .len(),
            3
        );
        assert_eq!(
            validate_module_type_origins_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_type_origins_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn real_clean_name_equality_can_stop_interior_before_any_error_is_created() {
    let origin = TypeOrigin::Clean {
        decl: "x".repeat(10000),
        env_digest: ProofDigest::zero(),
    };
    let mut m = Module::new("long-compare");
    m.structs = vec![
        strukt(0, "first", Some(origin.clone())),
        strukt(1, "second", Some(origin)),
    ];
    let mut o = Observer {
        work_cap: Some(5000),
        ..Observer::default()
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
    assert_eq!(state.keys.len(), 2);
    assert_eq!(state.seen, vec![0]);
    assert!(state.errors.is_empty());
    assert_eq!(state.origin.capacity(), 0);
    assert_eq!(work.session.first_refusal().unwrap().progress.work, 1024);
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn actual_scalar_render_stop_retains_partial_origin_before_names_and_output() {
    let origin = TypeOrigin::Clean {
        decl: "beforeλafter".into(),
        env_digest: ProofDigest::zero(),
    };
    let (_, base) = spelling(&origin);
    let scalar = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.work == 8 * u32::BITS as usize && e.copy_bytes == size_of::<core::char::EscapeDebug>()
        })
        .nth(3)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(scalar),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut output = String::new();
    assert_eq!(
        origin::write(&origin, &mut work, &mut output),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(output, "clean(decl=\"bef");
    work.retire_text(output);
    assert!(
        o.events
            .iter()
            .skip(scalar)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn real_pending_origin_and_both_names_survive_separate_error_reserve_and_move_stops() {
    let mut m = Module::new("pending");
    m.structs = vec![
        strukt(0, "first-owned", Some(rust())),
        strukt(1, "second-owned", Some(rust())),
    ];
    let mut base = Observer::default();
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        state.run(&m, &mut work).unwrap();
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
    let positions = base
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
    assert_eq!(positions.len(), 2);
    for (n, stop) in positions.into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
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
        assert_eq!(state.origin, rust().to_string());
        assert_eq!(state.first, "first-owned");
        assert_eq!(state.second, "second-owned");
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn initial_header_and_final_publication_refuse_with_no_partial_result() {
    let m = fixture();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_type_origins_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(o.events.len(), 1);
    let (_, base) = run(&m);
    let stop = base.events.len();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_type_origins_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(o.events.len() > stop);
    assert!(
        o.events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn cleanup_refusal_consumes_all_borrowed_indexes_partial_text_and_completed_diagnostics() {
    let m = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &mut work).unwrap();
    state.origin = "origin".repeat(1000);
    state.first = "first".repeat(1000);
    state.second = "second".repeat(1000);
    arm.set(true);
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.publication(1, size_of::<Vec<ValidationError>>()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn existing_original_refusal_prevents_all_origin_work_and_keeps_the_first_cause() {
    let m = fixture();
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 3,
        copy_bytes: 0,
    };
    assert!(s.admit(first).is_err());
    assert_eq!(
        validate_module_type_origins_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(o.events, vec![first]);
}
