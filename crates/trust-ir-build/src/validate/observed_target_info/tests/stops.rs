// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_scan_lookup_copy_growth_cleanup_and_publication_callback_refuses() {
    for kind in 0..8 {
        let m = fixtures::module(kind);
        let (_, base) = run(&m);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_module_target_info_observed(&m, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "original target stop");
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
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
fn original_work_and_copy_cumulate_without_replacement_owner_or_fuel() {
    let m = fixtures::module(0);
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_module_target_info_observed(&m, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_target_info_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_target_info_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn actual_full_direct_lookup_can_stop_interior_before_any_boundary_allocation() {
    let mut m = fixtures::module(0);
    let caller = m.functions.remove(0);
    let callee = m.functions.remove(0);
    m.functions = (100..600)
        .map(|id| fixtures::function(id, "unrelated", CallingConv::Rust))
        .collect();
    m.functions.push(callee);
    m.functions.insert(0, caller);
    let mut o = Observer {
        work_cap: Some(4000),
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
    assert_eq!(state.boundary.capacity(), 0);
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn actual_name_chunk_stop_retains_partial_complete_boundary_prefix() {
    let mut m = fixtures::module(0);
    m.functions[0].name = "λ".repeat(3000);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &mut work).unwrap();
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == 1024 && e.copy_bytes == 1024)
        .nth(1)
        .unwrap()
        .0
        + 1;
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
    assert_eq!(
        state.boundary,
        "cross-convention call edge `".to_owned() + &"λ".repeat(512)
    );
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn complete_boundary_survives_distinct_error_reserve_and_move_header_refusals() {
    let m = fixtures::module(0);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &mut work).unwrap();
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
        assert_eq!(
            state.boundary,
            "cross-convention call edge `caller` (rustcc) -> `callee` (ccc)"
        );
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn initial_state_and_final_output_publication_refuse_before_escape() {
    let m = fixtures::module(0);
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_target_info_observed(&m, &mut s, site()),
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
        validate_module_target_info_observed(&m, &mut s, site()),
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
fn cleanup_consumes_actual_completed_diagnostic_and_partial_boundary_after_sticky_refusal() {
    let m = fixtures::module(0);
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
    assert_eq!(state.errors.len(), 1);
    state.boundary = "partial".repeat(1000);
    arm.set(true);
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn preexisting_stop_performs_no_target_walk_and_keeps_original_first_cause() {
    let m = fixtures::module(0);
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
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
        validate_module_target_info_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(o.events, vec![first]);
}
