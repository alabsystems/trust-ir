// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

#[test]
fn every_actual_callback_refuses_with_original_cause_and_cleanup_only() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_information_flow_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let refusal = session.first_refusal().unwrap();
        assert_eq!(refusal.cause, "original stop");
        assert_eq!(refusal.progress, baseline.events[stop - 1]);
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
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
fn cumulative_work_and_bytes_share_one_original_session_across_calls() {
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
            validate_function_information_flow_observed(&f, &mut session, site()).unwrap(),
            validate_information_flow(&f)
        );
        assert_eq!(
            validate_function_information_flow_observed(&f, &mut session, site()),
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
fn first_taint_storage_refuses_before_any_allocation() {
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
        work.insert(&mut state.tainted, 1),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((state.tainted.len(), state.tainted.capacity()), (0, 0));
    assert_eq!(work.session.first_refusal().unwrap().cause, "bytes");
    state.retire_scratch(&mut work);
    assert_eq!(state.tainted.capacity(), 0);
}

#[test]
fn fixed_pending_diagnostic_survives_first_error_storage_refusal() {
    let mut observer = Observer {
        byte_cap: Some(size_of::<(u32, u32)>()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    assert_eq!(
        state.diagnostic(7, 42, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.pending, Some((7, 42)));
    assert_eq!((state.errors.len(), state.errors.capacity()), (0, 0));
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(state.pending.is_none());
    assert_eq!(work.session.first_refusal().unwrap().cause, "bytes");
}

#[test]
fn actual_linear_membership_stop_is_not_false_and_proof_scan_stops_before_seed() {
    let rows = (0..4096).collect::<Vec<u32>>();
    let mut observer = Observer {
        stop_at: Some(64),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        work.contains(&rows, 5000),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(work.session.first_refusal().unwrap().cause, "original stop");

    let mut node = seed(1);
    node.proofs = vec![ProofAnnotation::Pure; 4096];
    node.proofs.push(ProofAnnotation::Tainted);
    let f = function(vec![block(0, vec![node])]);
    let mut observer = Observer {
        stop_at: Some(64),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    assert_eq!(
        state.walk(&f, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((state.tainted.len(), state.tainted.capacity()), (0, 0));
    state.retire_scratch(&mut work);
    assert_eq!(work.session.first_refusal().unwrap().cause, "original stop");
}

#[test]
fn late_membership_stop_keeps_and_retires_the_complete_owned_operand_vector() {
    let f = function(vec![block(0, vec![seed(1), sink(&vec![1; 1024])])]);
    // Both baseline and replay enter Checking::walk directly, without the
    // public header. The second publication is the wide propagation operand
    // vector; three callbacks later is its actual first membership comparison.
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    state.walk(&f, &mut work).unwrap();
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    let publication_index = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.phase == ExecutionPhase::Publication)
        .nth(1)
        .unwrap()
        .0;
    let stop = publication_index + 4;
    let mut observer = Observer {
        stop_at: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    assert_eq!(
        state.walk(&f, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.operands, vec![v(1); 1024]);
    assert!(state.operands.capacity() >= 1024);
    assert!(state.errors.is_empty());
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert_eq!((state.operands.len(), state.operands.capacity()), (0, 0));
    assert_eq!((state.tainted.len(), state.tainted.capacity()), (0, 0));
    assert_eq!(work.session.first_refusal().unwrap().cause, "original stop");
    assert!(observer.events.len() > stop + 1024);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn first_retirement_refusal_prevents_publication_and_keeps_the_original_cause() {
    let f = fixture();
    let mut observer = Observer {
        stop_phase: Some(ExecutionPhase::ScratchRetirement),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_information_flow_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
    assert_eq!(session.first_refusal().unwrap().cause, "original stop");
    let first = observer
        .events
        .iter()
        .position(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .unwrap();
    assert!(observer.events.len() > first + 1);
    assert!(
        observer
            .events
            .iter()
            .skip(first)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn final_publication_refusal_retires_completed_errors_after_all_scratch() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop_at: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_information_flow_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    // Five completed fixed-field errors each have explicit pre/post retirement,
    // followed by error-vector buffer deallocation and its final poll.
    assert!(observer.events.len() >= stop + 5 * 3 + 2);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
