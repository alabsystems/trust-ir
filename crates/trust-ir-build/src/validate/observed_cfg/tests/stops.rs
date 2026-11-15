// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_cfg_callback_refuses_with_original_cause_and_cleanup_only() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_control_flow_observed(&f, &mut session, site()),
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
#[test]
fn cumulative_work_and_bytes_cover_repeated_whole_cfg_queries() {
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
            validate_function_control_flow_observed(&f, &mut session, site()).unwrap(),
            ordinary(&f)
        );
        assert_eq!(
            validate_function_control_flow_observed(&f, &mut session, site()),
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
fn first_block_index_growth_refuses_before_allocation() {
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
        work.push(&mut state.blocks, 0),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((state.blocks.len(), state.blocks.capacity()), (0, 0));
    state.retire_scratch(&mut work);
}
#[test]
fn duplicate_key_diagnostic_is_kept_across_error_vector_growth_refusal() {
    let f = function(
        vec![block(
            0,
            switch(vec![Constant::Int(3), Constant::Int(3)], vec![0; 2], 0),
        )],
        0,
    );
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
    let mut saw_pending = false;
    let mut saw_before_allocation = false;
    for stop in 1..=baseline.events.len() {
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
        let _ = state.walk(&f, &mut work);
        if let Some(ValidationError::DuplicateSwitchCase { value, .. }) = &state.pending {
            assert_eq!(value, "3");
            saw_pending = true;
            saw_before_allocation |= state.errors.capacity() == 0;
        }
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
        assert!(state.pending.is_none());
        assert!(state.errors.is_empty());
    }
    assert!(saw_pending && saw_before_allocation);
}
#[test]
fn interior_long_key_comparison_cancellation_is_not_an_unequal_answer() {
    let mut baseline = Observer::default();
    let left = "λ".repeat(3000);
    let right = left.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert!(work.equal(&left, &right).unwrap());
    assert!(baseline.events.len() > 4);
    let mut observer = Observer {
        stop_at: Some(3),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        work.equal(&left, &right),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(work.session.first_refusal().unwrap().cause, "original stop");
}
#[test]
fn final_publication_stop_retires_completed_errors_and_all_cfg_buffers() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    let mut observer = Observer {
        stop_at: Some(baseline.events.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_control_flow_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > baseline.events.len());
    assert!(
        observer
            .events
            .iter()
            .skip(baseline.events.len())
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
