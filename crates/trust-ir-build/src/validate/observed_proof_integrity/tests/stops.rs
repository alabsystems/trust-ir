// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_real_child_aggregation_retirement_and_outer_publication_callback_refuses() {
    let m = fixture();
    let (_, baseline, bound) = run(&m);
    for cut in 1..=bound {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_proof_obligation_integrity_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn successive_complete_integrity_calls_share_original_cumulative_work_and_copy() {
    let m = fixture();
    let (_, baseline, _) = run(&m);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes + 1)
        } else {
            o.work_cap = Some(baseline.work + 1)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_module_proof_obligation_integrity_observed(&m, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_proof_obligation_integrity_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn final_whole_vector_publication_refusal_returns_no_completed_prefix() {
    let m = fixture();
    let (_, baseline, bound) = run(&m);
    assert_eq!(
        baseline.events[bound - 1].copy_bytes,
        size_of::<Vec<ValidationError>>()
    );
    let mut o = Observer {
        stop: Some(bound),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_proof_obligation_integrity_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert!(o.events.len() > bound);
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn empty_batch_retirement_refusal_stops_before_later_children_and_outer_success() {
    let m = Module::new("");
    let mut o = Observer {
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_proof_obligation_integrity_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
    drop(s);
    assert_eq!(
        o.events.last().unwrap().phase,
        ExecutionPhase::ScratchRetirement
    );
}
#[test]
fn original_site_zero_fuel_and_existing_first_stop_are_preserved() {
    let m = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let out = validate_module_proof_obligation_integrity_observed(&m, &mut s, site()).unwrap();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        validate_module_proof_obligation_integrity_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original integrity stop");
    drop(s);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn earlier_whole_group_remains_owned_when_the_next_real_child_is_refused() {
    let m = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.before_child(&mut w).unwrap();
    state.batch = validate_module_proof_obligation_header_observed(&m, w.session, w.site).unwrap();
    state.append(&mut w).unwrap();
    let cut = calls.get() + 1;
    let saved = state.errors.clone();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&m, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, saved);
    assert_eq!(state.errors.len(), 2);
    assert_eq!(state.batch.capacity(), 0);
    assert!(state.row.is_none());
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
