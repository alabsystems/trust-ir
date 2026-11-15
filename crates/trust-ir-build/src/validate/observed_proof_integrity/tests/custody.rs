// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_returned_header_batch_is_held_before_first_parent_append_fee() {
    let m = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let child = validate_module_proof_obligation_header_observed(&m, &mut s, site()).unwrap();
    let child_bound = calls.get();
    let expected = child.clone();
    retire_validation_errors_observed(child, &mut s, site()).unwrap();
    drop(s);
    let child_events = o.events[..child_bound].to_vec();
    let cut = 1 + child_bound + 1;
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
    assert_eq!(state.batch, expected);
    assert_eq!(state.errors.capacity(), 0);
    assert!(state.row.is_none());
    drain(&mut state, &mut w);
    assert!(empty(&state));
    drop(w);
    drop(s);
    assert_eq!(&o.events[1..1 + child_bound], child_events.as_slice());
}
#[test]
fn every_pending_row_cut_retains_whole_row_remaining_tail_and_prior_errors() {
    let batch = vec![error("a"), error("b"), error("c")];
    let prior = error("prior");
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        batch: batch.clone(),
        errors: vec![prior.clone()],
        row: None,
    };
    state.append(&mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    let mut found = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            batch: batch.clone(),
            errors: vec![prior.clone()],
            row: None,
        };
        assert_eq!(
            state.append(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if let Some(row) = &state.row {
            found = true;
            let transferred = state.errors.len() - 1;
            assert_eq!(state.errors[0], prior);
            assert_eq!(row, &batch[transferred]);
            assert_eq!(state.batch.len(), batch.len() - transferred - 1);
            let mut remaining = state.batch.clone();
            remaining.reverse();
            assert_eq!(remaining, batch[transferred + 1..]);
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    assert!(found);
}
#[test]
fn parent_reserve_preallocation_and_transfer_cuts_both_keep_first_full_row() {
    let batch = vec![error("full first"), error("full second")];
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        batch: batch.clone(),
        ..State::default()
    };
    state.append(&mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    let (mut pre, mut post) = (false, false);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            batch: batch.clone(),
            ..State::default()
        };
        assert_eq!(
            state.append(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if state.errors.is_empty() && state.row.as_ref() == Some(&batch[0]) {
            if state.errors.capacity() == 0 {
                pre = true
            } else {
                post = true
            }
            assert_eq!(state.batch, vec![batch[1].clone()]);
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    assert!(pre && post);
}
#[test]
fn interrupted_actual_header_reversal_keeps_every_nested_child_owned() {
    let batch = vec![error("a"), error("b"), error("c"), error("d")];
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        batch: batch.clone(),
        ..State::default()
    };
    state.append(&mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    let mut found = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            batch: batch.clone(),
            ..State::default()
        };
        assert_eq!(
            state.append(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if state.row.is_none()
            && state.errors.is_empty()
            && state.batch.len() == batch.len()
            && state.batch != batch
        {
            found = true;
            for row in &batch {
                assert_eq!(state.batch.iter().filter(|e| *e == row).count(), 1);
            }
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    assert!(found);
}
#[test]
fn sticky_cleanup_consumes_full_pending_row_batch_tail_and_earlier_errors() {
    let mut state = State {
        errors: vec![error("prior")],
        batch: vec![error("tail1"), error("tail2")],
        row: Some(error("pending")),
    };
    let mut o = Observer {
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert!(w.session.first_refusal().is_some());
    drop(w);
    drop(s);
    assert!(o.events.len() > 30);
    assert!(
        o.events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn next_child_refuses_existing_pending_row_without_overwriting_any_owned_body() {
    let mut state = State {
        errors: vec![error("prior")],
        batch: Vec::new(),
        row: Some(error("held")),
    };
    let saved = state.row.clone();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        state.before_child(&mut w),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(state.row, saved);
    assert_eq!(state.errors, vec![error("prior")]);
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
