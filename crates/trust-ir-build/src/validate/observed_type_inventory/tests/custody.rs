// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_instruction_root_vector_is_held_before_first_parent_walk_fee() {
    let m = Module::new("");
    let r = registry();
    let inst = cast();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let roots = inst.inline_types_observed(&mut s, site()).unwrap();
    let bound = calls.get();
    drop(s);
    assert_eq!(roots.len(), 2);
    let cut = 1 + bound + 1;
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
        state.instruction(&m, &r, &inst, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.roots.len(), 2);
    for (a, b) in state.roots.iter().zip(&roots) {
        assert!(core::ptr::eq(*a, *b));
    }
    assert!(state.frames.is_empty());
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
#[test]
fn whole_node_tuple_is_held_before_parent_census_or_aggregation_fee() {
    let m = Module::new("");
    let r = registry();
    let ty = invalid();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let child = validate_type_reference_node_observed(&m, &r, &ty, "L", &mut s, site()).unwrap();
    let bound = calls.get();
    let saved = child.clone();
    retire_validation_errors_observed(child.0, &mut s, site()).unwrap();
    drop(s);
    let mut o = Observer {
        stop: Some(1 + bound + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        location: "L".into(),
        ..State::default()
    };
    assert_eq!(
        state.node(&m, &r, &ty, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.batch, saved.0);
    assert_eq!(state.child_census, saved.1);
    assert_eq!(state.census, NominalCensus::default());
    assert_eq!(state.errors.capacity(), 0);
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
#[test]
fn pending_full_node_row_and_prior_output_remain_owned_through_parent_fees() {
    let m = Module::new("");
    let r = registry();
    let ty = invalid();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        location: "L λ\0FULL".into(),
        errors: vec![prior()],
        ..State::default()
    };
    state.node(&m, &r, &ty, &mut w).unwrap();
    let end = calls.get();
    let child = state.errors[1].clone();
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
            location: "L λ\0FULL".into(),
            errors: vec![prior()],
            ..State::default()
        };
        assert_eq!(
            state.node(&m, &r, &ty, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if let Some(row) = &state.row {
            found = true;
            assert_eq!(row, &child);
            assert_eq!(state.errors, vec![prior()]);
            assert!(state.batch.is_empty());
            assert_eq!(state.location, "L λ\0FULL");
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    assert!(found);
}
#[test]
fn actual_nested_tree_stop_keeps_unvisited_borrowed_frames_until_retirement() {
    let m = Module::new("");
    let r = registry();
    let ty = Ty::Tuple(vec![Ty::Tuple(vec![d(), d()]), d()]);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        location: "L".into(),
        ..State::default()
    };
    state.ty(&m, &r, &ty, &mut w).unwrap();
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
            location: "L".into(),
            ..State::default()
        };
        assert_eq!(
            state.ty(&m, &r, &ty, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if state.frames.len() >= 2 {
            found = true;
            assert!(state.frames.capacity() >= state.frames.len());
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    assert!(found);
}
#[test]
fn sticky_cleanup_consumes_all_borrowed_frames_roots_raw_location_and_owned_rows() {
    let ty = d();
    let mut state = State {
        location: "partial λ\0FULL".into(),
        frames: vec![
            Frame::Visit(&ty),
            Frame::Children(core::slice::from_ref(&ty), 0),
        ],
        roots: vec![&ty, &ty],
        errors: vec![prior()],
        batch: vec![prior(), prior()],
        row: Some(prior()),
        census: NominalCensus {
            dialect: true,
            handle: true,
        },
        child_census: NominalCensus {
            dialect: true,
            handle: true,
        },
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
    assert!(o.events.len() > 40);
    assert!(
        o.events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn successful_whole_result_stays_owned_until_explicit_original_caller_retirement() {
    let m = fixture();
    let r = registry();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (out, c) = validate_type_table_references_observed(&m, &r, &mut s, site()).unwrap();
    let saved = out.clone();
    let bound = calls.get();
    assert!(c.dialect && c.handle);
    assert_eq!(out, saved);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    drop(s);
    // Explicit caller retirement consumes all payloads, then publishes its
    // own terminal receipt under the original session and site.
    let (publication, cleanup) = o.events[bound..].split_last().unwrap();
    assert!(!cleanup.is_empty());
    assert!(
        cleanup
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
    );
    assert_eq!(
        *publication,
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0,
        }
    );
}
