// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn whole_successful_arc_layout_is_held_through_parent_projection_and_consumed_before_transfer() {
    let m = fixture();
    let old = LayoutTable::new(&m).ty_layout(&handle()).unwrap();
    assert_eq!(old.size_bytes(), Some(8));
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = setup(&m, &mut s);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        state
            .run(&table, &nominal, &handle(), false, None, &mut work)
            .unwrap(),
        Some(8)
    );
    assert_eq!(state.shape.as_deref(), Some(old.as_ref()));
    assert!(state.error.is_none());
    drain(&mut state, &mut work);
    assert!(empty(&state));
    dispose(table, nominal, work.session);
}
#[test]
fn complete_semantic_layout_error_remains_owned_during_its_full_reason_rendering() {
    let m = fixture();
    let ty = tuple();
    let expected = LayoutTable::new(&m).ty_layout(&ty).unwrap_err().to_string();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = setup(&m, &mut s);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        state
            .run(&table, &nominal, &ty, false, None, &mut work)
            .unwrap(),
        None
    );
    assert_eq!(state.error.as_ref().unwrap().to_string(), expected);
    assert!(state.reason.contains(&expected));
    assert!(state.shape.is_none());
    drain(&mut state, &mut work);
    assert!(empty(&state));
    dispose(table, nominal, work.session);
}
#[test]
fn complete_returned_type_display_remains_owned_before_the_next_fallible_parent_copy() {
    let m = fixture();
    let ty = tuple();
    let complete = ty.to_string();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal) = setup(&m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        state
            .run(&table, &nominal, &ty, false, None, &mut work)
            .unwrap(),
        None
    );
    let end = calls.get();
    drain(&mut state, &mut work);
    dispose(table, nominal, work.session);
    drop(work);
    drop(s);
    let mut held = false;
    let mut before_copy = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal) = setup(&m, &mut s);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let _ = state.run(&table, &nominal, &ty, false, None, &mut work);
        if state.render == complete {
            held = true;
            assert!(state.render.capacity() > 0);
            assert!(state.reason.starts_with("`"));
            if state.reason == "`" {
                before_copy = true;
            }
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
        dispose(table, nominal, work.session);
    }
    assert!(held && before_copy);
}
#[test]
fn every_private_layout_and_reason_cut_drains_full_children_and_all_partial_string_capacities() {
    let m = fixture();
    for ty in [handle(), tuple()] {
        let mut baseline = Observer::default();
        let calls = baseline.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        let (table, nominal) = setup(&m, &mut s);
        let begin = calls.get();
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        state
            .run(&table, &nominal, &ty, false, Some(3), &mut work)
            .unwrap();
        let end = calls.get();
        drain(&mut state, &mut work);
        dispose(table, nominal, work.session);
        drop(work);
        drop(s);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (table, nominal) = setup(&m, &mut s);
            let mut state = State::default();
            let mut work = Work {
                session: &mut s,
                site: site(),
            };
            assert!(
                state
                    .run(&table, &nominal, &ty, false, Some(3), &mut work)
                    .is_err()
            );
            drain(&mut state, &mut work);
            assert!(empty(&state));
            assert_eq!(
                work.session.first_refusal().unwrap().cause,
                "original slot-shape stop"
            );
            dispose(table, nominal, work.session);
        }
    }
}
#[test]
fn sticky_cleanup_exhausts_full_arc_and_owned_error_string_fields_without_changing_first_cause() {
    // Adverse private State ownership, not a candidate layout/table interface.
    let shape = Arc::new(TyLayoutShape {
        size_bits: 7,
        align_bits: None,
        kind: TyLayoutKind::Struct {
            id: StructId::new(0),
            fields: vec![field()],
        },
    });
    let mut state = State {
        shape: Some(shape),
        error: Some(LayoutError::TargetScalarLayoutUnavailable {
            triple: "raw λ\0".repeat(1024),
        }),
        render: "pending".repeat(1024),
        reason: "whole reason".repeat(1024),
    };
    let mut o = Observer {
        stop: Some(1),
        cleanup_after: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(work.admit(1, 0).is_err());
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original slot-shape stop"
    );
    assert_eq!(
        work.publication_result(),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn full_semantic_reason_stays_owned_by_original_caller_until_explicit_consuming_cleanup() {
    let m = fixture();
    let (expected, _, _, _) = run(&m, &tuple(), false, None);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = setup(&m, &mut s);
    let out = slot_shape_observed(&table, &nominal, &tuple(), false, None, &mut s, site()).unwrap();
    assert_eq!(out, expected);
    let reason = out.unwrap_err();
    assert!(reason.capacity() > 0);
    let begin = calls.get();
    Work {
        session: &mut s,
        site: site(),
    }
    .flat(reason);
    let end = calls.get();
    dispose(table, nominal, &mut s);
    drop(s);
    assert!(end > begin);
    assert!(
        o.events[begin..end]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
