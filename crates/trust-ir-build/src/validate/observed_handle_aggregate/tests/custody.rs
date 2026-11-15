// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn full_discriminant_and_selected_child_vectors_are_held_until_parent_transfer_or_retirement() {
    let (m, f) = fixture();
    let inst = extract(handle(), 4, 1);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (values, nominal, guards) = setup(&m, &f, true, &mut s);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(
        state
            .run(
                &m,
                &inst,
                &values,
                &nominal,
                BlockId::new(17),
                guards.as_ref(),
                &mut work
            )
            .unwrap()
    );
    assert_eq!(state.discriminants, vec![0, 1]);
    assert_eq!(state.selected, vec![0]);
    assert!(state.discriminants.capacity() > 0 && state.selected.capacity() > 0);
    drain(&mut state, &mut work);
    assert!(empty(&state));
    dispose(values, nominal, guards, work.session);
}
#[test]
fn exact_tag_type_result_is_retained_and_explicitly_consumed_under_same_original_owner() {
    let (m, f) = fixture();
    let inst = extract(Ty::U8, 4, 0);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (values, nominal, guards) = setup(&m, &f, true, &mut s);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(
        state
            .run(
                &m,
                &inst,
                &values,
                &nominal,
                BlockId::new(17),
                guards.as_ref(),
                &mut work
            )
            .unwrap()
    );
    assert_eq!(state.tag_ty, Some(Ty::U8));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    dispose(values, nominal, guards, work.session);
}
#[test]
fn complete_returned_type_display_stays_owned_across_next_fallible_parent_copy() {
    let (m, f) = fixture();
    let inst = extract(Ty::U64, 2, 0);
    let complete = handle().to_string();
    let (_, _, _, end) = run(&m, &f, &inst, BlockId::new(17), true);
    let mut held = false;
    // Use identical private entry on baseline and interrupted paths.
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (values, nominal, guards) = setup(&m, &f, true, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(
        !state
            .run(
                &m,
                &inst,
                &values,
                &nominal,
                BlockId::new(17),
                guards.as_ref(),
                &mut work
            )
            .unwrap()
    );
    let finish = calls.get();
    assert!(end > finish);
    drain(&mut state, &mut work);
    dispose(values, nominal, guards, work.session);
    drop(work);
    drop(s);
    for cut in begin + 1..=finish {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (values, nominal, guards) = setup(&m, &f, true, &mut s);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let _ = state.run(
            &m,
            &inst,
            &values,
            &nominal,
            BlockId::new(17),
            guards.as_ref(),
            &mut work,
        );
        if state.render == complete {
            held = true;
            assert!(state.render.capacity() > 0);
            assert!(state.reason.contains(" is `"));
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
        dispose(values, nominal, guards, work.session);
    }
    assert!(held);
}
#[test]
fn every_private_tag_guard_and_reason_cut_exhausts_all_actual_owned_fields() {
    let (m, f) = fixture();
    for inst in [extract(Ty::U64, 4, 0), extract(Ty::U64, 4, 1)] {
        let mut baseline = Observer::default();
        let calls = baseline.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        let (values, nominal, guards) = setup(&m, &f, true, &mut s);
        let begin = calls.get();
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert!(
            !state
                .run(
                    &m,
                    &inst,
                    &values,
                    &nominal,
                    BlockId::new(17),
                    guards.as_ref(),
                    &mut work
                )
                .unwrap()
        );
        let end = calls.get();
        drain(&mut state, &mut work);
        dispose(values, nominal, guards, work.session);
        drop(work);
        drop(s);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (values, nominal, guards) = setup(&m, &f, true, &mut s);
            let mut state = State::default();
            let mut work = Work {
                session: &mut s,
                site: site(),
            };
            assert!(
                state
                    .run(
                        &m,
                        &inst,
                        &values,
                        &nominal,
                        BlockId::new(17),
                        guards.as_ref(),
                        &mut work
                    )
                    .is_err()
            );
            drain(&mut state, &mut work);
            assert!(empty(&state));
            assert_eq!(
                work.session.first_refusal().unwrap().cause,
                "original aggregate stop"
            );
            dispose(values, nominal, guards, work.session);
        }
    }
}
#[test]
fn sticky_full_child_and_reason_retirement_continues_after_late_cleanup_refusal() {
    let (m, f) = fixture();
    let inst = extract(Ty::U64, 4, 1);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (values, nominal, guards) = setup(&m, &f, true, &mut s);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(
        !state
            .run(
                &m,
                &inst,
                &values,
                &nominal,
                BlockId::new(17),
                guards.as_ref(),
                &mut work
            )
            .unwrap()
    );
    let end = calls.get();
    drain(&mut state, &mut work);
    dispose(values, nominal, guards, work.session);
    drop(work);
    drop(s);
    let mut o = Observer {
        stop: Some(end + 1),
        cleanup_after: Some(end + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (values, nominal, guards) = setup(&m, &f, true, &mut s);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(
        !state
            .run(
                &m,
                &inst,
                &values,
                &nominal,
                BlockId::new(17),
                guards.as_ref(),
                &mut work
            )
            .unwrap()
    );
    assert_eq!(state.discriminants, vec![0, 1]);
    assert_eq!(state.selected, vec![0]);
    assert!(!state.reason.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
    dispose(values, nominal, guards, work.session);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original aggregate stop"
    );
    drop(work);
    drop(s);
    assert!(
        o.events[end + 1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn complete_semantic_reason_is_owned_by_original_caller_until_explicit_field_retirement() {
    let (m, f) = fixture();
    let inst = extract(Ty::U64, 4, 1);
    let (expected, _, _, _) = run(&m, &f, &inst, BlockId::new(17), true);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (values, nominal, guards) = setup(&m, &f, true, &mut s);
    let out = handle_aggregate_lane_rule_observed(
        &m,
        &inst,
        &values,
        &nominal,
        BlockId::new(17),
        guards.as_ref(),
        &mut s,
        site(),
    )
    .unwrap();
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
    dispose(values, nominal, guards, &mut s);
    drop(s);
    assert!(end > begin);
    assert!(
        o.events[begin..end]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
