// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inspect(m: &Module, ty: &Ty, mut check: impl FnMut(&State<'_>, &ObservedAbiLanes<'_>)) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, mut lanes) = setup(m, &mut session);
    let begin = calls.get();
    let mut state = State::default();
    let mut w = Work {
        session: &mut session,
        site: site(),
    };
    state.run(&mut lanes, &table, ty, &mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut lanes, &mut w);
    empty(&state, &lanes);
    drop(w);
    drop(state);
    dispose(table, lanes, &mut session);
    drop(session);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, mut lanes) = setup(m, &mut session);
        let mut state = State::default();
        let mut w = Work {
            session: &mut session,
            site: site(),
        };
        assert_eq!(
            state.run(&mut lanes, &table, ty, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        check(&state, &lanes);
        drain(&mut state, &mut lanes, &mut w);
        empty(&state, &lanes);
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original ABI-lane stop"
        );
        drop(w);
        drop(state);
        dispose(table, lanes, &mut session);
    }
}
#[test]
fn full_scalar_layout_child_is_held_before_parent_size_read_and_retirement() {
    let m = module();
    let mut saw = false;
    inspect(&m, &Ty::Bool, |state, _| {
        if let Some(Ok(shape)) = &state.layout {
            saw = true;
            assert_eq!(shape.size_bytes(), Some(1));
        }
    });
    assert!(saw);
}
#[test]
fn uninhabited_direct_shape_and_sorted_ranges_are_held_until_same_session_cleanup() {
    let m = direct_storage_fixture(Ty::U32, 4, 4);
    let (mut shape, mut ranges) = (false, false);
    inspect(&m, &Ty::Enum(EnumId::new(0)), |state, _| {
        shape |= matches!(&state.enum_layout, Some(Ok(_)));
        ranges |= !state.ranges.is_empty();
    });
    assert!(shape && ranges);
}
#[test]
fn complete_owned_layout_error_is_held_until_actual_same_session_cleanup() {
    let mut m = module();
    m.target_info.as_mut().unwrap().triple = "unknown-target-尾".repeat(40);
    let mut saw = false;
    inspect(&m, &Ty::Bool, |state, _| {
        saw |= matches!(&state.layout, Some(Err(_)));
    });
    assert!(saw);
}
#[test]
fn full_borrowed_frames_and_open_nominal_memo_survive_interior_stop_before_full_drain() {
    let m = doubling(3);
    let (mut frames, mut open) = (false, false);
    inspect(&m, &s(3), |state, lanes| {
        frames |= !state.frames.is_empty();
        open |= lanes
            .nodes
            .iter()
            .any(|(_, slot)| matches!(slot, Slot::Open));
    });
    assert!(frames && open);
}
#[test]
fn initial_header_refusal_discards_all_previously_complete_cache_rows() {
    let mut m = module();
    m.structs.push(strukt(0, vec![Ty::Ptr]));
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        interrupt: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, mut lanes) = setup(&m, &mut session);
    assert_eq!(
        lanes
            .lanes_observed(&table, &s(0), &mut session, site())
            .unwrap(),
        Some(1)
    );
    assert!(!lanes.nodes.is_empty());
    arm.set(true);
    assert_eq!(
        lanes.lanes_observed(&table, &s(0), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(lanes.nodes.capacity(), 0);
    dispose(table, lanes, &mut session);
}
#[test]
fn different_source_module_is_typed_refusal_clears_cache_and_cannot_supply_a_count() {
    let mut m = module();
    m.structs.push(strukt(0, vec![Ty::Ptr]));
    let mut foreign = module();
    foreign.structs.push(strukt(0, vec![Ty::U64, Ty::Ptr]));
    let mut o = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, mut lanes) = setup(&m, &mut session);
    let other = LayoutTable::new_observed(&foreign, &mut session, site()).unwrap();
    assert_eq!(
        lanes
            .lanes_observed(&table, &s(0), &mut session, site())
            .unwrap(),
        Some(1)
    );
    assert_eq!(
        lanes.lanes_observed(&other, &s(0), &mut session, site()),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(lanes.nodes.capacity(), 0);
    assert!(session.first_refusal().is_none());
    session.retirement_step(site(), size_of::<LayoutTable<'_>>() + 1);
    drop(other);
    session.retirement_poll(site());
    dispose(table, lanes, &mut session);
}
#[test]
fn complete_memo_reuse_omits_rewalking_children_but_still_observes_original_owner() {
    let m = doubling(8);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, mut lanes) = setup(&m, &mut session);
    let a = calls.get();
    assert_eq!(
        lanes
            .lanes_observed(&table, &s(8), &mut session, site())
            .unwrap(),
        Some(256)
    );
    let b = calls.get();
    let n = lanes.nodes.len();
    assert_eq!(
        lanes
            .lanes_observed(&table, &s(8), &mut session, site())
            .unwrap(),
        Some(256)
    );
    let c = calls.get();
    assert_eq!(lanes.nodes.len(), n);
    assert!(c - b < b - a);
    dispose(table, lanes, &mut session);
}
#[test]
fn successful_whole_context_retirement_has_terminal_one_zero_or_original_sticky_cleanup() {
    let m = doubling(3);
    for refuse in [false, true] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            cleanup: Some(arm.clone()),
            ..Observer::default()
        };
        let calls = o.calls.clone();
        let trace = o.trace.clone();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, mut lanes) = setup(&m, &mut session);
        lanes
            .lanes_observed(&table, &s(3), &mut session, site())
            .unwrap();
        let begin = calls.get();
        arm.set(refuse);
        let result = lanes.retire_observed(&mut session, site());
        let end = calls.get();
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(session.first_refusal().unwrap().cause, "cleanup");
        } else {
            result.unwrap();
        }
        {
            let events = trace.borrow();
            let tail = &events[begin..end];
            if refuse {
                assert!(
                    tail.iter()
                        .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
                );
            } else {
                assert!(
                    tail[..tail.len() - 1]
                        .iter()
                        .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
                );
                let e = tail.last().unwrap();
                assert_eq!(
                    (e.phase, e.work, e.copy_bytes),
                    (ExecutionPhase::Publication, 1, 0)
                );
            }
        }
        session.retirement_step(site(), size_of::<LayoutTable<'_>>() + 1);
        drop(table);
        session.retirement_poll(site());
    }
}
