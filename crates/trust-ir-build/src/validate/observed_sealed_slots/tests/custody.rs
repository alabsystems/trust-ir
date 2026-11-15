// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn prepare<'m, O: ExecutionObserver>(
    m: &'m Module,
    s: &mut ObservedSession<'_, O>,
) -> (
    trust_ir::LayoutTable<'m>,
    trust_ir::ObservedNominalTypeReachability<'m>,
) {
    (
        trust_ir::LayoutTable::new_observed(m, s, site()).unwrap(),
        m.nominal_type_reachability_observed(s, site()).unwrap(),
    )
}
fn release<O: ExecutionObserver>(
    table: trust_ir::LayoutTable<'_>,
    nominal: trust_ir::ObservedNominalTypeReachability<'_>,
    s: &mut ObservedSession<'_, O>,
) {
    let _ = nominal.retire_observed(s, site());
    s.retirement_step(site(), size_of::<trust_ir::LayoutTable<'_>>() + 1);
    drop(table);
    s.retirement_poll(site());
}
#[test]
fn every_private_build_cut_preserves_same_entry_prefix_and_drains_all_owned_fields() {
    let (m, mut f) = fixture();
    f.blocks[0].body.insert(
        1,
        InstrNode::new(Inst::Copy {
            ty: Ty::Ptr,
            operand: v(10),
        })
        .with_result(v(11)),
    );
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal) = prepare(&m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .build(
            &table,
            &f,
            &nominal,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        )
        .unwrap();
    let end = calls.get();
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    assert!(empty(&state));
    release(table, nominal, &mut s);
    drop(s);
    let mut retained_partial = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal) = prepare(&m, &mut s);
        let mut state = State::default();
        assert_eq!(
            state.build(
                &table,
                &f,
                &nominal,
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        retained_partial |= state.operands.capacity() != 0
            || state.unsealing.capacity() != 0
            || state.reason.capacity() != 0
            || state.render.capacity() != 0;
        drain(
            &mut state,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        );
        assert!(empty(&state));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original sealed analysis stop"
        );
        release(table, nominal, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(retained_partial);
}
#[test]
fn pending_full_type_shape_reason_and_slot_remain_owned_before_fallible_map_transfer() {
    let (m, mut f) = fixture();
    f.blocks[0].body = vec![
        allocation(handle(), Some(v(0)), None, 10),
        allocation(handle(), Some(v(0)), None, 10),
    ];
    let ordinary = trust_ir::LayoutTable::new(&m);
    let old_nominal = m.nominal_type_reachability();
    let reason = super::super::super::handle_slots::slot_shape_test_oracle(
        &ordinary,
        &old_nominal,
        &handle(),
        true,
        None,
    )
    .unwrap_err();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal) = prepare(&m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .allocations(
            &table,
            &f,
            &nominal,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        )
        .unwrap();
    let end = calls.get();
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    release(table, nominal, &mut s);
    drop(s);
    let (mut saw_type, mut saw_reason, mut saw_slot) = (false, false, false);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal) = prepare(&m, &mut s);
        let mut state = State::default();
        assert_eq!(
            state.allocations(
                &table,
                &f,
                &nominal,
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        if let Some(ty) = &state.pending_type {
            assert_eq!(*ty, handle());
            saw_type = true;
        }
        if let Some(text) = &state.pending_unsealed {
            assert_eq!(text, &reason);
            saw_reason = true;
        }
        if let Some(slot) = &state.pending_slot {
            assert_eq!(slot.ty, handle());
            assert_eq!(slot.unsealed.as_ref(), Some(&reason));
            assert_eq!(slot.natural_align, None);
            assert!(slot.stores.is_empty());
            saw_slot = true;
        }
        drain(
            &mut state,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        );
        assert!(empty(&state));
        release(table, nominal, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
    assert!(saw_type && saw_reason && saw_slot);
}
#[test]
fn replaced_and_pending_slots_all_own_complete_nested_payloads_during_sticky_cleanup() {
    let owned = || Slot {
        ty: Ty::Tuple(vec![handle(), Ty::Bool]),
        site: (BlockId::new(7), 9),
        natural_align: Some(8),
        unsealed: Some("complete λ reason".repeat(1000)),
        stores: vec![(BlockId::new(7), 11); 17],
    };
    let mut state = State {
        old_slot: Some(owned()),
        pending_slot: Some(owned()),
        pending_type: Some(Ty::Tuple(vec![handle()])),
        pending_unsealed: Some("whole pending".repeat(100)),
        pending_natural: Some(8),
        operands: vec![v(10); 9],
        multiply_defined: vec![(10, 10); 4],
        unsealing: vec![(10, "queued".repeat(400))],
        reason: "partial λ".repeat(300),
        render: "render λ".repeat(300),
        ..State::default()
    };
    state.slots.insert(10, owned());
    state.members.insert(10, (10, (BlockId::new(7), 9)));
    state.definitions.insert(10, 2);
    let mut o = Observer {
        stop: Some(1),
        cleanup_after: Some(1),
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
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    assert!(empty(&state));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original sealed analysis stop"
    );
    drop(s);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn owned_copy_rows_are_consumed_and_capacity_retired_even_after_first_refusal() {
    let mut rows = Vec::<Point>::with_capacity(33);
    rows.extend([(BlockId::new(1), 2), (BlockId::new(3), 4)]);
    let capacity = rows.capacity();
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    work.rows(rows);
    drop(work);
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original sealed analysis stop"
    );
    drop(s);
    assert!(
        o.events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(
        o.events
            .iter()
            .any(|e| e.work >= capacity * size_of::<Point>() + size_of::<Vec<Point>>())
    );
}
#[test]
fn every_whole_analysis_retirement_callback_refuses_after_full_child_and_map_drain() {
    let (m, f) = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal) = prepare(&m, &mut s);
    let a = ObservedSealedHandleSlots::new_observed(&table, &f, &nominal, &mut s, site()).unwrap();
    let begin = calls.get();
    a.retire_observed(&mut s, site()).unwrap();
    let end = calls.get();
    release(table, nominal, &mut s);
    drop(s);
    assert!(
        baseline.events[begin..end]
            .iter()
            .any(|e| e.phase == ExecutionPhase::Publication && e.work == 1 && e.copy_bytes == 0)
    );
    assert_eq!(
        baseline.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal) = prepare(&m, &mut s);
        let a =
            ObservedSealedHandleSlots::new_observed(&table, &f, &nominal, &mut s, site()).unwrap();
        assert_eq!(
            a.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        release(table, nominal, &mut s);
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
fn per_node_queued_reasons_keep_source_order_and_discard_later_reason_explicitly() {
    let mut state = State::default();
    state.slots.insert(
        10,
        Slot {
            ty: handle(),
            site: (BlockId::new(1), 0),
            natural_align: Some(8),
            unsealed: None,
            stores: vec![],
        },
    );
    state.unsealing = vec![(10, "first λ".into()), (10, "second".repeat(2000))];
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    state
        .apply_unsealing(&mut Work {
            session: &mut s,
            site: site(),
        })
        .unwrap();
    assert_eq!(state.slots[&10].unsealed.as_deref(), Some("first λ"));
    assert!(state.reason.is_empty());
    assert_eq!(state.reason.capacity(), 0);
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    assert!(empty(&state));
    assert!(s.first_refusal().is_none());
}
#[test]
fn final_full_analysis_publication_refusal_consumes_return_owner_instead_of_publishing_subset() {
    let (m, f) = fixture();
    let (baseline, _, end) = run(&m, &f);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = prepare(&m, &mut s);
    assert!(matches!(
        ObservedSealedHandleSlots::new_observed(&table, &f, &nominal, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    release(table, nominal, &mut s);
    drop(s);
    assert_eq!(&o.events[..end], &baseline.events[..end]);
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
