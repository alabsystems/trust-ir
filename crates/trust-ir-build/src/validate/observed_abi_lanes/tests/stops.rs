// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module, ty: &Ty) {
    let (_, baseline, begin, end) = run(m, ty);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, mut lanes) = setup(m, &mut session);
        assert_eq!(
            lanes.lanes_observed(&table, ty, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(lanes.nodes.capacity(), 0);
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original ABI-lane stop"
        );
        dispose(table, lanes, &mut session);
        drop(session);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_actual_nominal_lookup_frame_memo_child_sum_and_publication_callback_refuses() {
    let mut m = module();
    m.structs.push(strukt(0, vec![Ty::U64, Ty::Ptr]));
    every(&m, &s(0));
}
#[test]
fn every_actual_empty_variant_and_niche_order_transition_refuses() {
    let mut m = module();
    m.enums.push(enum_def(
        0,
        vec![vec![], vec![Ty::Unit], vec![Ty::U64, Ty::Ptr]],
        Some(niche(2)),
    ));
    every(&m, &Ty::Enum(EnumId::new(0)));
}
#[test]
fn repeated_cached_queries_keep_original_cumulative_work_and_copy_budget() {
    let mut m = module();
    m.structs.push(strukt(0, vec![Ty::U64, Ty::Ptr]));
    let ty = s(0);
    let (_, base, _, end) = run(&m, &ty);
    for copy in [false, true] {
        let cap = base.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer {
            work_cap: (!copy).then_some(cap),
            byte_cap: copy.then_some(cap),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, mut lanes) = setup(&m, &mut session);
        assert_eq!(
            lanes
                .lanes_observed(&table, &ty, &mut session, site())
                .unwrap(),
            Some(2)
        );
        assert_eq!(
            lanes.lanes_observed(&table, &ty, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(lanes.nodes.capacity(), 0);
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        dispose(table, lanes, &mut session);
    }
}
#[test]
fn original_zero_fuel_and_sticky_interrupt_never_become_semantic_no_lanes() {
    let m = module();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        interrupt: Some(arm.clone()),
        ..Observer::default()
    };
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut session = ObservedSession::new(options, &mut o);
    let (table, mut lanes) = setup(&m, &mut session);
    assert_eq!(
        lanes
            .lanes_observed(&table, &Ty::Ptr, &mut session, site())
            .unwrap(),
        Some(1)
    );
    assert_eq!(session.remaining_fuel(), 0);
    arm.set(true);
    assert!(
        session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: site(),
                work: 1,
                copy_bytes: 0
            })
            .is_err()
    );
    assert_eq!(
        lanes.lanes_observed(&table, &Ty::Ptr, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interrupt");
    dispose(table, lanes, &mut session);
}
