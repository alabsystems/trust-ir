// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn cases() -> Vec<(Inst, BlockId, bool)> {
    vec![
        (make(tuple(), None, &[0, 1]), BlockId::new(17), true),
        (make(tuple(), None, &[1, 1]), BlockId::new(17), true),
        (extract(Ty::U8, 4, 0), BlockId::new(17), true),
        (extract(Ty::U64, 4, 0), BlockId::new(17), true),
        (extract(handle(), 4, 1), BlockId::new(17), true),
        (extract(handle(), 4, 1), BlockId::new(18), true),
        (extract(handle(), 4, 1), BlockId::new(17), false),
        (insert(tuple(), 2, 0, 0), BlockId::new(17), true),
        (insert(tuple(), 2, 0, 1), BlockId::new(17), true),
        (Inst::NullPtr, BlockId::new(17), true),
    ]
}
#[test]
fn every_actual_inner_lookup_nominal_type_equality_tag_guard_copy_retirement_and_publication_cut_refuses()
 {
    let (m, f) = fixture();
    for (inst, block, guard) in cases() {
        let (_, baseline, begin, end) = run(&m, &f, &inst, block, guard);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (values, nominal, guards) = setup(&m, &f, guard, &mut s);
            assert_eq!(
                handle_aggregate_lane_rule_observed(
                    &m,
                    &inst,
                    &values,
                    &nominal,
                    block,
                    guards.as_ref(),
                    &mut s,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "original aggregate stop");
            dispose(values, nominal, guards, &mut s);
            drop(s);
            assert_eq!(&o.events[..cut], &baseline.events[..cut]);
            assert!(
                o.events[cut..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_work_and_copy_repeated_semantic_success_and_refusal_share_the_original_account() {
    let (m, f) = fixture();
    for inst in [extract(handle(), 4, 1), extract(Ty::U64, 4, 1)] {
        let (_, baseline, _, end) = run(&m, &f, &inst, BlockId::new(17), true);
        for copy in [false, true] {
            let limit = baseline.events[..end]
                .iter()
                .map(|e| if copy { e.copy_bytes } else { e.work })
                .sum::<usize>();
            let mut o = Observer::default();
            if copy {
                o.byte_cap = Some(limit)
            } else {
                o.work_cap = Some(limit)
            }
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
            assert_eq!(
                handle_aggregate_lane_rule_observed(
                    &m,
                    &inst,
                    &values,
                    &nominal,
                    BlockId::new(17),
                    guards.as_ref(),
                    &mut s,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            dispose_reason(out, &mut s);
            dispose(values, nominal, guards, &mut s);
        }
    }
}
#[test]
fn interior_declared_definition_fallback_refusal_is_typed_not_missing_carrier() {
    let (mut m, f) = fixture();
    let mut rows = vec![];
    for id in 0..128 {
        let mut def = m.structs[0].clone();
        def.id = StructId::new(id + 1);
        rows.push(def);
    }
    rows.push(m.structs[0].clone());
    m.structs = rows;
    let inst = make(Ty::Struct(StructId::new(0)), None, &[0, 1]);
    let (_, baseline, begin, end) = run(&m, &f, &inst, BlockId::new(17), true);
    assert!(end > begin + 128);
    let cut = begin + 64;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (values, nominal, guards) = setup(&m, &f, true, &mut s);
    assert_eq!(
        handle_aggregate_lane_rule_observed(
            &m,
            &inst,
            &values,
            &nominal,
            BlockId::new(17),
            guards.as_ref(),
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    dispose(values, nominal, guards, &mut s);
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
}
#[test]
fn stopped_guard_query_never_becomes_empty_selected_or_ordinary_missing_guard_diagnostic() {
    let (m, f) = fixture();
    let inst = extract(handle(), 4, 1);
    let (_, baseline, begin, end) = run(&m, &f, &inst, BlockId::new(17), true);
    // All actual callback cuts include canonical/discriminant and guard interiors;
    // every cut must be operational, including the full successful result edge.
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (values, nominal, guards) = setup(&m, &f, true, &mut s);
        assert!(matches!(
            handle_aggregate_lane_rule_observed(
                &m,
                &inst,
                &values,
                &nominal,
                BlockId::new(17),
                guards.as_ref(),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        ));
        dispose(values, nominal, guards, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
}
#[test]
fn preexisting_original_stop_and_zero_instruction_fuel_are_not_recaptured_or_renewed() {
    let (m, f) = fixture();
    let inst = extract(handle(), 4, 1);
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
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
    assert_eq!(out, Ok(()));
    assert_eq!(s.remaining_fuel(), 0);
    dispose_reason(out, &mut s);
    dispose(values, nominal, guards, &mut s);
    drop(s);
    let (_, _, begin, _) = run(&m, &f, &inst, BlockId::new(17), true);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (values, nominal, guards) = setup(&m, &f, true, &mut s);
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
        handle_aggregate_lane_rule_observed(
            &m,
            &inst,
            &values,
            &nominal,
            BlockId::new(17),
            guards.as_ref(),
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original aggregate stop");
    dispose(values, nominal, guards, &mut s);
}
#[test]
fn first_normal_cause_survives_all_following_retirement_refusals_without_partial_publication() {
    let (m, f) = fixture();
    let inst = extract(Ty::U64, 4, 1);
    let (_, _, begin, end) = run(&m, &f, &inst, BlockId::new(17), true);
    let cut = begin + (end - begin) / 2;
    let mut o = Observer {
        stop: Some(cut),
        cleanup_after: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (values, nominal, guards) = setup(&m, &f, true, &mut s);
    assert_eq!(
        handle_aggregate_lane_rule_observed(
            &m,
            &inst,
            &values,
            &nominal,
            BlockId::new(17),
            guards.as_ref(),
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    dispose(values, nominal, guards, &mut s);
    assert_eq!(s.first_refusal().unwrap().cause, "original aggregate stop");
    drop(s);
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
