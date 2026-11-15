// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_public_stage_callback_preserves_original_refusal_and_cleans_before_escape() {
    let mut m = fixture(EnumTagRepr::U8);
    m.enums[0].variants.push(variant("unencoded", vec![]));
    for stage in [Stage::Prelude, Stage::Encoding] {
        let (_, base) = run(&m, stage);
        let (_, align) = original::prelude(&m, &m.enums[0], m.enums[0].layout.as_ref().unwrap());
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Default::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                call(&m, stage, align, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original enum encoding stop"
            );
            assert!(
                o.events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn independent_cumulative_work_and_copy_limits_are_not_reset_by_stage_calls() {
    let m = fixture(EnumTagRepr::U8);
    for stage in [Stage::Prelude, Stage::Encoding] {
        let (_, base) = run(&m, stage);
        let (_, align) = original::prelude(&m, &m.enums[0], m.enums[0].layout.as_ref().unwrap());
        for bytes in [false, true] {
            let mut o = Observer {
                work_cap: (!bytes).then_some(base.work),
                byte_cap: bytes.then_some(base.bytes),
                ..Default::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            call(&m, stage, align, &mut s).unwrap();
            assert_eq!(
                call(&m, stage, align, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            let first = s.first_refusal().unwrap().progress;
            assert_eq!(
                call(&m, stage, align, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, first);
            assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
        }
    }
}
#[test]
fn returned_arc_and_semantic_error_stay_owned_before_the_actual_query_snapshot() {
    for off in [false, true] {
        let mut m = fixture(EnumTagRepr::U128);
        if off {
            m.target_info = Some(target("unsupported"));
        }
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        state.table = Some(LayoutTable::new_observed(&m, work.session, work.site).unwrap());
        state.query(&Ty::U128, &mut work).unwrap();
        drain(&mut state, &mut work);
        let stop = o
            .events
            .iter()
            .rposition(|e| {
                e.phase == ExecutionPhase::Validation
                    && e.work == 5
                    && e.copy_bytes == size_of::<Summary>()
            })
            .unwrap()
            + 1;
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        state.table = Some(LayoutTable::new_observed(&m, work.session, work.site).unwrap());
        assert_eq!(
            state.query(&Ty::U128, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.shape.is_some(), !off);
        assert_eq!(state.error.is_some(), off);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn target_triple_survives_original_prelude_output_reserve_and_header_move() {
    let mut m = fixture(EnumTagRepr::U128);
    m.target_info = Some(target("unsupported-λ-tail"));
    let e = &m.enums[0];
    let l = e.layout.as_ref().unwrap();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.prelude(&m, e, l, &mut work).unwrap();
    drain(&mut state, &mut work);
    let cuts = o
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && [
                    size_of::<ValidationError>(),
                    size_of::<ValidationError>() + size_of::<u32>(),
                ]
                .contains(&e.copy_bytes)
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(cuts.len(), 2);
    for (n, stop) in cuts.into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.prelude(&m, e, l, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.triple, "unsupported-λ-tail");
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn pending_full_encoding_diagnostic_survives_distinct_output_reserve_and_move() {
    let mut m = fixture(EnumTagRepr::U8);
    m.enums[0].variants.push(variant("unencodedλ", vec![]));
    let base = private_trace(&m);
    let cuts = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(cuts.len(), 2);
    for (n, stop) in cuts.into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        state.table = Some(LayoutTable::new_observed(&m, work.session, work.site).unwrap());
        assert_eq!(
            raw(
                &mut state,
                &m.enums[0],
                m.enums[0].layout.as_ref().unwrap(),
                Some(1),
                &mut work
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.location, "enum.9 (Eλ) layout");
        assert!(state.expected.contains("cover every inhabited variant"));
        assert!(state.actual.contains("unencodedλ"));
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn actual_inhabitedness_work_can_refuse_inside_coverage_without_publishing_diagnostics() {
    let mut m = fixture(EnumTagRepr::U8);
    m.enums[0]
        .variants
        .push(variant("unencoded", vec![Ty::Tuple(vec![Ty::Unit; 100])]));
    let table_events = {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let table = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
        drop(table);
        o.events.len()
    };
    let base = private_trace(&m);
    // After the identical table constructor, the first Layout-phase work is
    // the actual unencoded-variant inhabitedness walk, before field queries.
    let stop = base
        .events
        .iter()
        .enumerate()
        .skip(table_events)
        .filter(|(_, e)| e.phase == ExecutionPhase::Layout)
        .nth(10)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.table = Some(LayoutTable::new_observed(&m, work.session, work.site).unwrap());
    assert_eq!(
        raw(
            &mut state,
            &m.enums[0],
            m.enums[0].layout.as_ref().unwrap(),
            Some(1),
            &mut work
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.errors.is_empty());
    assert_eq!(
        work.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn sticky_cleanup_refusal_still_drains_arc_error_full_text_and_completed_diagnostics() {
    let m = fixture(EnumTagRepr::U8);
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.table = Some(LayoutTable::new_observed(&m, work.session, work.site).unwrap());
    state.shape = Some(
        state
            .table
            .as_ref()
            .unwrap()
            .ty_layout_observed(&Ty::U8, work.session, work.site)
            .unwrap()
            .unwrap(),
    );
    state.error = Some(LayoutError::TargetScalarLayoutUnavailable {
        triple: "error".repeat(1000),
    });
    state.location = "pending".repeat(1000);
    state.why = "why".repeat(1000);
    state.errors.push(ValidationError::ConstTypeMismatch {
        location: "old".into(),
        expected: "e".repeat(1000),
        actual: "a".repeat(1000),
    });
    arm.set(true);
    assert_eq!(
        state.finish(Ok(()), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn invalid_private_zero_alignment_is_refused_before_any_modulo_operation() {
    let m = fixture(EnumTagRepr::U8);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        call(&m, Stage::Encoding, Some(0), &mut s),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(s.first_refusal().is_none());
}
#[test]
fn supplied_instruction_site_and_zero_fuel_remain_original_for_both_stages() {
    let m = fixture(EnumTagRepr::U8);
    let exact = ExecutionSite::Instruction(trust_ir::interpret::InstructionSite {
        function: FuncId::new(4),
        block: BlockId::new(2),
        instruction_index: 7,
    });
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..Default::default()
        },
        &mut o,
    );
    let (pre, align) = validate_enum_layout_prelude_observed(
        &m,
        &m.enums[0],
        m.enums[0].layout.as_ref().unwrap(),
        &mut s,
        exact,
    )
    .unwrap();
    assert!(pre.is_empty());
    assert!(
        validate_enum_layout_encoding_observed(
            &m,
            &m.enums[0],
            m.enums[0].layout.as_ref().unwrap(),
            align,
            &mut s,
            exact
        )
        .unwrap()
        .is_empty()
    );
    assert_eq!(s.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}

#[test]
fn preexisting_stop_refuses_both_stages_without_reading_new_inputs_or_replacing_cause() {
    let m = fixture(EnumTagRepr::U8);
    let mut o = Observer {
        stop: Some(1),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 9,
        copy_bytes: 0,
    };
    assert!(s.admit(first).is_err());
    for stage in [Stage::Prelude, Stage::Encoding] {
        assert_eq!(
            call(&m, stage, Some(1), &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
    }
    assert_eq!(o.events, vec![first]);
}
