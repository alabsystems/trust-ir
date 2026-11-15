// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_compact_query_copy_rule_cleanup_and_publication_callback_refuses() {
    let m = fixtures::invalid();
    let (_, base) = run(&m, &[]);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_declared_struct_layouts_observed(&m, &[], &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original struct-layout stop"
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn original_work_and_copy_accumulate_across_complete_calls_without_fuel_reset() {
    let m = fixtures::invalid();
    let (_, base) = run(&m, &[]);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_module_declared_struct_layouts_observed(&m, &[], &mut s, site()).unwrap();
        assert_eq!(
            validate_module_declared_struct_layouts_observed(&m, &[], &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_declared_struct_layouts_observed(&m, &[], &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
fn snapshot_stop(m: &Module, ty: &Ty) -> usize {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.table = Some(LayoutTable::new_observed(m, work.session, work.site).unwrap());
    state.query(ty, &mut work).unwrap();
    drain(&mut state, &mut work);
    let pairs = o
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, p)| {
            p[0].phase == ExecutionPhase::Publication
                && p[0].work == 0
                && p[0].copy_bytes == 0
                && p[1].phase == ExecutionPhase::Validation
                && p[1].work == 5
                && p[1].copy_bytes == size_of::<Summary>()
        })
        .map(|(i, _)| i + 2)
        .collect::<Vec<_>>();
    assert_eq!(pairs.len(), 1);
    pairs[0]
}
#[test]
fn actual_returned_arc_and_owned_field_names_stay_retained_before_snapshot_admission() {
    let mut m = fixtures::valid();
    m.structs[0].fields[0].name = "owned-name".repeat(1000);
    let ty = Ty::Struct(StructId::new(0));
    let stop = snapshot_stop(&m, &ty);
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.table = Some(LayoutTable::new_observed(&m, work.session, work.site).unwrap());
    assert_eq!(
        state.query(&ty, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.error.is_none());
    let shape = state.shape.as_ref().unwrap();
    assert!(
        matches!(&shape.kind,trust_ir::shape::TyLayoutKind::Struct{fields,..} if fields[0].name==m.structs[0].fields[0].name)
    );
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original struct-layout stop"
    );
}
#[test]
fn actual_returned_owned_semantic_error_is_retained_before_snapshot_admission() {
    let mut m = fixtures::valid();
    m.target_info = Some(fixtures::target("custom-λ".repeat(1000)));
    let stop = snapshot_stop(&m, &Ty::U64);
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.table = Some(LayoutTable::new_observed(&m, work.session, work.site).unwrap());
    assert_eq!(
        state.query(&Ty::U64, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.shape.is_none());
    assert!(
        matches!(&state.error,Some(LayoutError::TargetScalarLayoutUnavailable{triple}) if triple==&m.target_info.as_ref().unwrap().triple)
    );
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn full_target_triple_survives_actual_output_reserve_and_header_refusals() {
    let mut m = fixtures::valid();
    m.target_info = Some(fixtures::target("custom-owned-λ".repeat(100)));
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &[], &mut work).unwrap();
    drain(&mut state, &mut work);
    let positions = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .take(2)
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(positions.len(), 2);
    for (n, stop) in positions.into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.run(&m, &[], &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.triple, m.target_info.as_ref().unwrap().triple);
        assert!(state.error.is_none());
        assert!(state.shape.is_none());
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn final_result_publication_refuses_only_after_all_owned_query_scratch_is_gone() {
    let m = fixtures::invalid();
    let (_, base) = run(&m, &[]);
    let stop = base.events.len();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_declared_struct_layouts_observed(&m, &[], &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(o.events.len() > stop);
    assert!(
        o.events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn cleanup_stop_consumes_table_arc_error_triple_indexes_ranges_and_complete_diagnostics() {
    let m = fixtures::valid();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &[], &mut work).unwrap();
    state.shape = Some(Arc::new(TyLayoutShape {
        size_bits: 0,
        align_bits: Some(8),
        kind: trust_ir::shape::TyLayoutKind::Tuple {
            fields: vec![trust_ir::shape::FieldOffsetShape {
                field: 0,
                name: "owned".repeat(1000),
                ty_shape: trust_ir::shape::TyShape::Unit,
                offset_bits: Some(0),
            }],
        },
    }));
    state.error = Some(LayoutError::TargetScalarLayoutUnavailable {
        triple: "error".repeat(1000),
    });
    state.triple = "pending".repeat(1000);
    state.ranges = vec![(0, 1); 10];
    state.reported = vec![0; 10];
    state.errors = vec![ValidationError::TargetScalarLayoutUnavailable {
        struct_id: 0,
        triple: "completed".repeat(1000),
    }];
    arm.set(true);
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn original_sticky_stop_and_initial_copy_refusal_admit_no_owned_state() {
    let m = fixtures::valid();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_declared_struct_layouts_observed(&m, &[], &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        validate_module_declared_struct_layouts_observed(&m, &[], &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(o.events.len(), 1);
}
