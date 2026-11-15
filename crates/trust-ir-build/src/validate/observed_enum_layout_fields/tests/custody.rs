// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

fn snapshot_stop(m: &Module, ty: &Ty) -> usize {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.table = Some(LayoutTable::new_observed(m, work.session, work.site).unwrap());
    state.query(ty, &mut work).unwrap();
    drain(&mut state, &mut work);
    assert!(empty(&state));
    let positions: Vec<_> = observer
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Publication
                && pair[0].work == 0
                && pair[0].copy_bytes == 0
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 6
                && pair[1].copy_bytes == size_of::<Summary>()
        })
        .map(|(i, _)| i + 2)
        .collect();
    assert_eq!(positions.len(), 1);
    positions[0]
}
#[test]
fn complete_returned_arc_and_owned_field_name_precede_summary_admission() {
    let mut m = Module::new("owned-result");
    let name = "field-λ-tail".repeat(500);
    m.structs = vec![strukt(
        0,
        Some(8),
        Some(8),
        vec![FieldDef {
            name: name.clone(),
            ty: Ty::U64,
            offset: Some(0),
        }],
    )];
    let ty = Ty::Struct(StructId::new(0));
    let stop = snapshot_stop(&m, &ty);
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    // Identical new-table -> private query entry as the baseline.
    state.table = Some(LayoutTable::new_observed(&m, work.session, work.site).unwrap());
    assert_eq!(
        state.query(&ty, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.error.is_none());
    assert!(
        matches!(&state.shape.as_ref().unwrap().kind,trust_ir::shape::TyLayoutKind::Struct{fields,..} if fields[0].name==name)
    );
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original field stop"
    );
}
#[test]
fn complete_owned_semantic_error_precedes_summary_admission() {
    let mut m = Module::new("owned-error");
    m.target_info = Some(target("custom-λ".repeat(500)));
    let stop = snapshot_stop(&m, &Ty::U64);
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
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
fn formatted_error_reason_is_retained_immediately_before_bounds_work() {
    let (mut m, mut e, mut d) = compact();
    m.target_info = Some(target("custom-owned-λ".repeat(300)));
    e.variants[0].fields[0] = Ty::U64;
    d.variant_field_offsets[0][0] = 0;
    let base = private_trace(&m, &e, &d);
    let positions: Vec<_> = base
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Publication
                && pair[0].work == 1
                && pair[0].copy_bytes == size_of::<String>()
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 3
                && pair[1].copy_bytes == size_of::<Option<u64>>()
        })
        .map(|(i, _)| i + 2)
        .collect();
    assert_eq!(positions.len(), 1);
    let stop = positions[0];
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&m, &e, &d, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        state.reason.as_deref(),
        Some(state.error.as_ref().unwrap().to_string().as_str())
    );
    assert!(state.tytext.is_none());
    assert_eq!(state.expected.capacity(), 0);
    assert_eq!(state.actual.capacity(), 0);
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn complete_type_display_is_retained_before_the_first_following_actual_text_copy() {
    let (m, mut e, mut d) = compact();
    e.variants[0].fields[0] = Ty::Tuple(vec![Ty::U64; 400]);
    d.variant_field_offsets[0][0] = 0;
    let base = private_trace(&m, &e, &d);
    let positions: Vec<_> = base
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Publication
                && pair[0].work == 1
                && pair[0].copy_bytes == size_of::<String>()
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 1
                && pair[1].copy_bytes == 0
        })
        .map(|(i, _)| i + 2)
        .collect();
    assert_eq!(positions.len(), 1);
    let stop = positions[0];
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&m, &e, &d, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        state.tytext.as_deref(),
        Some(e.variants[0].fields[0].to_string().as_str())
    );
    assert!(state.reason.is_some() && state.error.is_some());
    assert!(state.expected.ends_with("size 0)"));
    assert_eq!(state.actual.capacity(), 0);
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn all_three_pending_strings_survive_distinct_output_growth_and_header_admissions() {
    let (m, e, d) = compact();
    let base = private_trace(&m, &e, &d);
    let positions: Vec<_> = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .map(|(i, _)| i + 1)
        .collect();
    assert!(positions.len() >= 2);
    assert_eq!(positions[1], positions[0] + 1);
    for (n, stop) in positions.into_iter().take(2).enumerate() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.run(&m, &e, &d, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.location, "enum.7 (Eλ) layout");
        assert_eq!(state.expected, "variant 0 field 0 entirely within size 0");
        assert_eq!(state.actual, "offset 1, field size 1");
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        assert!(state.shape.is_some());
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn completed_prefix_and_new_pending_strings_stay_owned_at_later_output_move() {
    let (m, e, d) = compact();
    let base = private_trace(&m, &e, &d);
    let positions: Vec<_> = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .map(|(i, _)| i + 1)
        .collect();
    // First growth/header precede the first push; the final such admission is
    // the second push header (its possible growth costs >=3 row images).
    assert_eq!(positions.len(), 3);
    let stop = positions[2];
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&m, &e, &d, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors.len(), 1);
    assert_eq!(state.errors[0], original::run(&m, &e, &d)[0]);
    assert_eq!(
        state.expected,
        "descriptor align at least variant 0 field 0 alignment 1"
    );
    assert_eq!(state.actual, "align 0");
    assert_eq!(state.location, "enum.7 (Eλ) layout");
    assert!(state.shape.is_some());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn long_raw_location_name_copy_can_stop_interior_with_partial_prefix_retained() {
    let e = EnumDef::new(EnumId::new(7), "x".repeat(3000) + "λTAIL", vec![]);
    let trace = |stop: Option<usize>| {
        let mut observer = Observer {
            stop,
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State {
            expected: "pending expected".into(),
            actual: "pending actual".into(),
            ..State::default()
        };
        let result = state.push(&e, &mut work);
        if stop.is_some() {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(state.location, "enum.7 (".to_owned() + &"x".repeat(1024));
            assert_eq!(state.expected, "pending expected");
            assert_eq!(state.actual, "pending actual");
        } else {
            result.unwrap();
            assert_eq!(state.errors.len(), 1);
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
        observer
    };
    let base = trace(None);
    let copies: Vec<_> = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(copies.len(), 2);
    trace(Some(copies[1]));
    // The borrowed enum was never consumed or rewritten by either path.
    assert!(e.name.ends_with("λTAIL"));
}
#[test]
fn sticky_retirement_consumes_every_owned_query_text_range_and_diagnostic_payload() {
    let (m, e, d) = compact();
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &e, &d, &mut work).unwrap();
    state.shape = Some(Arc::new(TyLayoutShape {
        size_bits: 0,
        align_bits: Some(8),
        kind: trust_ir::shape::TyLayoutKind::Tuple {
            fields: vec![trust_ir::shape::FieldOffsetShape {
                field: 0,
                name: "shape".repeat(1000),
                ty_shape: trust_ir::shape::TyShape::Unit,
                offset_bits: Some(0),
            }],
        },
    }));
    state.error = Some(LayoutError::TargetScalarLayoutUnavailable {
        triple: "owned triple".repeat(1000),
    });
    state.reason = Some("reason".repeat(1000));
    state.tytext = Some("type text".repeat(1000));
    state.location = "pending location".repeat(1000);
    state.expected = "pending expected".repeat(1000);
    state.actual = "pending actual".repeat(1000);
    state.ranges = vec![(0, 1, 2); 20];
    arm.set(true);
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original cleanup stop"
    );
    let first = work.session.first_refusal().unwrap().progress;
    assert_eq!(
        work.publication(1, size_of::<Vec<ValidationError>>()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(work.session.first_refusal().unwrap().progress, first);
    assert!(
        observer
            .events
            .iter()
            .rev()
            .take_while(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .count()
            > 20
    );
}
