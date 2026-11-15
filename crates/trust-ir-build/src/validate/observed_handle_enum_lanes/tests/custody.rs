// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

// EL1: a tuple layout exists only when its exact type, descriptor and target
// are declared. Keep the other parity fixtures unchanged.
fn complete_layout_fixture() -> Module {
    let mut m = fixture();
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    m.types.push(Ty::Tuple(vec![handle(), Ty::Bool]));
    m.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type: TyId::new(0),
        size: 16,
        align: 8,
        field_offsets: vec![0, 8],
    });
    m
}
fn complete_tuple_shape() -> TyLayoutShape {
    use trust_ir::shape::{FieldOffsetShape, TyLayoutKind, TyShape};
    TyLayoutShape {
        size_bits: 128,
        align_bits: Some(64),
        kind: TyLayoutKind::Tuple {
            fields: vec![
                FieldOffsetShape {
                    field: 0,
                    name: "0".into(),
                    ty_shape: TyShape::Handle,
                    offset_bits: Some(0),
                },
                FieldOffsetShape {
                    field: 1,
                    name: "1".into(),
                    ty_shape: TyShape::Bool,
                    offset_bits: Some(64),
                },
            ],
        },
    }
}
#[test]
fn complete_returned_shape_stays_owned_before_summary_fee_and_all_retirement_cuts() {
    let m = complete_layout_fixture();
    let ty = Ty::Tuple(vec![handle(), Ty::Bool]);
    let old = LayoutTable::new(&m);
    let expected_shape = old.ty_layout(&ty).unwrap();
    assert_eq!(expected_shape.as_ref(), &complete_tuple_shape());
    let expected = expected_shape.size_bytes();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal) = setup(&m, &mut s);
    let begin = calls.get();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(state.size(&table, &ty, &mut work).unwrap(), expected);
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    dispose(table, nominal, &mut s);
    drop(s);
    let mut pending = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal) = setup(&m, &mut s);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.size(&table, &ty, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        if let Some(shape) = &state.shape {
            pending = true;
            // Compare the WHOLE owning result, including both allocated names,
            // all field rows and the tuple kind, before observed retirement.
            assert_eq!(shape.as_ref(), expected_shape.as_ref());
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
        drop(work);
        dispose(table, nominal, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(pending);
}
#[test]
fn complete_semantic_error_stays_owned_before_summary_and_resource_stop_never_becomes_unknown_size()
{
    let m = fixture();
    let ty = semantic_ty();
    let old = LayoutTable::new(&m);
    let expected = old.ty_layout(&ty).unwrap_err().to_string();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal) = setup(&m, &mut s);
    let begin = calls.get();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(state.size(&table, &ty, &mut work).unwrap(), None);
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    dispose(table, nominal, &mut s);
    drop(s);
    let mut pending = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal) = setup(&m, &mut s);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.size(&table, &ty, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        if let Some(error) = &state.error {
            pending = true;
            assert_eq!(error.to_string(), expected);
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
        drop(work);
        dispose(table, nominal, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(pending);
}
#[test]
fn complete_display_fields_and_both_actual_output_allocation_states_remain_custodied() {
    let m = fixture();
    let old = LayoutTable::new(&m);
    let old_nominal = m.nominal_type_reachability();
    let original = super::super::super::validate_handle_enum_layouts(&old, &old_nominal);
    let ValidationError::HandleLaneNiche {
        enum_name, detail, ..
    } = &original[0]
    else {
        panic!("expected original overlap")
    };
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal) = setup(&m, &mut s);
    let begin = calls.get();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&table, &nominal, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    dispose(table, nominal, &mut s);
    drop(s);
    let mut before = false;
    let mut after = false;
    let mut display = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal) = setup(&m, &mut s);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.run(&table, &nominal, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        display |= !state.render.is_empty();
        if &state.name == enum_name && &state.detail == detail && state.errors.is_empty() {
            if state.errors.capacity() == 0 {
                before = true
            } else {
                after = true
            }
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
        drop(work);
        dispose(table, nominal, &mut s);
    }
    assert!(before && after && display);
}
#[test]
fn earlier_rows_remain_owned_during_every_later_layout_child_field_and_transfer_refusal() {
    let mut m = fixture();
    let mut later = m.enums[0].clone();
    later.name = "later raw λ\0".into();
    later.variants[0].fields[1] = semantic_ty();
    m.enums.push(later);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal) = setup(&m, &mut s);
    let begin = calls.get();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&table, &nominal, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    dispose(table, nominal, &mut s);
    drop(s);
    let mut prior = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            cleanup_after: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal) = setup(&m, &mut s);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.run(&table, &nominal, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        prior |= !state.errors.is_empty()
            && (state.shape.is_some()
                || state.error.is_some()
                || !state.name.is_empty()
                || !state.detail.is_empty()
                || !state.render.is_empty());
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original handle-lane stop"
        );
        drop(work);
        dispose(table, nominal, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(prior);
}
fn pending<O: ExecutionObserver>(table: &LayoutTable<'_>, s: &mut ObservedSession<'_, O>) -> State {
    let mut state = State::default();
    state.shape = Some(
        table
            .ty_layout_observed(&Ty::Tuple(vec![handle(), Ty::Bool]), s, site())
            .unwrap()
            .unwrap(),
    );
    assert_eq!(state.shape.as_deref(), Some(&complete_tuple_shape()));
    state.error = Some(
        table
            .ty_layout_observed(&semantic_ty(), s, site())
            .unwrap()
            .unwrap_err(),
    );
    state.name = "name λ\0".into();
    state.detail = "detail λ\0".into();
    state.render = "complete child".into();
    state.errors = vec![ValidationError::HandleLaneNiche {
        enum_name: "prior name".into(),
        variant: 0,
        field: 0,
        detail: "prior detail".into(),
    }];
    state
}
#[test]
fn actual_owning_children_partial_strings_and_prior_rows_all_drain_under_same_stopped_session() {
    let m = complete_layout_fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal) = setup(&m, &mut s);
    let mut state = pending(&table, &mut s);
    let begin = calls.get();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    drain(&mut state, &mut work);
    drop(work);
    dispose(table, nominal, &mut s);
    drop(s);
    let mut o = Observer {
        cleanup_after: Some(begin),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = setup(&m, &mut s);
    let mut state = pending(&table, &mut s);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(work);
    dispose(table, nominal, &mut s);
    drop(s);
    assert_eq!(&o.events[..begin], &baseline.events[..begin]);
    assert!(
        o.events[begin..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
