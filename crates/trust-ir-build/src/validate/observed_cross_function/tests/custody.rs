// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inspect(m: &Module, mut inspect: impl FnMut(&State<'_, '_>)) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (layouts, catalog, census, nominal) = setup(m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state
        .run(
            &layouts,
            &catalog,
            0,
            census,
            nominal.as_ref(),
            None,
            &mut w,
        )
        .unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    empty(&state);
    drop(w);
    drop(state);
    dispose(layouts, catalog, nominal, &mut s);
    drop(s);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (layouts, catalog, census, nominal) = setup(m, &mut s);
        let mut state = State::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(
                &layouts,
                &catalog,
                0,
                census,
                nominal.as_ref(),
                None,
                &mut w
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        inspect(&state);
        drain(&mut state, &mut w);
        empty(&state);
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original cross-function stop"
        );
        drop(w);
        drop(state);
        dispose(layouts, catalog, nominal, &mut s);
    }
}
#[test]
fn complete_missing_signature_getter_error_is_owned_before_parent_reserve_or_transfer() {
    let mut m = fixture();
    m.functions[0].ty = FuncTyId::new(999);
    m.functions[0].name = "λ尾".repeat(400);
    let mut saw = false;
    inspect(&m, |s| {
        if let Some(Err(ValidationError::FuncTypeNotFound { func_name, .. })) = &s.getter {
            saw = true;
            assert_eq!(func_name, &m.functions[0].name);
        }
    });
    assert!(saw);
}
#[test]
fn full_general_value_map_and_eager_indirect_context_remain_parent_owned_until_cleanup() {
    let m = fixture();
    let mut saw = false;
    inspect(&m, |s| {
        saw |= s.values.is_some() && s.indirect.is_some() && s.signature.is_some();
    });
    assert!(saw);
}
#[test]
fn actual_census_predicates_build_and_hold_both_complete_guard_and_slot_children() {
    let mut m = nominal_fixture();
    m.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::ExtractField {
            ty: Ty::Bool,
            aggregate: v(3),
            field: 1,
        })
        .with_result(v(99)),
    );
    let mut saw = false;
    inspect(&m, |s| {
        saw |=
            s.guards.is_some() && s.slots.is_some() && s.values.is_some() && s.indirect.is_some();
    });
    assert!(saw);
}
#[test]
fn complete_multi_error_batch_and_all_prior_errors_are_owned_during_aggregation() {
    let mut m = fixture();
    m.func_types[0].params.clear();
    replace(
        &mut m,
        vec![Inst::Call {
            callee: FuncId::new(9),
            args: vec![v(0), v(2)],
        }],
    );
    let mut saw = false;
    inspect(&m, |s| {
        saw |= s.pending.len() == 2
            && matches!(
                s.errors.first(),
                Some(ValidationError::EntryParamsMismatch { .. })
            );
    });
    assert!(saw);
}
#[test]
fn mismatched_layout_or_nominal_source_and_missing_or_extra_summary_are_typed_refusals() {
    let m = fixture();
    let foreign = nominal_fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (layouts, catalog, census, nominal) = setup(&m, &mut s);
    let other = trust_ir::LayoutTable::new_observed(&foreign, &mut s, site()).unwrap();
    let other_nominal = foreign
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    assert_eq!(
        validate_cross_function_observed(&other, &catalog, 0, census, None, None, &mut s, site()),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(
        validate_cross_function_observed(
            &layouts,
            &catalog,
            0,
            NominalCensus {
                handle: true,
                dialect: false
            },
            Some(&other_nominal),
            None,
            &mut s,
            site()
        ),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(
        validate_cross_function_observed(
            &layouts,
            &catalog,
            0,
            NominalCensus {
                handle: true,
                dialect: false
            },
            None,
            None,
            &mut s,
            site()
        ),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(
        validate_cross_function_observed(
            &layouts,
            &catalog,
            0,
            census,
            Some(&other_nominal),
            None,
            &mut s,
            site()
        ),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(
        validate_cross_function_observed(
            &layouts,
            &catalog,
            usize::MAX,
            census,
            None,
            None,
            &mut s,
            site()
        ),
        Err(ObservedValueError::InvalidRange)
    );
    other_nominal.retire_observed(&mut s, site()).unwrap();
    s.retirement_step(site(), size_of::<trust_ir::LayoutTable<'_>>() + 1);
    drop(other);
    s.retirement_poll(site());
    dispose(layouts, catalog, nominal, &mut s);
}
#[test]
fn census_absence_keeps_guard_and_slot_analyses_absent_without_hiding_actual_module_errors() {
    let m = broad();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (layouts, catalog, census, nominal) = setup(&m, &mut s);
    assert_eq!(census, NominalCensus::default());
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state
        .run(&layouts, &catalog, 0, census, None, None, &mut w)
        .unwrap();
    assert!(state.guards.is_none() && state.slots.is_none());
    assert!(!state.errors.is_empty());
    drain(&mut state, &mut w);
    empty(&state);
    drop(w);
    drop(state);
    dispose(layouts, catalog, nominal, &mut s);
}
#[test]
fn complete_output_retirement_has_healthy_terminal_receipt_or_original_sticky_cleanup() {
    let m = broad();
    for refuse in [false, true] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            cleanup: Some(arm.clone()),
            ..Observer::default()
        };
        let trace = o.trace.clone();
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (layouts, catalog, census, nominal) = setup(&m, &mut s);
        let out = validate_cross_function_observed(
            &layouts,
            &catalog,
            0,
            census,
            nominal.as_ref(),
            None,
            &mut s,
            site(),
        )
        .unwrap();
        assert_eq!(out, original::run(&m, 0, None));
        let begin = calls.get();
        arm.set(refuse);
        let result = retire_validation_errors_observed(out, &mut s, site());
        let end = calls.get();
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
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
                    (ExecutionPhase::Publication, 0, 0)
                );
            }
        }
        dispose(layouts, catalog, nominal, &mut s);
    }
}
#[test]
fn dialect_only_census_with_present_nominal_summary_cannot_enable_handle_guards_or_slots() {
    let mut m = fixture();
    let dialect = Ty::Dialect(Box::new(trust_ir::DialectTy::new("ns", "D", 1)));
    m.func_types[0].params.push(dialect.clone());
    m.functions[0].blocks[0]
        .params
        .push((v(3), dialect.clone()));
    m.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Alloca {
            ty: dialect,
            count: None,
            align: None,
        })
        .with_result(v(20)),
    );
    m.functions[0].blocks[0].body.insert(
        1,
        InstrNode::new(Inst::ExtractField {
            ty: Ty::Bool,
            aggregate: v(3),
            field: 1,
        })
        .with_result(v(21)),
    );
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (layouts, catalog, census, nominal) = setup(&m, &mut s);
    assert!(census.dialect && !census.handle && nominal.is_some());
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state
        .run(
            &layouts,
            &catalog,
            0,
            census,
            nominal.as_ref(),
            None,
            &mut w,
        )
        .unwrap();
    assert!(state.guards.is_none() && state.slots.is_none());
    assert_eq!(state.errors, original::run(&m, 0, None));
    drain(&mut state, &mut w);
    empty(&state);
    drop(w);
    drop(state);
    dispose(layouts, catalog, nominal, &mut s);
}
