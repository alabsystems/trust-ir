// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn whole_original_closure_valid_body_and_bodyless_signature_keep_empty_diagnostics() {
    let m = fixture();
    assert!(run(&m, 0, None).0.is_empty());
    assert!(run(&m, 1, None).0.is_empty());
}
#[test]
fn whole_missing_getter_error_precedes_later_cross_errors_and_only_returns_skip() {
    let mut m = fixture();
    m.functions[0].ty = FuncTyId::new(999);
    replace(
        &mut m,
        vec![
            Inst::Drop {
                ptr: v(0),
                ty: Ty::Bool,
            },
            Inst::Return { values: vec![v(1)] },
        ],
    );
    let out = run(&m, 0, None).0;
    assert!(matches!(
        &out[..],
        [
            ValidationError::FuncTypeNotFound { .. },
            ValidationError::OperandTypeMismatch { .. }
        ]
    ));
}
#[test]
fn whole_actual_effect_then_entry_then_all_node_route_error_order_is_exact() {
    let out = run(&broad(), 0, None).0;
    assert!(out.len() > 10);
    let effect = out
        .iter()
        .position(|e| matches!(e, ValidationError::FuncAttrClaimViolated { .. }))
        .unwrap();
    let entry = out
        .iter()
        .position(|e| matches!(e, ValidationError::EntryParamsMismatch { .. }))
        .unwrap();
    let call = out
        .iter()
        .position(|e| matches!(e, ValidationError::CallArgCountMismatch { .. }))
        .unwrap();
    assert!(effect < entry && entry < call);
}
#[test]
fn actual_enum_rule2_precedes_entry_and_all_nominal_or_node_diagnostics() {
    let mut m = enum_fixture();
    m.func_types[0].params.clear();
    m.functions[0].blocks[1].body.insert(
        0,
        InstrNode::new(Inst::Drop {
            ptr: v(1),
            ty: Ty::U8,
        }),
    );
    let out = run(&m, 0, None).0;
    assert!(matches!(
        &out[0],
        ValidationError::ExhaustiveSwitchCasesIncomplete { .. }
    ));
    assert!(matches!(
        &out[1],
        ValidationError::EntryParamsMismatch { .. }
    ));
    assert!(
        out.iter()
            .any(|e| matches!(e, ValidationError::OperandTypeMismatch { .. }))
    );
    assert!(run(&signed_enum(), 0, None).0.is_empty());
}
#[test]
fn all_three_direct_families_keep_actual_refinement_defer_and_invoke_strictness() {
    for family in 0..3 {
        let mut m = fixture();
        m.functions[0].blocks[0].params[1].1 = Ty::Refine(TyId::new(1), PredId::new(0));
        let node = match family {
            0 => Inst::Call {
                callee: FuncId::new(9),
                args: vec![v(1)],
            },
            1 => Inst::CallCannotUnwind {
                callee: FuncId::new(9),
                args: vec![v(1)],
            },
            _ => Inst::Invoke {
                callee: FuncId::new(9),
                args: vec![v(1)],
                normal_dest: BlockId::new(2),
                normal_args: vec![],
                unwind_dest: BlockId::new(3),
            },
        };
        replace(&mut m, vec![node]);
        let out = run(&m, 0, None).0;
        assert_eq!(
            out.iter()
                .filter(|e| matches!(e, ValidationError::CallArgTypeMismatch { .. }))
                .count(),
            usize::from(family == 2)
        );
    }
}
#[test]
fn all_three_indirect_families_use_actual_coordinate_and_typed_static_provenance() {
    for family in 0..3 {
        let mut m = fixture();
        m.functions[1].calling_conv = CallingConv::Rust;
        m.functions[0].blocks[0].body = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Func(FuncTyId::new(1)),
                value: Constant::FnDef(FuncId::new(9)),
            })
            .with_result(v(10)),
            InstrNode::new(indirect(family, 10, 1, vec![v(0)])),
        ];
        if family == 2 {
            for id in [2, 3] {
                let mut exit = Block::new(BlockId::new(id));
                exit.body.push(InstrNode::new(Inst::Unreachable));
                m.functions[0].blocks.push(exit);
            }
        } else {
            m.functions[0].blocks[0]
                .body
                .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        }
        let analysis = StaticFunctionPointerAnalysis::new(&m.functions[0]);
        assert!(
            analysis.dominator_tree().is_well_formed(),
            "actual valid fixture CFG"
        );
        assert_eq!(
            analysis
                .resolve_typed_at(v(10), BlockId::new(1), 1)
                .map(|r| r.function()),
            Some(FuncId::new(9)),
            "the actual typed static provenance must exist before asserting its convention diagnostic"
        );
        let out = run(&m, 0, None).0;
        assert!(
            out.iter()
                .any(|e| matches!(e, ValidationError::CallIndirectArgTypeMismatch { .. }))
        );
        assert!(
            out.iter()
                .any(|e| matches!(e, ValidationError::CallEdgeConvMismatch { .. }))
        );
    }
}
#[test]
fn actual_physical_function_position_never_substitutes_a_same_id_other_body() {
    let mut m = fixture();
    let mut other = m.functions[0].clone();
    other.name = "other".into();
    other.blocks[0].body = vec![InstrNode::new(Inst::Return { values: vec![v(1)] })];
    m.functions.insert(0, other);
    let a = run(&m, 0, None).0;
    let b = run(&m, 1, None).0;
    assert!(!a.is_empty());
    assert!(b.is_empty());
}
#[test]
fn general_module_value_map_keeps_indexed_duplicate_id_semantics_distinct_from_catalog() {
    let mut m = fixture();
    m.functions[1].id = FuncId::new(1);
    let mut duplicate = m.functions[1].clone();
    duplicate.name = "duplicate".into();
    m.functions.push(duplicate);
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![v(1)],
        })
        .with_result(v(10)),
        InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }),
    ];
    let out = run(&m, 0, None).0;
    assert!(
        out.iter()
            .any(|e| matches!(e, ValidationError::CalleeNotFound { callee_id: 1, .. }))
    );
    assert!(
        out.iter()
            .any(|e| matches!(e, ValidationError::ReturnTypeMismatch { .. }))
    );
}
#[test]
fn seq_map_missing_signature_type_and_full_signature_mismatches_take_actual_route() {
    for fwd in [9, 999] {
        let mut m = fixture();
        replace(
            &mut m,
            vec![Inst::SeqMap {
                ty: Ty::Sequence(TyId::new(0)),
                seq: v(0),
                fwd: FuncId::new(fwd),
            }],
        );
        assert!(!run(&m, 0, None).0.is_empty());
    }
}
#[test]
fn projection_make_aggregate_and_zero_length_splat_keep_independent_ordered_errors() {
    let out = run(&broad(), 0, None).0;
    assert!(
        out.iter()
            .any(|e| matches!(e, ValidationError::InvalidMakeAggregate { .. }))
    );
    assert!(
        out.iter()
            .any(|e| matches!(e, ValidationError::NonCanonicalUniformArray { .. }))
    );
}
#[test]
fn builtin_before_optional_schema_is_preserved_and_no_schema_is_the_original_lane() {
    let mut m = fixture();
    replace(
        &mut m,
        vec![Inst::DialectOp(Box::new(DialectInst::new(
            "gpu",
            "not_an_op",
        )))],
    );
    let registry = DialectSchemaRegistry::new(Vec::<DialectSchema>::new()).unwrap();
    let out = run(&m, 0, Some(&registry)).0;
    assert!(matches!(
        &out[..],
        [
            ValidationError::InvalidVectorDialectOp { .. },
            ValidationError::InvalidDialectSchema { .. }
        ]
    ));
    assert_eq!(run(&m, 0, None).0.len(), 1);
}
#[test]
fn nominal_handle_and_dialect_families_keep_original_actual_allocation_guards_and_slots() {
    let mut m = nominal_fixture();
    let mixed = m.functions[0].blocks[0].params[3].1.clone();
    m.functions[0].blocks[0]
        .body
        .insert(0, InstrNode::new(Inst::Undef { ty: mixed }));
    let out = run(&m, 0, None).0;
    assert!(
        out.iter()
            .any(|e| matches!(e, ValidationError::InvalidHandleUse { .. }))
    );
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
    let _ = run(&m, 0, None);
}
#[test]
fn full_unicode_function_producer_and_dialect_diagnostics_are_not_truncated() {
    let mut m = broad();
    let name = "λ🦀尾".repeat(400);
    m.functions[0].name = name.clone();
    m.functions[1].name = name.clone();
    m.functions[0].producer = Some(trust_ir::Producer::Other(name.clone()));
    let out = run(&m, 0, None).0;
    assert!(out.iter().any(
        |e| matches!(e,ValidationError::EntryParamsMismatch{func_name,..} if func_name==&name)
    ));
    assert!(out.iter().any(|e|matches!(e,ValidationError::CallArgCountMismatch{callee,caller_producer:Some(p),..} if callee==&name && p.contains(&name))));
}
#[test]
fn original_coro_suspend_takes_return_rule_and_missing_signature_is_not_a_new_default() {
    let mut m = fixture();
    replace(
        &mut m,
        vec![Inst::CoroSuspend {
            frame: v(2),
            state_slot: 0,
            next_state: 1,
            value: v(1),
        }],
    );
    assert!(
        run(&m, 0, None)
            .0
            .iter()
            .any(|e| matches!(e, ValidationError::ReturnTypeMismatch { .. }))
    );
    m.functions[0].ty = FuncTyId::new(999);
    let out = run(&m, 0, None).0;
    assert!(matches!(
        &out[..],
        [ValidationError::FuncTypeNotFound { .. }]
    ));
}

#[test]
fn both_panic_routes_use_actual_physical_coordinates_and_complete_parenthesized_signature() {
    for invoke in [false, true] {
        let mut m = fixture();
        let panic = PanicSite {
            entry: FuncId::new(9),
            location: PanicLocation::Value(v(2)),
        };
        let node = if invoke {
            Inst::AssertInvoke {
                cond: v(0),
                kind: AssertKind::Unspecified,
                site: panic,
                normal_dest: BlockId::new(2),
                normal_args: vec![],
                unwind_dest: BlockId::new(3),
            }
        } else {
            Inst::Assert {
                cond: v(0),
                kind: AssertKind::Unspecified,
                site: Some(panic),
            }
        };
        m.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Copy {
                ty: Ty::Bool,
                operand: v(0),
            })
            .with_result(v(15)),
        );
        m.functions[0].blocks[0]
            .body
            .insert(1, InstrNode::new(node));
        let out = run(&m, 0, None).0;
        assert!(out.iter().any(|e|matches!(e,ValidationError::PanicEntrySignatureMismatch{block:1,inst_index:1,found,..} if found=="fn(u64) -> (u64)")));
    }
}
