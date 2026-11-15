// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
mod surfaces;
#[test]
fn exact_full_table_errors_keep_original_child_then_pending_defect_order() {
    let mut m = module();
    m.universes.extend([
        Universe::IntRange { lo: 8, hi: 2 },
        Universe::Members(vec![]),
        Universe::Members(vec![Constant::Int(3), Constant::Int(2)]),
        Universe::IntRange { lo: 1, hi: 3 },
    ]);
    m.predicates.extend([
        Pred::Interval { lo: 8, hi: 2 },
        Pred::FiniteSet(vec![Constant::Float(f64::from_bits(0x7ff8_0000_0000_1234))]),
        Pred::Conj(vec![PredId::new(99)]),
        Pred::Disj(vec![PredId::new(14), PredId::new(99)]),
        Pred::Top,
        Pred::InUniverse(UnivId::new(99), Space::Index),
    ]);
    let (e, _, _) = run(&m);
    assert!(e.iter().any(|e| matches!(
        e,
        ValidationError::PredicateTableNotInterned {
            kind: "universe",
            first: 0,
            ..
        }
    )));
    assert!(e.iter().any(|e|matches!(e,ValidationError::PredicateTableMalformed{detail,..}if detail.contains("not in canonical order")&&detail.contains("): entries"))));
    let at=e.iter().position(|e|matches!(e,ValidationError::DanglingPredicateRef{location,id:99,..}if location=="pred.12")).unwrap();
    assert!(
        matches!(&e[at+1],ValidationError::PredicateTableMalformed{detail,..}if detail.contains("1 operand(s)"))
    );
}
#[test]
fn all_inline_container_occurrences_keep_complete_location_and_first_defect_fields() {
    let mut m = module();
    let bad = Ty::Refine(TyId::new(99), PredId::new(99));
    m.types.extend([
        Ty::Tuple(vec![
            Ty::Ref(Box::new(bad.clone())),
            Ty::Rc(Box::new(bad.clone())),
        ]),
        Ty::Refine(TyId::new(0), PredId::new(99)),
        Ty::Refine(TyId::new(3), PredId::new(1)),
    ]);
    m.structs.push(strukt(31, bad.clone()));
    m.records.push(RecordDef {
        id: RecordId::new(8),
        name: "R'λ".into(),
        fields: vec![FieldDef {
            name: "f'λ".into(),
            ty: bad.clone(),
            offset: None,
        }],
    });
    m.enums.push(enumeration(vec![bad.clone()]));
    m.func_types[0].params.push(bad.clone());
    m.func_types[0].returns.push(bad.clone());
    m.functions.push(function(
        10,
        0,
        vec![(v(0), bad.clone())],
        vec![node(
            Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: bad.clone(),
                dst_ty: bad,
                operand: v(0),
            },
            &[],
        )],
    ));
    let (e, _, _) = run(&m);
    let locs = e
        .iter()
        .filter_map(|e| match e {
            ValidationError::RefinementTypeInvalid { location, .. }
            | ValidationError::DanglingPredicateRef { location, .. } => Some(location.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(locs.contains(&"type ty.3"));
    assert!(locs.iter().any(|l| l.contains("instruction 0")));
    assert_eq!(
        locs.iter().filter(|l| l.contains("instruction 0")).count(),
        2
    );
}
#[test]
fn empty_predicate_table_still_checks_types_before_the_original_consumption_exit() {
    let mut m = small();
    m.predicates.clear();
    m.functions[0].blocks[0].params[0].1 = r(2);
    let (e, _, _) = run(&m);
    assert!(e.iter().any(|e| matches!(
        e,
        ValidationError::DanglingPredicateRef {
            kind: "pred",
            id: 2,
            ..
        }
    )));
    assert!(
        !e.iter()
            .any(|e| matches!(e, ValidationError::RefinementNotImplied { .. }))
    );
}
#[test]
fn entry_signature_to_declared_parameter_direction_is_preserved() {
    let mut m = small();
    m.func_types[0].params[0] = r(1);
    m.func_types[0].returns.clear();
    m.functions[0].blocks[0].body.clear();
    m.functions[0].blocks[0].params[0].1 = r(2);
    let (e, _, _) = run(&m);
    assert!(
        matches!(e.as_slice(),[ValidationError::RefinementNotImplied{location,..}]if location.ends_with("entry param 0"))
    );
    m.func_types[0].params[0] = r(2);
    m.functions[0].blocks[0].params[0].1 = r(1);
    assert!(run(&m).0.is_empty());
}
#[test]
fn direct_indirect_and_both_invoke_halves_keep_all_original_error_order() {
    let m = calls();
    let (e, _, _) = run(&m);
    let locations = e
        .iter()
        .filter_map(|e| match e {
            ValidationError::RefinementNotImplied { location, .. } => Some(location.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(locations.iter().any(|s| s.contains("call @")));
    assert!(
        locations
            .iter()
            .any(|s| s.contains("call_indirect functy.1"))
    );
    assert!(
        locations
            .iter()
            .any(|s| s.contains("invoke_indirect functy.1"))
    );
    assert_eq!(
        locations
            .iter()
            .filter(|s| s.contains("-> bb1 join arg 0"))
            .count(),
        2
    );
}
#[test]
fn duplicate_missing_callees_signatures_and_unknown_values_keep_original_skips() {
    let mut m = calls();
    m.functions.push(m.functions[1].clone());
    m.functions[0].blocks[0].body.push(node(
        Inst::Call {
            callee: FuncId::new(999),
            args: vec![v(999)],
        },
        &[],
    ));
    m.functions[0].blocks[0].body.push(node(
        Inst::CallIndirect {
            callee: v(90),
            sig: FuncTyId::new(99),
            args: vec![v(0)],
            calling_conv: CallingConv::Rust,
        },
        &[],
    ));
    let (e, _, _) = run(&m);
    assert!(!e.iter().any(|e|matches!(e,ValidationError::RefinementNotImplied{location,..}if location.contains("call @"))));
}
#[test]
fn return_and_coro_yield_keep_complete_required_predicate_diagnostics() {
    let mut m = small();
    m.functions[0].blocks[0].body.push(node(
        Inst::CoroSuspend {
            frame: v(99),
            state_slot: 9,
            next_state: -1,
            value: v(0),
        },
        &[],
    ));
    let (e, _, _) = run(&m);
    assert_eq!(
        e.iter()
            .filter(|e| matches!(e, ValidationError::RefinementNotImplied { .. }))
            .count(),
        2
    );
    assert!(
        matches!(&e[1],ValidationError::RefinementNotImplied{location,actual,required}if location.contains("coro_suspend yield 0")&&actual.contains("fact was dropped")&&required.contains("in[5, 9]"))
    );
}
#[test]
fn every_store_consumes_the_written_value_including_cmpxchg_desired() {
    let mut m = small();
    m.functions[0].blocks[0].body = vec![
        node(
            Inst::Store {
                ty: r(2),
                ptr: v(90),
                value: v(0),
                volatile: false,
                align: None,
            },
            &[],
        ),
        node(
            Inst::AtomicStore {
                ty: r(2),
                ptr: v(90),
                value: v(0),
                ordering: Ordering::SeqCst,
            },
            &[],
        ),
        node(
            Inst::AtomicRMW {
                op: AtomicRMWOp::Add,
                ty: r(2),
                ptr: v(90),
                value: v(0),
                ordering: Ordering::SeqCst,
            },
            &[],
        ),
        node(
            Inst::CmpXchg {
                ty: r(2),
                ptr: v(90),
                expected: v(999),
                desired: v(0),
                success: Ordering::SeqCst,
                failure: Ordering::SeqCst,
                weak: true,
            },
            &[],
        ),
    ];
    let (e, _, _) = run(&m);
    assert_eq!(
        e.iter()
            .filter(|e| matches!(e, ValidationError::RefinementNotImplied { .. }))
            .count(),
        4
    );
    assert!(
        matches!(&e[3],ValidationError::RefinementNotImplied{location,..}if location.contains("cmpxchg value"))
    );
}
#[test]
fn all_struct_record_tuple_array_vector_sequence_aggregate_write_read_lanes_match() {
    let (e, _, _) = run(&aggregates());
    for text in [
        "insert_field",
        "extract_field",
        "insert_element",
        "extract_element",
        "make_aggregate",
        "array_splat",
    ] {
        assert!(e.iter().any(|e|matches!(e,ValidationError::RefinementNotImplied{location,..}if location.contains(text))),"{text}");
    }
}
#[test]
fn out_of_order_functional_frame_aliases_reach_the_full_monotone_closure() {
    let mut m = small();
    m.functions[0].blocks[0].body = vec![
        node(
            Inst::BindSlot {
                frame: v(101),
                slot: 0,
                value: v(0),
            },
            &[102],
        ),
        node(
            Inst::BindSlot {
                frame: v(100),
                slot: 0,
                value: v(0),
            },
            &[101],
        ),
        node(
            Inst::OpenFrame {
                def: BindingFrameDef::new(
                    BindingFrameId::new(7),
                    "frame λ",
                    vec![BindingSlot::new("slot λ", r(2))],
                ),
            },
            &[100],
        ),
        node(
            Inst::LoadSlot {
                frame: v(102),
                slot: 0,
                ty: r(2),
            },
            &[103],
        ),
    ];
    let (e, _, _) = run(&m);
    assert_eq!(e.iter().filter(|e|matches!(e,ValidationError::RefinementNotImplied{location,..}if location.contains("bind_slot"))).count(),2);
    assert!(!e.iter().any(|e|matches!(e,ValidationError::RefinementNotImplied{location,..}if location.contains("load_slot"))));
}
#[test]
fn propagation_contradiction_precedes_consumption_and_preserves_both_facts() {
    let mut m = small();
    m.functions[0].blocks[0].body = vec![
        node(
            Inst::Const {
                ty: r(2),
                value: Constant::Int(3),
            },
            &[1],
        ),
        node(Inst::Return { values: vec![v(1)] }, &[]),
    ];
    let (e, _, _) = run(&m);
    assert!(
        matches!(e.as_slice(),[ValidationError::RefinementContradicted{location,declared,derived}]if location.ends_with(": %1")&&declared=="in[5, 9]"&&derived=="in[3, 3]")
    );
}
#[test]
fn exact_add_sub_and_cast_facts_survive_whole_consumption() {
    let mut m = small();
    m.func_types[0].params.clear();
    m.functions[0].blocks[0].params.clear();
    m.functions[0].blocks[0].body = vec![
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(3),
            },
            &[1],
        ),
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(4),
            },
            &[2],
        ),
        node(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(1),
                rhs: v(2),
            },
            &[3],
        ),
        node(
            Inst::Cast {
                op: CastOp::SExt,
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand: v(3),
            },
            &[4],
        ),
        node(Inst::Return { values: vec![v(3)] }, &[]),
    ];
    assert!(run(&m).0.is_empty());
    m.functions[0].blocks[0].body[2] = node(
        Inst::BinOp {
            op: BinOp::Sub,
            ty: Ty::I32,
            lhs: v(1),
            rhs: v(2),
        },
        &[3],
    );
    assert!(run(&m).0.iter().any(|e|matches!(e,ValidationError::RefinementNotImplied{actual,..}if actual.contains("in[-1, -1]"))));
}
#[test]
fn finite_set_select_union_is_owned_canonical_and_preserves_full_derived_fact() {
    let mut m = module();
    m.predicates
        .push(Pred::FiniteSet(vec![Constant::Int(2), Constant::Int(4)]));
    m.predicates.push(Pred::FiniteSet(vec![
        Constant::Int(1),
        Constant::Int(2),
        Constant::Int(3),
        Constant::Int(4),
    ]));
    m.func_types[0] = sig(vec![r(5), r(10)], vec![r(11)]);
    m.functions.push(function(
        10,
        0,
        vec![(v(0), Ty::I32), (v(1), Ty::I32)],
        vec![
            node(
                Inst::Select {
                    ty: Ty::I32,
                    cond: v(99),
                    then_val: v(0),
                    else_val: v(1),
                },
                &[2],
            ),
            node(Inst::Return { values: vec![v(2)] }, &[]),
        ],
    ));
    assert!(run(&m).0.is_empty());
}
#[test]
fn enum_existential_consumption_reports_each_original_variant_or_retires_earlier_refusals() {
    let mut m = module();
    m.enums.push(enumeration(vec![r(2), r(1)]));
    m.functions.push(function(
        10,
        0,
        vec![(v(0), r(5)), (v(1), Ty::Enum(EnumId::new(17)))],
        vec![node(
            Inst::InsertField {
                ty: Ty::Enum(EnumId::new(17)),
                aggregate: v(1),
                field: 1,
                value: v(0),
            },
            &[],
        )],
    ));
    let (e, _, _) = run(&m);
    assert!(!e.iter().any(|e|matches!(e,ValidationError::RefinementNotImplied{location,..}if location.contains("insert_field"))));
    m.functions[0].blocks[0].params[0].1 = Ty::I32;
    let (e, _, _) = run(&m);
    let variants = e
        .iter()
        .filter_map(|e| match e {
            ValidationError::RefinementNotImplied { location, .. }
                if location.contains("insert_field") =>
            {
                Some(location.as_str())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(variants.len(), 2);
    assert!(variants[0].contains("variant 0λ'"));
    assert!(variants[1].contains("variant 1λ'"));
}
#[test]
fn enum_uninhabited_absent_lane_and_nonaggregate_skips_remain_semantic_only() {
    let mut m = aggregates();
    m.enums[0].variants.clear();
    m.functions[0].blocks[0].body.push(node(
        Inst::ExtractField {
            ty: r(2),
            aggregate: v(106),
            field: 99,
        },
        &[],
    ));
    let (e, _, _) = run(&m);
    assert!(!e.iter().any(|e|matches!(e,ValidationError::RefinementNotImplied{location,..}if location.contains("extract_field enum.17"))));
}
