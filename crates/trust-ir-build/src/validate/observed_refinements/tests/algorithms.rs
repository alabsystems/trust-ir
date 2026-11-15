// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn full_predicate_relation_bound_and_structural_equality_matrix_matches_real_ordinary_methods() {
    let mut m = module();
    let value = Constant::Record(vec![(
        "λ'\0".repeat(17),
        Constant::Aggregate(vec![
            Constant::Float(f64::from_bits(0x7ff8_0000_0000_1234)),
            Constant::Bytes {
                data: vec![9; 4097],
                utf8: false,
            },
            Constant::Splat {
                elem: Box::new(Constant::Bool(true)),
                len: u64::MAX,
            },
        ]),
    )]);
    m.predicates.extend([
        Pred::FiniteSet(vec![value.clone()]),
        Pred::FiniteSet(vec![value]),
        Pred::FiniteSet(vec![Constant::Float(-0.0)]),
        Pred::FiniteSet(vec![Constant::Float(0.0)]),
        Pred::NonNull,
        Pred::FiniteSet(vec![Constant::Bool(false), Constant::Bool(true)]),
    ]);
    run(&m);
    let table = m.pred_table();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    for a in &m.predicates {
        for b in &m.predicates {
            let av = lattice::View::node(a);
            let bv = lattice::View::node(b);
            assert_eq!(lattice::equal(av, bv, &mut work).unwrap(), a == b);
            assert_eq!(
                lattice::implies(&m, av, bv, 0, &mut work).unwrap(),
                table.implies_pred(a, b)
            );
        }
        assert_eq!(
            lattice::bounds(&m, lattice::View::node(a), 0, &mut work).unwrap(),
            table.interval_bound_of(a)
        );
    }
    assert!(work.session.first_refusal().is_none());
}
#[test]
fn default_first_reverse_postorder_keeps_last_duplicate_definition_and_unreachable_rows() {
    let mut m = small();
    let mut f = function(
        10,
        0,
        vec![(v(0), Ty::I32)],
        vec![node(
            Inst::Switch {
                value: v(0),
                default: b(1),
                default_args: vec![v(0)],
                cases: vec![
                    SwitchCase {
                        value: Constant::Int(0),
                        target: b(2),
                        args: vec![v(0)],
                    },
                    SwitchCase {
                        value: Constant::Int(1),
                        target: b(99),
                        args: vec![],
                    },
                ],
                exhaustive_enum_unreachable: false,
            },
            &[],
        )],
    );
    for id in [1, 2, 2, 8] {
        let mut block = Block::new(b(id));
        block.params = vec![(v(100 + id), r(2))];
        if id == 2 {
            block.body.push(node(
                Inst::Br {
                    target: b(1),
                    args: vec![v(102)],
                },
                &[],
            ));
        }
        f.blocks.push(block);
    }
    m.functions = vec![f];
    run(&m);
    let expected = super::super::super::reverse_postorder(&m.functions[0]);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut flow = graph::Flow::default();
    flow.order(&m.functions[0], &mut work).unwrap();
    assert_eq!(flow.order, expected);
    flow.incoming(&m.functions[0], &mut work).unwrap();
    assert_eq!(flow.incoming[0].0, 1);
    assert_eq!(flow.incoming[1].0, 2);
    flow.retire(&mut work);
}
#[test]
fn entire_real_propagation_map_matches_for_copy_select_arithmetic_cast_and_comparison_results() {
    let mut m = small();
    let f = &mut m.functions[0];
    f.blocks[0].body = vec![
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
            Inst::Copy {
                ty: Ty::I32,
                operand: v(1),
            },
            &[3],
        ),
        node(
            Inst::Select {
                ty: Ty::I32,
                cond: v(90),
                then_val: v(1),
                else_val: v(2),
            },
            &[4],
        ),
        node(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(1),
                rhs: v(2),
            },
            &[5],
        ),
        node(
            Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I32,
                lhs: v(1),
                rhs: v(2),
            },
            &[6],
        ),
        node(
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I32,
                dst_ty: Ty::U64,
                operand: v(1),
            },
            &[7],
        ),
        node(
            Inst::Cast {
                op: CastOp::SExt,
                src_ty: Ty::U32,
                dst_ty: Ty::I64,
                operand: v(1),
            },
            &[8],
        ),
        node(
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: Ty::I8,
                operand: v(1),
            },
            &[9],
        ),
        node(
            Inst::ICmp {
                op: trust_ir::inst::ICmpOp::Eq,
                ty: Ty::I32,
                lhs: v(1),
                rhs: v(2),
            },
            &[10],
        ),
        node(
            Inst::FCmp {
                op: trust_ir::inst::FCmpOp::OEq,
                ty: Ty::Vector(Box::new(Ty::F32), 4),
                lhs: v(1),
                rhs: v(2),
            },
            &[11],
        ),
        node(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U8,
                lhs: v(0),
                rhs: v(1),
            },
            &[12],
        ),
        node(
            Inst::Const {
                ty: Ty::F32,
                value: Constant::Float(3.0),
            },
            &[1],
        ),
    ];
    run(&m);
    let ordinary_types = super::super::super::build_module_value_types(&m.functions[0], &m);
    let mut expected_errors = vec![];
    let expected = super::super::super::propagate_function_facts(
        &mut expected_errors,
        &m,
        &m.functions[0],
        &ordinary_types,
        m.func_types.first(),
    );
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    let mut flow = graph::Flow::default();
    flow.values = Some(
        build_module_value_types_observed(&m.functions[0], &m, work.session, work.site).unwrap(),
    );
    flow.propagate(
        &mut state,
        &m,
        &m.functions[0],
        m.func_types.first(),
        &mut work,
    )
    .unwrap();
    assert_eq!(state.errors, expected_errors);
    assert_eq!(flow.derived.len(), expected.len());
    for (id, pred) in expected {
        let actual = flow.fact(id, &mut work).unwrap();
        let view = flow.facts.view(&m, actual, &mut work).unwrap();
        let mut text = String::new();
        work.pred_view(view, &mut text).unwrap();
        assert_eq!(text, pred.to_string());
        work.flat(text);
    }
    flow.retire(&mut work);
    drain(&mut state, &mut work);
}
#[test]
fn sparse_fast_index_then_first_fallback_definition_queries_match_all_three_real_tables() {
    let mut m = aggregates();
    m.structs = (0..78).map(|i| strukt(i, Ty::I32)).collect();
    m.structs[0] = strukt(77, r(1));
    m.structs[77] = strukt(77, r(2));
    run(&m);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    for id in [0, 9, 17, 31, 77, 99] {
        assert_eq!(
            consumption::strukt(&m, StructId::new(id), &mut w)
                .unwrap()
                .map(|x| x as *const _),
            m.struct_def(StructId::new(id)).map(|x| x as *const _)
        );
        assert_eq!(
            consumption::record(&m, RecordId::new(id), &mut w)
                .unwrap()
                .map(|x| x as *const _),
            m.record_def(RecordId::new(id)).map(|x| x as *const _)
        );
        assert_eq!(
            consumption::enumeration(&m, EnumId::new(id), &mut w)
                .unwrap()
                .map(|x| x as *const _),
            m.enum_def(EnumId::new(id)).map(|x| x as *const _)
        );
    }
    assert_eq!(
        consumption::strukt(&m, StructId::new(77), &mut w)
            .unwrap()
            .unwrap()
            .fields[0]
            .ty,
        r(2)
    );
    m.structs[77].id = StructId::new(99);
    assert_eq!(
        consumption::strukt(&m, StructId::new(77), &mut w)
            .unwrap()
            .unwrap()
            .fields[0]
            .ty,
        r(1)
    );
}
#[test]
fn existing_lattice_depth_cap_and_uncapped_acyclic_type_descent_keep_distinct_contracts() {
    let mut m = module();
    let mut prev = 9;
    for _ in 0..72 {
        m.predicates
            .push(Pred::Conj(vec![PredId::new(0), PredId::new(prev)]));
        prev = m.predicates.len() as u32 - 1;
    }
    m.types.push(r(prev));
    assert!(run(&m).0.is_empty());
    let cyclic = m.predicates.len() as u32;
    m.predicates.push(Pred::Conj(vec![PredId::new(cyclic)]));
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let view = lattice::View::node(m.predicates.last().unwrap());
    assert_eq!(
        lattice::bounds(&m, view, 0, &mut w).unwrap(),
        m.pred_table()
            .interval_bound_of(m.predicates.last().unwrap())
    );
    assert_eq!(
        lattice::implies(&m, view, lattice::View::NonZero, 0, &mut w).unwrap(),
        m.pred_table()
            .implies_pred(m.predicates.last().unwrap(), &Pred::NonZero)
    );
    m.types.push(r(cyclic));
    assert_eq!(
        validate_module_refinements_observed(&m, w.session, w.site),
        Err(ObservedValueError::UnsupportedValue)
    );
    assert_eq!(w.session.remaining_fuel(), 0);
    assert!(w.session.first_refusal().is_none());
}
