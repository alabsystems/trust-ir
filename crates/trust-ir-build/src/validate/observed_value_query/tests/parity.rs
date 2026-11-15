// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn all_current_inference_cases_match_the_ordinary_query_for_every_result_position() {
    let mut shapes = std::collections::BTreeSet::new();
    for instruction in witnesses::all() {
        assert!(shapes.insert(instruction.shape()));
        let f = function(vec![node(instruction, &[7, 8, 7])]);
        for value in [7, 8, 99] {
            parity(&f, value);
        }
    }
    assert_eq!(shapes, InstShape::ALL.iter().copied().collect());
}

#[test]
fn first_typeable_definition_wins_instead_of_the_last_write_map() {
    let f = function(vec![
        node(Inst::Undef { ty: Ty::U8 }, &[7]),
        node(Inst::Undef { ty: Ty::U32 }, &[7]),
    ]);
    assert_eq!(parity(&f, 7), Some(Ty::U8));
    assert_eq!(
        super::super::super::build_function_value_types(&f)[&7],
        Ty::U32
    );
}

#[test]
fn block_local_parameter_then_body_order_differs_from_collecting_all_parameters_first() {
    let mut f = function(vec![node(Inst::Undef { ty: Ty::U8 }, &[7])]);
    f.blocks.push(Block::new(b(1)).with_param(id(7), Ty::U32));
    assert_eq!(parity(&f, 7), Some(Ty::U8));
    f.blocks[0]
        .params
        .extend([(id(7), Ty::Bool), (id(7), Ty::I8)]);
    assert_eq!(parity(&f, 7), Some(Ty::Bool));
}

#[test]
fn every_untypeable_definition_falls_through_to_a_later_typeable_result() {
    let mut checked = 0;
    for instruction in witnesses::all() {
        if super::super::super::infer_result_type(&instruction).is_some() {
            continue;
        }
        checked += 1;
        let f = function(vec![
            node(instruction, &[7, 8]),
            node(Inst::Undef { ty: Ty::I32 }, &[8, 7]),
        ]);
        assert_eq!(parity(&f, 7), Some(Ty::I32));
        assert_eq!(parity(&f, 8), Some(Ty::I32));
    }
    // The fixture's two-result dialect joins the 31 always-untyped shapes.
    assert_eq!(checked, 32);
}

#[test]
fn all_six_unknown_call_forms_before_a_borrow_do_not_mask_its_fat_root() {
    let mut checked = 0;
    for instruction in witnesses::all() {
        if !matches!(
            instruction,
            Inst::Call { .. }
                | Inst::CallCannotUnwind { .. }
                | Inst::Invoke { .. }
                | Inst::CallIndirect { .. }
                | Inst::CallIndirectCannotUnwind { .. }
                | Inst::InvokeIndirect { .. }
        ) {
            continue;
        }
        checked += 1;
        let mut f = function(vec![
            node(instruction, &[7]),
            node(Inst::Borrow { ptr: id(1) }, &[7]),
        ]);
        f.blocks[0]
            .params
            .push((id(1), Ty::FatPtr(FatPtrKind::Str)));
        assert_eq!(parity(&f, 7), Some(Ty::FatPtr(FatPtrKind::Str)));
    }
    assert_eq!(checked, 6);
}

#[test]
fn a_typeable_nonborrow_or_parameter_stops_a_later_borrow_definition() {
    let mut f = function(vec![
        node(Inst::Undef { ty: Ty::U8 }, &[7]),
        node(Inst::Borrow { ptr: id(1) }, &[7]),
    ]);
    f.blocks[0]
        .params
        .push((id(1), Ty::FatPtr(FatPtrKind::Str)));
    assert_eq!(parity(&f, 7), Some(Ty::U8));
    f.blocks[0].params.push((id(7), Ty::I64));
    assert_eq!(parity(&f, 7), Some(Ty::I64));
}

#[test]
fn zero_and_multi_result_dialects_are_untypeable_but_single_declared_type_covers_all_ids() {
    for declared in [0, 1, 2, 100] {
        let f = function(vec![
            node(dialect(declared), &[7, 8]),
            node(Inst::Undef { ty: Ty::Bool }, &[7, 8]),
        ]);
        let expected = if declared == 1 { Ty::U8 } else { Ty::Bool };
        assert_eq!(parity(&f, 7), Some(expected.clone()));
        assert_eq!(parity(&f, 8), Some(expected));
    }
}

#[test]
fn comparison_result_reads_only_outer_vector_lanes_even_for_malformed_elements() {
    for float in [false, true] {
        let make = |ty| {
            if float {
                Inst::FCmp {
                    op: FCmpOp::OEq,
                    ty,
                    lhs: v(),
                    rhs: v(),
                }
            } else {
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty,
                    lhs: v(),
                    rhs: v(),
                }
            }
        };
        for lanes in [0, 17, u32::MAX] {
            let a = function(vec![node(make(Ty::Vector(Box::new(Ty::U8), lanes)), &[7])]);
            let c = function(vec![node(
                make(Ty::Vector(
                    Box::new(Ty::Tuple(vec![Ty::Error; 5000])),
                    lanes,
                )),
                &[7],
            )]);
            assert_eq!(parity(&c, 7), Some(Ty::Vector(Box::new(Ty::Bool), lanes)));
            assert_eq!(run(&a, 7).1.events, run(&c, 7).1.events);
        }
        let scalar = function(vec![node(make(Ty::Tuple(vec![Ty::Error; 20])), &[7])]);
        assert_eq!(parity(&scalar, 7), Some(Ty::Bool));
    }
}

#[test]
fn absence_empty_results_and_declared_error_remain_distinct_answers() {
    let f = function(vec![node(Inst::Undef { ty: Ty::Error }, &[])]);
    assert_eq!(parity(&f, 7), None);
    let mut f = function(vec![]);
    f.blocks[0].params.push((id(7), Ty::Error));
    assert_eq!(parity(&f, 7), Some(Ty::Error));
    f.blocks.clear();
    assert_eq!(parity(&f, 7), None);
}
