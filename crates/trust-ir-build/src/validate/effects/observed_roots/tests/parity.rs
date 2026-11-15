// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn missing_definition_is_untraceable_and_never_an_empty_accepting_set() {
    assert_eq!(run(&function(Vec::new()), u32::MAX), [Root::Untraceable]);
}
#[test]
fn local_formal_and_global_roots_have_the_exact_original_classification() {
    let f = function(vec![
        node(alloca(), &[3]),
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(42),
            },
            &[4],
        ),
    ]);
    assert_eq!(
        run(&f, 1),
        [Root::Place(EffectPlace::ParamPointee { index: 0 })]
    );
    assert_eq!(
        run(&f, 2),
        [Root::Place(EffectPlace::ParamPointee { index: 1 })]
    );
    assert_eq!(run(&f, 3), [Root::Local]);
    assert_eq!(
        run(&f, 4),
        [Root::Place(EffectPlace::Global(GlobalId::new(42)))]
    );
}
#[test]
fn every_address_preserving_opcode_follows_exactly_its_original_operand() {
    let instructions = [
        Inst::GEP {
            pointee_ty: Ty::U8,
            base: v(1),
            indices: vec![v(999)],
            inbounds: false,
        },
        Inst::PtrData {
            ptr_ty: Ty::Ptr,
            ptr: v(1),
        },
        Inst::Borrow { ptr: v(1) },
        Inst::BorrowMut { ptr: v(1) },
        copy(1),
        Inst::Cast {
            op: CastOp::PtrToPtr,
            src_ty: Ty::U32,
            dst_ty: Ty::U8,
            operand: v(1),
        },
    ];
    for instruction in instructions {
        assert_eq!(
            run(&function(vec![node(instruction, &[9])]), 9),
            [Root::Place(EffectPlace::ParamPointee { index: 0 })]
        );
    }
}
#[test]
fn selects_follow_both_address_arms_and_ignore_the_condition() {
    let f = function(vec![node(alloca(), &[3]), node(select(3, 1), &[9])]);
    assert_eq!(
        run(&f, 9),
        [
            Root::Local,
            Root::Place(EffectPlace::ParamPointee { index: 0 })
        ]
    );
}
#[test]
fn shared_select_operand_and_converging_diamond_are_done_not_cycles() {
    let f = function(vec![
        node(alloca(), &[3]),
        node(copy(3), &[4]),
        node(copy(3), &[5]),
        node(select(4, 5), &[6]),
        node(select(6, 6), &[9]),
    ]);
    assert_eq!(run(&f, 9), [Root::Local]);
}
#[test]
fn self_and_two_node_cycles_are_unknown_while_other_select_roots_are_retained() {
    let f = function(vec![node(copy(9), &[9])]);
    assert_eq!(run(&f, 9), [Root::Untraceable]);
    let f = function(vec![
        node(copy(10), &[9]),
        node(copy(9), &[10]),
        node(alloca(), &[3]),
        node(select(9, 3), &[11]),
    ]);
    assert_eq!(run(&f, 11), [Root::Local, Root::Untraceable]);
}
#[test]
fn all_parameter_and_node_definitions_contribute_instead_of_last_write_winning() {
    let mut f = function(vec![
        node(alloca(), &[1]),
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(8),
            },
            &[1],
        ),
    ]);
    let mut block = Block::new(BlockId::new(2));
    block.params.push((v(1), Ty::Ptr));
    f.blocks.push(block);
    assert_eq!(
        run(&f, 1),
        [
            Root::Local,
            Root::Place(EffectPlace::ParamPointee { index: 0 }),
            Root::Place(EffectPlace::Global(GlobalId::new(8))),
            Root::Untraceable
        ]
    );
}
#[test]
fn repeated_and_nonfirst_result_ids_use_every_original_definition_row() {
    let f = function(vec![node(alloca(), &[8, 9, 9]), node(copy(8), &[10, 11])]);
    for id in [8, 9, 10, 11] {
        assert_eq!(run(&f, id), [Root::Local]);
    }
}
#[test]
fn a_nonentry_block_parameter_is_unknown_even_when_an_incoming_argument_is_local() {
    let mut f = function(vec![
        node(alloca(), &[3]),
        node(
            Inst::Br {
                target: BlockId::new(1),
                args: vec![v(3)],
            },
            &[],
        ),
    ]);
    let mut block = Block::new(BlockId::new(1));
    block.params.push((v(9), Ty::Ptr));
    f.blocks.push(block);
    assert_eq!(run(&f, 9), [Root::Untraceable]);
}
#[test]
fn every_current_instruction_tag_is_classified_without_type_or_opcode_validity_invention() {
    let instructions = witnesses::all();
    assert_eq!(instructions.len(), 67);
    let names = instructions
        .iter()
        .map(|i| format!("{:?}", i.shape()))
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(names.len(), 67);
    for instruction in instructions {
        let expected = match &instruction {
            Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::Copy { .. }
            | Inst::Select { .. } => Root::Place(EffectPlace::ParamPointee { index: 0 }),
            Inst::Alloca { .. } => Root::Local,
            Inst::GlobalAddr { global } => Root::Place(EffectPlace::Global(*global)),
            _ => Root::Untraceable,
        };
        assert_eq!(run(&function(vec![node(instruction, &[9])]), 9), [expected]);
    }
}
#[test]
fn canonical_set_keeps_all_root_kinds_sorted_and_deduplicates_only_equal_scalars() {
    let f = mixed();
    assert_eq!(
        run(&f, 7),
        [
            Root::Local,
            Root::Place(EffectPlace::ParamPointee { index: 0 }),
            Root::Place(EffectPlace::Global(GlobalId::new(9))),
            Root::Untraceable
        ]
    );
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = Trace::default();
    let rows = [
        Root::Untraceable,
        Root::Place(EffectPlace::Global(GlobalId::new(u32::MAX))),
        Root::Place(EffectPlace::Global(GlobalId::new(0))),
        Root::Place(EffectPlace::ParamPointee { index: u32::MAX }),
        Root::Place(EffectPlace::ParamPointee { index: 0 }),
        Root::Local,
    ];
    for row in rows {
        state.root(row, &mut w).unwrap();
        state.root(row, &mut w).unwrap();
    }
    let expected = rows
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    assert_eq!(state.output.rows, expected);
    let roots = state.finish(Ok(()), &mut w).unwrap();
    roots.retire_observed(w.session, w.site).unwrap();
}
#[test]
fn long_reverse_stored_address_chain_remains_exact_under_iterative_lookup() {
    let mut nodes = Vec::new();
    for id in (4..104).rev() {
        nodes.push(node(copy(id - 1), &[id]));
    }
    nodes.push(node(alloca(), &[3]));
    assert_eq!(run(&function(nodes), 103), [Root::Local]);
}
#[test]
fn ignored_inline_types_remain_borrowed_and_unwalked() {
    let f = function(vec![node(copy(1), &[9])]);
    let (_, before) = query_trace(&f, 9);
    let mut changed = f.clone();
    changed.blocks[0].body[0].inst = Inst::Copy {
        ty: Ty::Tuple(vec![Ty::Tuple(vec![Ty::U8]); 3000]),
        operand: v(1),
    };
    let (left, _) = query_trace(&f, 9);
    let (right, right_bound) = query_trace(&changed, 9);
    assert_eq!(before, right_bound);
    assert_eq!(left.events, right.events);
}
#[test]
fn only_ptr_to_ptr_among_all_seventeen_cast_operations_preserves_the_address() {
    for op in [
        CastOp::Trunc,
        CastOp::ZExt,
        CastOp::SExt,
        CastOp::FPTrunc,
        CastOp::FPExt,
        CastOp::FPToUI,
        CastOp::FPToSI,
        CastOp::UIToFP,
        CastOp::SIToFP,
        CastOp::PtrToInt,
        CastOp::IntToPtr,
        CastOp::PtrToPtr,
        CastOp::Bitcast,
        CastOp::Transmute,
        CastOp::ReifyFnPointer,
        CastOp::FPToSISat,
        CastOp::FPToUISat,
    ] {
        let f = function(vec![node(
            Inst::Cast {
                op,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Ptr,
                operand: v(1),
            },
            &[9],
        )]);
        assert_eq!(
            run(&f, 9),
            if op == CastOp::PtrToPtr {
                vec![Root::Place(EffectPlace::ParamPointee { index: 0 })]
            } else {
                vec![Root::Untraceable]
            }
        );
    }
}
