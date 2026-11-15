// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
fn branch(to: u32) -> InstrNode {
    InstrNode::new(Inst::Br {
        target: BlockId::new(to),
        args: vec![],
    })
}
fn finish() -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![] })
}
#[test]
fn real_single_block_roundtrip_matches_complete_original_analysis_and_accesses() {
    let (m, f) = fixture();
    run(&m, &f);
    for i in 0..3 {
        assert_eq!(node_access(&m, &f, 0, i), Ok(()));
    }
}
#[test]
fn missing_or_later_store_never_initializes_an_earlier_read() {
    let (m, mut f) = fixture();
    f.blocks[0].body.remove(1);
    run(&m, &f);
    assert!(
        node_access(&m, &f, 0, 1)
            .unwrap_err()
            .contains("not dominated by a store")
    );
    f.blocks[0].body.insert(2, store(handle(), 10, 0));
    run(&m, &f);
    assert!(node_access(&m, &f, 0, 1).is_err());
}
#[test]
fn borrowed_chain_converges_in_reverse_block_storage_order() {
    let (m, mut f) = fixture();
    f.blocks[0].body = vec![
        allocation(handle(), None, None, 10),
        store(handle(), 10, 0),
        branch(2),
    ];
    let mut third = Block::new(BlockId::new(3));
    third.body = vec![
        InstrNode::new(Inst::BorrowMut { ptr: v(11) }).with_result(v(12)),
        load(handle(), 12, 20),
        InstrNode::new(Inst::EndBorrow { borrow_ptr: v(12) }),
        finish(),
    ];
    let mut second = Block::new(BlockId::new(2));
    second.body = vec![
        InstrNode::new(Inst::Borrow { ptr: v(10) }).with_result(v(11)),
        branch(3),
    ];
    f.blocks.extend([third, second]);
    run(&m, &f);
    assert_eq!(node_access(&m, &f, 1, 1), Ok(()));
}
#[test]
fn every_borrow_result_joins_but_duplicate_definitions_fail_closed_in_key_order() {
    let (m, mut f) = fixture();
    f.blocks[0]
        .params
        .extend([(v(9), Ty::Ptr), (v(20), Ty::Ptr)]);
    let mut borrow = InstrNode::new(Inst::Borrow { ptr: v(10) });
    borrow.results = vec![v(20), v(9)];
    f.blocks[0].body.insert(1, borrow);
    run(&m, &f);
    let reason = node_access(&m, &f, 0, 0).unwrap_err();
    assert!(reason.contains("%9 is defined more than once"));
}
#[test]
fn repeated_alloca_result_preserves_last_full_slot_and_first_duplicate_reason() {
    let (m, mut f) = fixture();
    f.blocks[0]
        .body
        .insert(1, allocation(Ty::Struct(StructId::new(0)), None, None, 10));
    run(&m, &f);
    assert!(
        node_access(&m, &f, 0, 1)
            .unwrap_err()
            .contains("defined more than once")
    );
}
#[test]
fn stored_pointer_as_value_reason_precedes_same_node_type_mismatch() {
    let (m, mut f) = fixture();
    f.blocks[0].body[1] = store(Ty::Ptr, 10, 10);
    run(&m, &f);
    assert!(
        node_access(&m, &f, 0, 0)
            .unwrap_err()
            .contains("stored AS A VALUE")
    );
}
#[test]
fn real_copy_select_and_return_pointer_escapes_match_original_reasons() {
    let (m, base) = fixture();
    for inst in [
        Inst::Copy {
            ty: Ty::Ptr,
            operand: v(10),
        },
        Inst::Select {
            ty: Ty::Ptr,
            cond: v(0),
            then_val: v(10),
            else_val: v(99),
        },
        Inst::Return {
            values: vec![v(10)],
        },
    ] {
        let mut f = base.clone();
        if matches!(&inst, Inst::Return { .. }) {
            let terminator = f.blocks[0]
                .body
                .last_mut()
                .expect("real fixture has a final terminator");
            assert!(matches!(&terminator.inst, Inst::Return { .. }));
            *terminator = InstrNode::new(inst);
        } else {
            f.blocks[0].body.insert(1, InstrNode::new(inst));
        }
        run(&m, &f);
        assert!(
            node_access(&m, &f, 0, 0)
                .unwrap_err()
                .contains("escapes into")
        );
    }
}
#[test]
fn wrong_load_and_store_types_unseal_the_complete_slot_without_shorter_reason() {
    let (m, base) = fixture();
    for node in [store(Ty::Bool, 10, 0), load(Ty::Bool, 10, 20)] {
        let mut f = base.clone();
        f.blocks[0].body[1] = node;
        run(&m, &f);
        let e = node_access(&m, &f, 0, 0).unwrap_err();
        assert!(e.contains("not at the slot's own type"));
    }
}
#[test]
fn store_value_must_have_the_exact_handle_type_independent_of_pointer_sealing() {
    let (m, mut f) = fixture();
    if let Inst::Store { value, .. } = &mut f.blocks[0].body[1].inst {
        *value = v(99);
    }
    run(&m, &f);
    assert!(
        node_access(&m, &f, 0, 1)
            .unwrap_err()
            .contains("needs a value of exactly that type")
    );
}
#[test]
fn volatile_accesses_remain_refused_without_removing_original_store_points() {
    let (m, mut f) = fixture();
    if let Inst::Store { volatile, .. } = &mut f.blocks[0].body[1].inst {
        *volatile = true;
    }
    if let Inst::Load { volatile, .. } = &mut f.blocks[0].body[2].inst {
        *volatile = true;
    }
    run(&m, &f);
    for i in [1, 2] {
        assert!(
            node_access(&m, &f, 0, i)
                .unwrap_err()
                .contains("may not be volatile")
        );
    }
}
#[test]
fn stronger_allocation_alignment_is_allowed_but_access_alignment_must_be_exact() {
    let (m, mut f) = fixture();
    if let Inst::Alloca { align, .. } = &mut f.blocks[0].body[0].inst {
        *align = Some(16);
    }
    run(&m, &f);
    assert_eq!(node_access(&m, &f, 0, 0), Ok(()));
    for align in [None, Some(8), Some(16), Some(3)] {
        if let Inst::Load { align: actual, .. } = &mut f.blocks[0].body[2].inst {
            *actual = align;
        }
        let r = node_access(&m, &f, 0, 2);
        assert_eq!(r.is_ok(), align.is_none() || align == Some(8));
    }
}
#[test]
fn counted_under_aligned_and_non_power_of_two_allocations_keep_shape_refusals() {
    let (m, base) = fixture();
    for (count, align, needle) in [
        (Some(v(0)), None, "dynamic count"),
        (None, Some(4), "power of two"),
        (None, Some(12), "power of two"),
    ] {
        let mut f = base.clone();
        f.blocks[0].body[0] = allocation(handle(), count, align, 10);
        run(&m, &f);
        assert!(node_access(&m, &f, 0, 0).unwrap_err().contains(needle));
    }
}
#[test]
fn absent_analysis_unknown_pointer_and_non_single_result_never_create_slots() {
    let (m, mut f) = fixture();
    let n = &f.blocks[0].body[2];
    assert!(
        access(&m, &f, &n.inst, &n.results, (f.entry, 2), false)
            .0
            .is_err()
    );
    assert!(
        access(
            &m,
            &f,
            &Inst::Load {
                ty: handle(),
                ptr: v(99),
                volatile: false,
                align: None
            },
            &[v(20)],
            (f.entry, 2),
            true
        )
        .0
        .is_err()
    );
    f.blocks[0].body[0].results = vec![v(10), v(11)];
    run(&m, &f);
    assert!(
        node_access(&m, &f, 0, 0)
            .unwrap_err()
            .contains("no single slot pointer")
    );
}
#[test]
fn diamond_arm_stores_do_not_individually_dominate_the_join_read() {
    let (m, mut f) = fixture();
    f.blocks[0].body = vec![
        allocation(handle(), None, None, 10),
        InstrNode::new(Inst::CondBr {
            cond: v(0),
            then_target: BlockId::new(2),
            then_args: vec![],
            else_target: BlockId::new(3),
            else_args: vec![],
        }),
    ];
    for id in [2, 3] {
        let mut b = Block::new(BlockId::new(id));
        b.body = vec![store(handle(), 10, 0), branch(4)];
        f.blocks.push(b);
    }
    let mut join = Block::new(BlockId::new(4));
    join.body = vec![load(handle(), 10, 20), finish()];
    f.blocks.push(join);
    run(&m, &f);
    assert!(
        node_access(&m, &f, 3, 0)
            .unwrap_err()
            .contains("not dominated by a store")
    );
}
#[test]
fn store_before_fresh_loop_allocation_cannot_initialize_its_instance() {
    let (m, mut f) = fixture();
    f.blocks[0].body = vec![
        store(handle(), 10, 0),
        allocation(handle(), None, None, 10),
        load(handle(), 10, 20),
        branch(1),
    ];
    run(&m, &f);
    assert!(
        node_access(&m, &f, 0, 2)
            .unwrap_err()
            .contains("definition does not dominate")
    );
}
#[test]
fn unreachable_or_malformed_cfg_later_use_fails_closed() {
    let (m, mut f) = fixture();
    f.entry = BlockId::new(999);
    run(&m, &f);
    assert!(node_access(&m, &f, 0, 2).is_err());
}
#[test]
fn declared_struct_has_real_layout_while_undeclared_tuple_stays_semantic_error() {
    let (m, mut f) = fixture();
    let ty = Ty::Struct(StructId::new(0));
    f.blocks[0].params[0].1 = ty.clone();
    f.blocks[0].body = vec![
        allocation(ty.clone(), None, None, 10),
        store(ty.clone(), 10, 0),
        load(ty, 10, 20),
        finish(),
    ];
    run(&m, &f);
    assert_eq!(node_access(&m, &f, 0, 2), Ok(()));
    f.blocks[0].body[0] = allocation(Ty::Tuple(vec![handle(), Ty::Bool]), None, None, 10);
    run(&m, &f);
    assert!(
        node_access(&m, &f, 0, 0)
            .unwrap_err()
            .contains("no computable layout")
    );
}
#[test]
fn scalar_only_function_retains_empty_analysis_and_false_allocation_predicate() {
    let (m, mut f) = fixture();
    f.blocks[0].body = vec![allocation(Ty::Bool, None, None, 10), finish()];
    run(&m, &f);
}
