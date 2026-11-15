// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn only_gep_copy_and_ptrtoptr_preserve_local_alloca_roots() {
    let f = function(vec![
        node(alloca(), &[10]),
        node(
            Inst::GEP {
                pointee_ty: Ty::U32,
                base: v(10),
                indices: vec![v(1)],
                inbounds: false,
            },
            &[11],
        ),
        node(copy(11), &[12]),
        node(
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Ptr,
                operand: v(12),
            },
            &[13],
        ),
        node(load(13), &[]),
        node(store(13), &[]),
    ]);
    assert!(parity(&f, None).is_empty());
    let mut nonlocal = f.clone();
    nonlocal.blocks[0].body[0] = node(copy(1), &[10]);
    assert_eq!(parity(&nonlocal, None).len(), 2);
}
#[test]
fn select_load_borrow_pointer_parts_integer_roundtrip_and_call_results_are_opaque_roots() {
    let opaque = [
        Inst::Select {
            ty: Ty::Ptr,
            cond: v(1),
            then_val: v(10),
            else_val: v(10),
        },
        load(10),
        Inst::Borrow { ptr: v(10) },
        Inst::PtrData {
            ptr_ty: Ty::Ptr,
            ptr: v(10),
        },
        Inst::PtrFromParts {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Unit,
            data: v(10),
            metadata: v(10),
        },
        Inst::Cast {
            op: CastOp::IntToPtr,
            src_ty: Ty::Usize,
            dst_ty: Ty::Ptr,
            operand: v(10),
        },
        Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        },
    ];
    let mut module = Module::new("opaque-roots");
    module.functions.push(callee(9, "pure", true, false));
    for root in opaque {
        let f = function(vec![
            node(alloca(), &[10]),
            node(root, &[20]),
            node(store(20), &[]),
        ]);
        let errors = parity(&f, Some(&module));
        assert_eq!(errors.len(), 1);
        assert!(text(&errors[0]).starts_with("store (writes"));
    }
}
#[test]
fn every_duplicate_definition_participates_and_every_result_id_has_a_definition() {
    let f = function(vec![
        node(alloca(), &[10, 11]),
        node(alloca(), &[10]),
        node(store(10), &[]),
        node(store(11), &[]),
    ]);
    assert!(parity(&f, None).is_empty());
    let mut f = f;
    f.blocks[0].body.insert(
        1,
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(0),
            },
            &[10],
        ),
    );
    assert_eq!(parity(&f, None).len(), 1);
    f.blocks[0].params.push((v(11), Ty::Ptr));
    assert_eq!(parity(&f, None).len(), 2);
}
#[test]
fn missing_cycles_and_repeated_convergence_remain_unknown_roots() {
    let fixtures = [
        vec![node(store(99), &[])],
        vec![
            node(copy(11), &[10]),
            node(copy(10), &[11]),
            node(store(10), &[]),
        ],
        vec![
            node(alloca(), &[10]),
            node(copy(10), &[20]),
            node(copy(10), &[20]),
            node(store(20), &[]),
        ],
        vec![
            node(alloca(), &[10]),
            node(copy(20), &[20]),
            node(copy(10), &[20]),
            node(store(20), &[]),
        ],
    ];
    for nodes in fixtures {
        let errors = parity(&function(nodes), None);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            text(&errors[0]),
            "store (writes memory not rooted at a local alloca)"
        );
    }
}
#[test]
fn block_parameters_stay_opaque_even_with_only_local_alloca_incoming_arguments() {
    let mut f = function(vec![
        node(alloca(), &[10]),
        node(
            Inst::Br {
                target: BlockId::new(3),
                args: vec![v(10)],
            },
            &[],
        ),
    ]);
    let mut next = Block::new(BlockId::new(3));
    next.params.push((v(20), Ty::Ptr));
    next.body.push(node(store(20), &[]));
    f.blocks.push(next);
    assert_eq!(parity(&f, None).len(), 1);
}
