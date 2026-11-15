// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

pub(super) fn all() -> Vec<Inst> {
    let mut all = arithmetic();
    all.extend(memory());
    all.extend(aggregate());
    all
}
fn arithmetic() -> Vec<Inst> {
    vec![
        Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: v(1),
            rhs: v(1),
        },
        Inst::SeqMapAddK {
            ty: Ty::Sequence(TyId::new(8)),
            seq: v(1),
            k: 1,
        },
        Inst::SeqMapNot {
            ty: Ty::Sequence(TyId::new(8)),
            seq: v(1),
        },
        Inst::SeqMap {
            ty: Ty::Sequence(TyId::new(8)),
            seq: v(1),
            fwd: FuncId::new(9),
        },
        Inst::UnOp {
            op: UnOp::Not,
            ty: Ty::U32,
            operand: v(1),
        },
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::U32,
            lhs: v(1),
            rhs: v(1),
        },
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::U32,
            lhs: v(1),
            rhs: v(1),
        },
        Inst::FCmp {
            op: FCmpOp::OEq,
            ty: Ty::F32,
            lhs: v(1),
            rhs: v(1),
        },
        Inst::Copy {
            ty: Ty::U32,
            operand: v(1),
        },
        Inst::Select {
            ty: Ty::U32,
            cond: v(1),
            then_val: v(1),
            else_val: v(1),
        },
    ]
}
fn memory() -> Vec<Inst> {
    vec![
        Inst::Drop {
            ty: Ty::U32,
            ptr: v(1),
        },
        Inst::DropInvoke {
            ty: Ty::U32,
            ptr: v(1),
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(2),
        },
        Inst::Load {
            ty: Ty::U32,
            ptr: v(1),
            volatile: true,
            align: Some(4),
        },
        Inst::Store {
            ty: Ty::U32,
            ptr: v(1),
            value: v(1),
            volatile: false,
            align: None,
        },
        Inst::Alloca {
            ty: Ty::U32,
            count: Some(v(1)),
            align: None,
        },
        Inst::HeapAlloc {
            ty: Ty::U32,
            count: None,
            align: None,
            origin: AllocOrigin::RustHeap,
        },
        Inst::AtomicLoad {
            ty: Ty::U32,
            ptr: v(1),
            ordering: Ordering::Acquire,
        },
        Inst::AtomicStore {
            ty: Ty::U32,
            ptr: v(1),
            value: v(1),
            ordering: Ordering::Release,
        },
        Inst::AtomicRMW {
            op: AtomicRMWOp::Xchg,
            ty: Ty::U32,
            ptr: v(1),
            value: v(1),
            ordering: Ordering::SeqCst,
        },
        Inst::CmpXchg {
            ty: Ty::U32,
            ptr: v(1),
            expected: v(1),
            desired: v(1),
            success: Ordering::SeqCst,
            failure: Ordering::Relaxed,
            weak: false,
        },
        Inst::LoadSlot {
            frame: v(1),
            slot: 5,
            ty: Ty::U32,
        },
    ]
}
fn aggregate() -> Vec<Inst> {
    vec![
        Inst::MakeAggregate {
            ty: Ty::Tuple(vec![Ty::U32]),
            variant: None,
            fields: vec![v(1)],
        },
        Inst::ArraySplat {
            ty: Ty::Array(TyId::new(8), u64::MAX),
            value: v(1),
        },
        Inst::ExtractField {
            ty: Ty::U32,
            aggregate: v(1),
            field: 0,
        },
        Inst::InsertField {
            ty: Ty::U32,
            aggregate: v(1),
            field: 0,
            value: v(1),
        },
        Inst::ExtractElement {
            ty: Ty::U32,
            array: v(1),
            index: v(1),
        },
        Inst::InsertElement {
            ty: Ty::U32,
            array: v(1),
            index: v(1),
            value: v(1),
        },
        Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(0),
        },
        Inst::Undef { ty: Ty::U32 },
    ]
}
