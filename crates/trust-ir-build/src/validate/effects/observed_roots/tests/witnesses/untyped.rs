// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

pub(super) fn all() -> Vec<Inst> {
    let mut all = calls();
    all.extend(branches());
    all.extend(other());
    all
}
fn calls() -> Vec<Inst> {
    let site = PanicSite {
        entry: FuncId::new(9),
        location: PanicLocation::Value(v(1)),
    };
    vec![
        Inst::Call {
            callee: FuncId::new(9),
            args: vec![v(1)],
        },
        Inst::CallCannotUnwind {
            callee: FuncId::new(9),
            args: vec![v(1)],
        },
        Inst::CallIndirect {
            callee: v(1),
            sig: FuncTyId::new(8),
            args: vec![v(1)],
            calling_conv: trust_ir::CallingConv::C,
        },
        Inst::CallIndirectCannotUnwind {
            callee: v(1),
            sig: FuncTyId::new(8),
            args: vec![v(1)],
            calling_conv: trust_ir::CallingConv::C,
        },
        Inst::Invoke {
            callee: FuncId::new(9),
            args: vec![v(1)],
            normal_dest: BlockId::new(1),
            normal_args: vec![v(1)],
            unwind_dest: BlockId::new(2),
        },
        Inst::InvokeIndirect {
            callee: v(1),
            sig: FuncTyId::new(8),
            args: vec![v(1)],
            calling_conv: trust_ir::CallingConv::C,
            normal_dest: BlockId::new(1),
            normal_args: vec![v(1)],
            unwind_dest: BlockId::new(2),
        },
        Inst::Assert {
            cond: v(1),
            kind: AssertKind::NullPtr,
            site: Some(site),
        },
        Inst::AssertInvoke {
            cond: v(1),
            kind: AssertKind::DivByZero,
            site,
            normal_dest: BlockId::new(1),
            normal_args: vec![v(1)],
            unwind_dest: BlockId::new(2),
        },
    ]
}
fn branches() -> Vec<Inst> {
    vec![
        Inst::Br {
            target: BlockId::new(1),
            args: vec![v(1)],
        },
        Inst::CondBr {
            cond: v(1),
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![v(1)],
        },
        Inst::Switch {
            value: v(1),
            default: BlockId::new(1),
            default_args: vec![],
            exhaustive_enum_unreachable: false,
            cases: vec![SwitchCase {
                value: Constant::Int(0),
                target: BlockId::new(2),
                args: vec![v(1)],
            }],
        },
        Inst::Return { values: vec![v(1)] },
        Inst::Unreachable,
        Inst::CoroSuspend {
            frame: v(1),
            state_slot: 1,
            next_state: 2,
            value: v(1),
        },
        Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![4, 4],
        },
        Inst::Resume { exn: v(1) },
    ]
}
fn other() -> Vec<Inst> {
    vec![
        Inst::Fence {
            ordering: Ordering::SeqCst,
        },
        Inst::NullPtr,
        Inst::GlobalAddr {
            global: GlobalId::new(8),
        },
        Inst::Assume { cond: v(1) },
        Inst::Borrow { ptr: v(1) },
        Inst::BorrowMut { ptr: v(1) },
        Inst::EndBorrow { borrow_ptr: v(1) },
        Inst::Retain { ptr: v(1) },
        Inst::Release { ptr: v(1) },
        Inst::IsUnique { ptr: v(1) },
        Inst::Dealloc { ptr: v(1) },
        Inst::MemCopy {
            dst: v(1),
            src: v(1),
            bytes: v(1),
            overlap: true,
        },
        Inst::MemSet {
            dst: v(1),
            byte: v(1),
            bytes: v(1),
        },
        Inst::BindSlot {
            frame: v(1),
            slot: 1,
            value: v(1),
        },
        Inst::CloseFrame { frame: v(1) },
    ]
}
