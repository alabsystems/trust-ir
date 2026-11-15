// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn check<O: ExecutionObserver>(
        &mut self,
        block: u32,
        instruction: &Inst,
        values: &ObservedValueTypes,
        module: Option<&Module>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(67, 0)?;
        match instruction {
            Inst::Load { ptr, .. } => self.pointer(block, "load", *ptr, values, work)?,
            Inst::Store { ty, value, .. } => self.operand(
                block,
                "store",
                "value",
                *value,
                ty,
                Refinement::Consumption,
                values,
                work,
            )?,
            Inst::CondBr { cond, .. } => self.boolean(block, None, *cond, values, work)?,
            Inst::Assume { cond } => self.boolean(block, Some("assume"), *cond, values, work)?,
            Inst::Assert { cond, kind, .. } | Inst::AssertInvoke { cond, kind, .. } => {
                self.boolean(block, Some("assert"), *cond, values, work)?;
                // Both original helpers are fixed seven-kind discriminant
                // tables returning at most the two stored SSA message fields.
                work.admit(
                    14,
                    size_of::<Option<[ValueId; 2]>>() + size_of::<Option<[&str; 2]>>(),
                )?;
                if let (Some(operands), Some(roles)) = (kind.operands(), kind.operand_roles()) {
                    let mut index = 0usize;
                    while index < 2 {
                        work.admit(1, size_of::<ValueId>() + size_of::<&str>())?;
                        self.operand(
                            block,
                            "assert",
                            roles[index],
                            operands[index],
                            &Ty::Usize,
                            Refinement::Exact,
                            values,
                            work,
                        )?;
                        index += 1;
                    }
                }
            }
            Inst::Dealloc { ptr } => self.pointer(block, "dealloc", *ptr, values, work)?,
            Inst::MemCopy {
                dst, src, bytes, ..
            } => {
                self.pointer(block, "memcopy", *dst, values, work)?;
                self.pointer(block, "memcopy", *src, values, work)?;
                self.byte_count(block, "memcopy", *bytes, values, module, work)?;
            }
            Inst::MemSet { dst, byte, bytes } => {
                self.pointer(block, "memset", *dst, values, work)?;
                self.operand(
                    block,
                    "memset",
                    "byte",
                    *byte,
                    &Ty::U8,
                    Refinement::Exact,
                    values,
                    work,
                )?;
                self.byte_count(block, "memset", *bytes, values, module, work)?;
            }
            Inst::CoroSuspend { frame, .. } => {
                self.pointer(block, "coro_suspend", *frame, values, work)?
            }
            Inst::GEP { base, indices, .. } => {
                self.pointer(block, "gep", *base, values, work)?;
                self.indices(block, indices, values, work)?;
            }
            Inst::AtomicLoad { ptr, ordering, .. } => {
                self.pointer(block, "atomic_load", *ptr, values, work)?;
                self.ordering(
                    block,
                    "atomic_load",
                    "ordering",
                    *ordering,
                    AtomicRole::Load,
                    work,
                )?;
            }
            Inst::AtomicStore {
                ty,
                ptr,
                value,
                ordering,
            } => {
                self.pointer(block, "atomic_store", *ptr, values, work)?;
                self.ordering(
                    block,
                    "atomic_store",
                    "ordering",
                    *ordering,
                    AtomicRole::Store,
                    work,
                )?;
                self.operand(
                    block,
                    "atomic_store",
                    "value",
                    *value,
                    ty,
                    Refinement::Consumption,
                    values,
                    work,
                )?;
            }
            Inst::AtomicRMW { ty, ptr, value, .. } => {
                self.pointer(block, "atomic_rmw", *ptr, values, work)?;
                self.operand(
                    block,
                    "atomic_rmw",
                    "value",
                    *value,
                    ty,
                    Refinement::Consumption,
                    values,
                    work,
                )?;
            }
            Inst::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                failure,
                ..
            } => {
                self.pointer(block, "cmpxchg", *ptr, values, work)?;
                self.ordering(
                    block,
                    "cmpxchg",
                    "failure ordering",
                    *failure,
                    AtomicRole::Load,
                    work,
                )?;
                self.operand(
                    block,
                    "cmpxchg",
                    "expected",
                    *expected,
                    ty,
                    Refinement::Consumption,
                    values,
                    work,
                )?;
                self.operand(
                    block,
                    "cmpxchg",
                    "desired",
                    *desired,
                    ty,
                    Refinement::Consumption,
                    values,
                    work,
                )?;
            }
            Inst::Copy { ty, operand } => self.operand(
                block,
                "copy",
                "operand",
                *operand,
                ty,
                Refinement::Exact,
                values,
                work,
            )?,
            Inst::Borrow { ptr } => self.pointer(block, "borrow", *ptr, values, work)?,
            Inst::BorrowMut { ptr } => self.pointer(block, "borrow_mut", *ptr, values, work)?,
            Inst::EndBorrow { borrow_ptr } => {
                self.pointer(block, "end_borrow", *borrow_ptr, values, work)?
            }
            Inst::Retain { ptr } => self.pointer(block, "retain", *ptr, values, work)?,
            Inst::Release { ptr } => self.pointer(block, "release", *ptr, values, work)?,
            Inst::IsUnique { ptr } => self.pointer(block, "is_unique", *ptr, values, work)?,
            // Exact unowned cases: their numeric/cast/fat-pointer/select/
            // element/vector/other rules are separate original constituents.
            Inst::BinOp { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::SeqMap { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Alloca { .. }
            | Inst::HeapAlloc { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. }
            | Inst::Fence { .. }
            | Inst::Br { .. }
            | Inst::Switch { .. }
            | Inst::Call { .. }
            | Inst::CallIndirect { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::Return { .. }
            | Inst::Drop { .. }
            | Inst::DropInvoke { .. }
            | Inst::MakeAggregate { .. }
            | Inst::MakeClosure { .. }
            | Inst::ArraySplat { .. }
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::ExtractField { .. }
            | Inst::InsertField { .. }
            | Inst::ExtractElement { .. }
            | Inst::InsertElement { .. }
            | Inst::Const { .. }
            | Inst::NullPtr
            | Inst::GlobalAddr { .. }
            | Inst::Undef { .. }
            | Inst::Select { .. }
            | Inst::Unreachable
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::Invoke { .. }
            | Inst::InvokeIndirect { .. }
            | Inst::LandingPad { .. }
            | Inst::Resume { .. }
            | Inst::DialectOp(_) => {}
        }
        Ok(())
    }
}
