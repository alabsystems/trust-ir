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
            Inst::BinOp { op, ty, lhs, rhs } => {
                self.binary(block, *op, ty, *lhs, *rhs, values, module, work)?
            }
            Inst::UnOp { op, ty, operand } => self.unary(block, *op, ty, *operand, values, work)?,
            Inst::ICmp { ty, lhs, rhs, .. } => {
                self.integer_compare(block, ty, *lhs, *rhs, values, work)?
            }
            Inst::FCmp { ty, lhs, rhs, .. } => {
                self.float_compare(block, ty, *lhs, *rhs, values, work)?
            }
            Inst::Overflow { op, ty, lhs, rhs } => {
                self.overflow(block, *op, ty, *lhs, *rhs, values, work)?
            }
            // Other actual type-pass checks remain separate original constituents.
            Inst::Alloca { .. }
            | Inst::ArraySplat { .. }
            | Inst::Assert { .. }
            | Inst::AssertInvoke { .. }
            | Inst::Assume { .. }
            | Inst::AtomicLoad { .. }
            | Inst::AtomicRMW { .. }
            | Inst::AtomicStore { .. }
            | Inst::BindSlot { .. }
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::Br { .. }
            | Inst::Call { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirect { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::Cast { .. }
            | Inst::CloseFrame { .. }
            | Inst::CmpXchg { .. }
            | Inst::CondBr { .. }
            | Inst::Const { .. }
            | Inst::Copy { .. }
            | Inst::CoroSuspend { .. }
            | Inst::Dealloc { .. }
            | Inst::DialectOp(_)
            | Inst::Drop { .. }
            | Inst::DropInvoke { .. }
            | Inst::EndBorrow { .. }
            | Inst::ExtractElement { .. }
            | Inst::ExtractField { .. }
            | Inst::Fence { .. }
            | Inst::GEP { .. }
            | Inst::GlobalAddr { .. }
            | Inst::HeapAlloc { .. }
            | Inst::InsertElement { .. }
            | Inst::InsertField { .. }
            | Inst::Invoke { .. }
            | Inst::InvokeIndirect { .. }
            | Inst::IsUnique { .. }
            | Inst::LandingPad { .. }
            | Inst::Load { .. }
            | Inst::LoadSlot { .. }
            | Inst::MakeAggregate { .. }
            | Inst::MakeClosure { .. }
            | Inst::MemCopy { .. }
            | Inst::MemSet { .. }
            | Inst::NullPtr
            | Inst::OpenFrame { .. }
            | Inst::PtrData { .. }
            | Inst::PtrFromParts { .. }
            | Inst::PtrMetadata { .. }
            | Inst::Release { .. }
            | Inst::Resume { .. }
            | Inst::Retain { .. }
            | Inst::Return { .. }
            | Inst::Select { .. }
            | Inst::SeqMap { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::Store { .. }
            | Inst::Switch { .. }
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::Undef { .. }
            | Inst::Unreachable => {}
        }
        Ok(())
    }
}
