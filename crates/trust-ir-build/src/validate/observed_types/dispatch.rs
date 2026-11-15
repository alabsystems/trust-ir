// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
fn route(instruction: &Inst) -> (Route, Option<&Ty>) {
    match instruction {
        Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::ICmp { ty, .. }
        | Inst::FCmp { ty, .. }
        | Inst::Overflow { ty, .. } => (Route::Numeric, Some(ty)),
        Inst::Store { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicStore { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::CmpXchg { ty, .. }
        | Inst::Copy { ty, .. } => (Route::Basic, Some(ty)),
        Inst::Alloca { ty, .. } => (Route::None, Some(ty)),
        Inst::Select { ty, .. } => (Route::PointerSelect, Some(ty)),
        Inst::Cast { .. } => (Route::Cast, None),
        Inst::PtrData { .. } | Inst::PtrMetadata { .. } | Inst::PtrFromParts { .. } => {
            (Route::PointerSelect, None)
        }
        Inst::ExtractElement { .. } | Inst::InsertElement { .. } => (Route::Element, None),
        // The tensor region: the original's static contraction rules
        // (`check_tensor_contract`) have no observed constituent yet.
        Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. } => (Route::Unsupported, None),
        Inst::CondBr { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::AssertInvoke { .. }
        | Inst::Dealloc { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::CoroSuspend { .. }
        | Inst::GEP { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. } => (Route::Basic, None),
        Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::SeqMap { .. }
        | Inst::HeapAlloc { .. }
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
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::Const { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Unreachable
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::Invoke { .. }
        | Inst::InvokeIndirect { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. }
        | Inst::DialectOp(_) => (Route::None, None),
    }
}
impl State {
    pub(super) fn instruction<O: ExecutionObserver>(
        &mut self,
        block: u32,
        instruction: &Inst,
        context: ValidationContext<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(67, size_of::<(Route, Option<&Ty>)>())?;
        let (selected, vector) = route(instruction);
        if let Some(ty) = vector {
            self.vector(ty, block, work)?;
        }
        self.prepare(work)?;
        let values = self
            .values
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        self.pending = match selected {
            Route::Numeric => validate_instruction_numeric_type_operands_observed(
                block,
                instruction,
                values,
                context.module,
                work.session,
                work.site,
            )?,
            Route::Basic => validate_instruction_basic_type_operands_observed(
                block,
                instruction,
                values,
                context.module,
                work.session,
                work.site,
            )?,
            Route::PointerSelect => {
                super::super::observed_pointer_select::validate_pointer_select_operands_observed(
                    block,
                    instruction,
                    values,
                    context.pointer_bits,
                    work.session,
                    work.site,
                )?
            }
            Route::Element => {
                super::super::observed_element_operands::validate_element_operands_observed(
                    block,
                    instruction,
                    values,
                    &self.constants,
                    context.module,
                    work.session,
                    work.site,
                )?
            }
            Route::Cast => {
                let Inst::Cast {
                    op,
                    src_ty,
                    dst_ty,
                    operand,
                } = instruction
                else {
                    return Err(ObservedValueError::InvalidRange);
                };
                super::super::observed_cast_operands::validate_cast_operands_observed(
                    block,
                    *op,
                    src_ty,
                    dst_ty,
                    *operand,
                    values,
                    context.cast_mode,
                    work.session,
                    work.site,
                )?
            }
            Route::Unsupported => return Err(ObservedValueError::UnsupportedValue),
            Route::None => return Ok(()),
        };
        self.append(work)
    }
}
