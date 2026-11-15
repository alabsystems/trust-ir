// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use trust_ir::value::FuncTyId;

fn signature<O: ExecutionObserver>(
    module: &Module,
    id: FuncTyId,
    work: &mut Work<'_, '_, O>,
) -> R<usize> {
    work.admit(1, size_of::<Option<&FuncTy>>() + size_of::<usize>())?;
    Ok(module
        .func_types
        .get(id.as_usize())
        .map_or(0, |signature| signature.returns.len()))
}

fn direct<O: ExecutionObserver>(
    module: &Module,
    id: FuncId,
    work: &mut Work<'_, '_, O>,
) -> R<usize> {
    work.admit(2, size_of::<Option<&Function>>())?;
    if let Some(function) = module.functions.get(id.as_usize())
        && function.id == id
    {
        return signature(module, function.ty, work);
    }
    let mut index = 0;
    loop {
        work.admit(1, 0)?;
        let Some(function) = module.functions.get(index) else {
            return Ok(0);
        };
        if function.id == id {
            return signature(module, function.ty, work);
        }
        index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
}

pub(super) fn expected<O: ExecutionObserver>(
    instruction: &Inst,
    module: &Module,
    work: &mut Work<'_, '_, O>,
) -> R<usize> {
    work.admit(67, size_of::<usize>())?;
    Ok(match instruction {
        Inst::BinOp { .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::SeqMap { .. }
        | Inst::UnOp { .. }
        | Inst::Load { .. }
        | Inst::AtomicLoad { .. }
        | Inst::AtomicRMW { .. }
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
        | Inst::Undef { .. }
        | Inst::Copy { .. }
        | Inst::Select { .. }
        | Inst::LoadSlot { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::Cast { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::IsUnique { .. }
        | Inst::Alloca { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. } => 1,
        Inst::Overflow { .. } | Inst::CmpXchg { .. } | Inst::LandingPad { .. } => 2,
        Inst::Call { callee, .. }
        | Inst::CallCannotUnwind { callee, .. }
        | Inst::Invoke { callee, .. } => direct(module, *callee, work)?,
        Inst::CallIndirect { sig, .. }
        | Inst::CallIndirectCannotUnwind { sig, .. }
        | Inst::InvokeIndirect { sig, .. } => signature(module, *sig, work)?,
        Inst::DialectOp(op) => op.result_tys.len(),
        Inst::Drop { .. }
        | Inst::DropInvoke { .. }
        | Inst::Store { .. }
        | Inst::AtomicStore { .. }
        | Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Return { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::AssertInvoke { .. }
        | Inst::Unreachable
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::Dealloc { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::Resume { .. } => 0,
    })
}
