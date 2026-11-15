// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[derive(Clone, Copy)]
pub(super) enum Inferred<'a> {
    Borrowed(&'a Ty),
    Comparison(&'a Ty),
    Closure(trust_ir::value::ClosureTyId),
    Bool,
    Ptr,
}

impl Inferred<'_> {
    pub(super) fn make<O: ExecutionObserver>(self, work: &mut Work<'_, '_, O>) -> R<Ty> {
        if let Self::Borrowed(ty) = self {
            return ty.clone_observed(work.session, work.site);
        }
        work.admit(1, 0)?;
        if let Self::Comparison(Ty::Vector(_, lanes)) = self {
            let bytes = size_of::<Ty>()
                .checked_mul(2)
                .and_then(|n| n.checked_add(2 * align_of::<Ty>()))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            work.admit(2, bytes)?;
            return Ok(Ty::Vector(Box::new(Ty::Bool), *lanes));
        }
        work.admit(1, size_of::<Ty>())?;
        Ok(match self {
            Self::Ptr => Ty::Ptr,
            Self::Closure(id) => Ty::Closure(id),
            Self::Bool | Self::Comparison(_) => Ty::Bool,
            Self::Borrowed(_) => return Err(ObservedValueError::InvalidRange),
        })
    }
}

pub(super) fn for_instruction<'a, O: ExecutionObserver>(
    instruction: &'a Inst,
    work: &mut Work<'_, '_, O>,
) -> R<Option<Inferred<'a>>> {
    work.admit(67, size_of::<Option<Inferred<'_>>>())?;
    Ok(match instruction {
        Inst::MakeClosure { ty, .. } => Some(Inferred::Closure(*ty)),
        Inst::BinOp { ty, .. }
        | Inst::SeqMapAddK { ty, .. }
        | Inst::SeqMapNot { ty, .. }
        | Inst::SeqMap { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::MakeAggregate { ty, .. }
        | Inst::ArraySplat { ty, .. }
        | Inst::TensorContract { ty, .. }
        | Inst::TensorMap { ty, .. }
        | Inst::TensorReduce { ty, .. }
        | Inst::TensorView { ty, .. }
        | Inst::TensorGather { ty, .. }
        | Inst::TensorScatter { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Const { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. }
        | Inst::PtrMetadata {
            metadata_ty: ty, ..
        }
        | Inst::PtrFromParts { ptr_ty: ty, .. } => Some(Inferred::Borrowed(ty)),
        Inst::Cast { dst_ty, .. } => Some(Inferred::Borrowed(dst_ty)),
        Inst::ICmp { ty, .. } | Inst::FCmp { ty, .. } => Some(Inferred::Comparison(ty)),
        Inst::IsUnique { .. } => Some(Inferred::Bool),
        Inst::Alloca { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. } => Some(Inferred::Ptr),
        Inst::DialectOp(op) => {
            if op.result_tys.len() == 1 {
                Some(Inferred::Borrowed(&op.result_tys[0]))
            } else {
                None
            }
        }
        Inst::Drop { .. }
        | Inst::DropInvoke { .. }
        | Inst::Overflow { .. }
        | Inst::CmpXchg { .. }
        | Inst::Call { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::Invoke { .. }
        | Inst::CallIndirect { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::InvokeIndirect { .. }
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
        | Inst::Resume { .. }
        | Inst::LandingPad { .. } => None,
    })
}
