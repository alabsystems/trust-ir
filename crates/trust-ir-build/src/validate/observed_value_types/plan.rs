// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use trust_ir::value::FuncTyId;

#[derive(Clone, Copy)]
pub(super) enum Atom<'a> {
    Borrowed(&'a Ty),
    Comparison(&'a Ty),
    Closure(trust_ir::value::ClosureTyId),
    Bool,
    Ptr,
    I32,
}

#[derive(Clone, Copy)]
pub(super) enum Plan<'a> {
    All(Atom<'a>),
    One(Atom<'a>),
    Pair(Atom<'a>, Atom<'a>),
    Types(&'a [Ty]),
    Empty,
}

impl<'a> Plan<'a> {
    fn single(atom: Atom<'a>, context: Context<'_>) -> Self {
        match context {
            Context::Function => Self::All(atom),
            Context::Module(_) | Context::Catalog(_) => Self::One(atom),
        }
    }

    pub(super) fn at<O: ExecutionObserver>(
        self,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<Atom<'a>>> {
        work.admit(1, size_of::<Option<Atom<'_>>>())?;
        Ok(match self {
            Self::All(atom) => Some(atom),
            Self::One(atom) => (index == 0).then_some(atom),
            Self::Pair(first, second) => match index {
                0 => Some(first),
                1 => Some(second),
                _ => None,
            },
            Self::Types(types) => types.get(index).map(Atom::Borrowed),
            Self::Empty => None,
        })
    }
}

impl Atom<'_> {
    pub(super) fn clone_type<O: ExecutionObserver>(self, work: &mut Work<'_, '_, O>) -> R<Ty> {
        if let Self::Borrowed(ty) = self {
            return ty.clone_observed(work.session, work.site);
        }
        // A vector comparison result allocates one Bool child. Other comparison
        // payloads are not traversed by the ordinary comparison_result_ty rule.
        work.admit(1, 0)?;
        if let Self::Comparison(Ty::Vector(_, lanes)) = self {
            let bytes = size_of::<Ty>()
                .checked_mul(2)
                .and_then(|n| n.checked_add(2 * core::mem::align_of::<Ty>()))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            work.admit(2, bytes)?;
            return Ok(Ty::Vector(Box::new(Ty::Bool), *lanes));
        }
        work.admit(1, size_of::<Ty>())?;
        Ok(match self {
            Self::Bool | Self::Comparison(_) => Ty::Bool,
            Self::Ptr => Ty::Ptr,
            Self::Closure(id) => Ty::Closure(id),
            Self::I32 => Ty::I32,
            Self::Borrowed(_) => return Err(ObservedValueError::InvalidRange),
        })
    }
}

fn signature<'a, O: ExecutionObserver>(
    module: &'a Module,
    id: FuncTyId,
    work: &mut Work<'_, '_, O>,
) -> R<Plan<'a>> {
    work.admit(1, size_of::<Option<&FuncTy>>())?;
    Ok(match module.func_types.get(id.as_usize()) {
        Some(signature) => Plan::Types(&signature.returns),
        None => Plan::Empty,
    })
}

fn direct<'a, O: ExecutionObserver>(
    module: &'a Module,
    id: FuncId,
    work: &mut Work<'_, '_, O>,
) -> R<Plan<'a>> {
    // Preserve indexed-slot preference even for sparse duplicate function IDs.
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
            return Ok(Plan::Empty);
        };
        if function.id == id {
            return signature(module, function.ty, work);
        }
        index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
}

pub(super) fn for_instruction<'a, O: ExecutionObserver>(
    instruction: &'a Inst,
    context: Context<'a>,
    work: &mut Work<'_, '_, O>,
) -> R<Plan<'a>> {
    Ok(match instruction {
        Inst::MakeClosure { ty, .. } => Plan::single(Atom::Closure(*ty), context),
        Inst::BinOp { ty, .. }
        | Inst::SeqMapAddK { ty, .. }
        | Inst::SeqMapNot { ty, .. }
        | Inst::SeqMap { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::MakeAggregate { ty, .. }
        | Inst::ArraySplat { ty, .. }
        | Inst::TensorContract { ty, .. }
        | Inst::TensorMap { ty, .. }
        | Inst::TensorReduce { ty, .. }
        | Inst::TensorView { ty, .. }
        | Inst::TensorGather { ty, .. }
        | Inst::TensorScatter { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
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
        | Inst::PtrFromParts { ptr_ty: ty, .. }
        | Inst::BoxDeref { ptr_ty: ty, .. } => Plan::single(Atom::Borrowed(ty), context),
        Inst::Cast { dst_ty, .. } => Plan::single(Atom::Borrowed(dst_ty), context),
        Inst::ICmp { ty, .. } | Inst::FCmp { ty, .. } => {
            Plan::single(Atom::Comparison(ty), context)
        }
        Inst::Overflow { ty, .. } | Inst::CmpXchg { ty, .. } => {
            Plan::Pair(Atom::Borrowed(ty), Atom::Bool)
        }
        Inst::IsUnique { .. } => Plan::single(Atom::Bool, context),
        Inst::Alloca { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. } => Plan::single(Atom::Ptr, context),
        Inst::Call { callee, .. }
        | Inst::CallCannotUnwind { callee, .. }
        | Inst::Invoke { callee, .. } => match context {
            Context::Function => Plan::Empty,
            Context::Module(module) => direct(module, *callee, work)?,
            Context::Catalog(catalog) => {
                match catalog.unique_observed(*callee, work.session, work.site)? {
                    Some(function) => signature(catalog.source_module(), function.ty, work)?,
                    None => Plan::Empty,
                }
            }
        },
        Inst::CallIndirect { sig, .. }
        | Inst::CallIndirectCannotUnwind { sig, .. }
        | Inst::InvokeIndirect { sig, .. } => match context {
            Context::Function => Plan::Empty,
            Context::Module(module) => signature(module, *sig, work)?,
            Context::Catalog(catalog) => signature(catalog.source_module(), *sig, work)?,
        },
        Inst::DialectOp(op) => match context {
            Context::Function if op.result_tys.len() == 1 => {
                Plan::All(Atom::Borrowed(&op.result_tys[0]))
            }
            Context::Function => Plan::Empty,
            Context::Module(_) | Context::Catalog(_) => Plan::Types(&op.result_tys),
        },
        Inst::LandingPad { .. } => match context {
            Context::Function => Plan::Empty,
            Context::Module(_) | Context::Catalog(_) => Plan::Pair(Atom::Ptr, Atom::I32),
        },
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
        | Inst::Resume { .. } => Plan::Empty,
    })
}
