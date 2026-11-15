// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    pub(super) fn ty<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        registry: &HandleRegistry,
        ty: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Frame<'_>>())?;
        work.push(&mut self.frames, Frame::Visit(ty))?;
        loop {
            work.admit(1, size_of::<Option<Frame<'_>>>())?;
            let Some(frame) = self.frames.pop() else {
                break;
            };
            work.admit(2, size_of::<Frame<'_>>())?;
            match frame {
                Frame::Visit(ty) => {
                    self.node(module, registry, ty, work)?;
                    work.admit(42, 2 * size_of::<Frame<'_>>())?;
                    match ty {
                        Ty::Storage(_) => {}
                        Ty::Vector(inner, _)
                        | Ty::Tensor(inner, _)
                        | Ty::Ref(inner)
                        | Ty::RefMut(inner)
                        | Ty::PtrConst(inner)
                        | Ty::PtrMut(inner)
                        | Ty::Rc(inner) => work.push(&mut self.frames, Frame::Visit(inner))?,
                        Ty::Tuple(items) => {
                            work.push(&mut self.frames, Frame::Children(items, 0))?
                        }
                        Ty::I8
                        | Ty::I16
                        | Ty::I32
                        | Ty::I64
                        | Ty::I128
                        | Ty::U8
                        | Ty::U16
                        | Ty::U32
                        | Ty::U64
                        | Ty::U128
                        | Ty::Isize
                        | Ty::Usize
                        | Ty::Char
                        | Ty::Error
                        | Ty::F16
                        | Ty::F32
                        | Ty::F64
                        | Ty::Bool
                        | Ty::Ptr
                        | Ty::FatPtr(_)
                        | Ty::Unit
                        | Ty::Never
                        | Ty::Struct(_)
                        | Ty::Array(_, _)
                        | Ty::Enum(_)
                        | Ty::Func(_)
                        | Ty::Set(_, _)
                        | Ty::Sequence(_)
                        | Ty::Record(_)
                        | Ty::Closure(_)
                        | Ty::Refine(_, _)
                        | Ty::Dialect(_)
                        | Ty::Handle(_)
                        | Ty::Ext(_) => {}
                    }
                }
                Frame::Children(items, index) => {
                    if let Some(ty) = work.at(items, index)? {
                        let mut next = index;
                        work.next(&mut next)?;
                        work.push(&mut self.frames, Frame::Children(items, next))?;
                        work.push(&mut self.frames, Frame::Visit(ty))?;
                    }
                }
            }
        }
        Ok(())
    }
    pub(super) fn instruction<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        registry: &HandleRegistry,
        inst: &'a Inst,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, size_of::<Vec<&Ty>>())?;
        if self.roots.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.roots = inst.inline_types_observed(work.session, work.site)?;
        let mut at = 0usize;
        while let Some(root) = work.at(&self.roots, at)? {
            work.admit(1, size_of::<&Ty>())?;
            let ty = *root;
            self.ty(module, registry, ty, work)?;
            work.next(&mut at)?;
        }
        self.retire_roots(work);
        work.admit(67, size_of::<Option<&trust_ir::dialect::DialectInst>>())?;
        if let Inst::DialectOp(op) = inst {
            let mut at = 0usize;
            while let Some(attr) = work.at(&op.attrs, at)? {
                work.admit(7, size_of::<Option<&Ty>>())?;
                if let trust_ir::dialect::AttrValue::Ty(ty) = &attr.value {
                    self.ty(module, registry, ty, work)?;
                }
                work.next(&mut at)?;
            }
        }
        Ok(())
    }
}
