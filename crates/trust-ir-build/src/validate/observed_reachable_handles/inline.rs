// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    pub(super) fn inline<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        root: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Frame<'_>>())?;
        if !self.frames.is_empty() {
            return Err(ObservedValueError::InvalidRange);
        }
        work.push(&mut self.frames, Frame::Visit(root))?;
        while let Some(frame) = work.pop(&mut self.frames)? {
            work.admit(48, 2 * size_of::<Frame<'_>>() + size_of::<Option<Key>>())?;
            match frame {
                Frame::Visit(ty) => {
                    self.occurrence(module, ty, work)?;
                    match ty {
                        Ty::Storage(_) => {}
                        Ty::Vector(t, _)
                        | Ty::Tensor(t, _)
                        | Ty::Ref(t)
                        | Ty::RefMut(t)
                        | Ty::PtrConst(t)
                        | Ty::PtrMut(t)
                        | Ty::Rc(t) => work.push(&mut self.frames, Frame::Visit(t))?,
                        Ty::Tuple(types) => {
                            work.push(&mut self.frames, Frame::Children(types, 0))?
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
                Frame::Children(types, index) => {
                    if let Some(ty) = work.at(types, index)? {
                        let mut next = index;
                        work.next(&mut next)?;
                        work.push(&mut self.frames, Frame::Children(types, next))?;
                        work.push(&mut self.frames, Frame::Visit(ty))?;
                    }
                }
            }
        }
        Ok(())
    }
    fn occurrence<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        ty: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(48, size_of::<Option<Key>>())?;
        let key = match ty {
            Ty::Storage(_) => return Ok(()),
            Ty::Handle(_) => {
                self.insert(ty, work)?;
                return Ok(());
            }
            Ty::Array(id, _)
            | Ty::Set(id, _)
            | Ty::Sequence(id)
            | Ty::Refine(id, _)
            | Ty::FatPtr(FatPtrKind::Slice(id)) => Key::Ty(id.as_usize()),
            Ty::Func(id) => Key::Func(id.as_usize()),
            Ty::Struct(id) => Key::Struct(id.index()),
            Ty::Enum(id) => Key::Enum(id.index()),
            Ty::Record(id) => Key::Record(id.index()),
            Ty::Closure(id) => Key::Closure(id.as_usize()),
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
            | Ty::FatPtr(
                FatPtrKind::Str
                | FatPtrKind::TraitObject { .. }
                | FatPtrKind::ContainerLen
                | FatPtrKind::ContainerVtable,
            )
            | Ty::Unit
            | Ty::Never
            | Ty::Tuple(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Vector(_, _)
            | Ty::Tensor(_, _)
            | Ty::Dialect(_)
            | Ty::Ext(_) => return Ok(()),
        };
        if self.fresh(key, work)? {
            self.follow(module, key, work)?;
        }
        Ok(())
    }
    pub(super) fn fresh<O: ExecutionObserver>(
        &mut self,
        key: Key,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0usize;
        while let Some(old) = work.at(&self.seen, at)? {
            work.admit(2, 2 * size_of::<Key>())?;
            if *old == key {
                return Ok(false);
            }
            work.next(&mut at)?;
        }
        work.push(&mut self.seen, key)?;
        Ok(true)
    }
}
