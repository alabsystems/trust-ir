// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn surface<O: ExecutionObserver>(
        &mut self,
        location: Location<'_>,
        ty: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.location(location, work)?;
        self.check(ty, Buffer::Base, work)?;
        self.end_location(work)
    }
    pub(super) fn check<O: ExecutionObserver>(
        &mut self,
        ty: &'a Ty,
        location: Buffer,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.push(&mut self.frames, Frame::Visit(ty))?;
        while !self.frames.is_empty() {
            work.admit(1, size_of::<Frame<'_>>())?;
            match self.frames.pop().ok_or(ObservedValueError::InvalidRange)? {
                Frame::Children(elements) => {
                    work.admit(1, 0)?;
                    if let Some((first, rest)) = elements.split_first() {
                        if !rest.is_empty() {
                            work.push(&mut self.frames, Frame::Children(rest))?;
                        }
                        work.push(&mut self.frames, Frame::Visit(first))?;
                    }
                }
                Frame::Visit(ty) => match ty {
                    Ty::Storage(_) => {}
                    Ty::Error => self.poison(location, work)?,
                    Ty::Vector(elem, _)
                    | Ty::Tensor(elem, _)
                    | Ty::Ref(elem)
                    | Ty::RefMut(elem)
                    | Ty::PtrConst(elem)
                    | Ty::PtrMut(elem)
                    | Ty::Rc(elem) => work.push(&mut self.frames, Frame::Visit(elem))?,
                    Ty::Tuple(elements) => {
                        work.push(&mut self.frames, Frame::Children(elements))?
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
                    | Ty::Handle(_) => {}
                    Ty::Ext(extension) => extension.unreachable(),
                },
            }
        }
        work.retire_refs(&mut self.frames);
        work.admit(1, 0)
    }
}
