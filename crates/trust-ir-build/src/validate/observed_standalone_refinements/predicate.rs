// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

impl<'a> Checking<'a> {
    pub(super) fn contains<O: ExecutionObserver>(
        &mut self,
        ty: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.push(&mut self.frames, Frame::Visit(ty))?;
        let mut found = false;
        while !self.frames.is_empty() {
            work.admit(1, size_of::<Frame<'_>>())?;
            let frame = self.frames.pop().ok_or(ObservedValueError::InvalidRange)?;
            match frame {
                Frame::Children(elements) => {
                    work.admit(1, 0)?;
                    if let Some((first, rest)) = elements.split_first() {
                        // Schedule one borrowed continuation, not an eager
                        // reversed copy of every sibling. Tuple short-circuit
                        // order is exactly the original left-to-right any().
                        if !rest.is_empty() {
                            work.push(&mut self.frames, Frame::Children(rest))?;
                        }
                        work.push(&mut self.frames, Frame::Visit(first))?;
                    }
                }
                Frame::Visit(ty) => match ty {
                    Ty::Storage(_) => {}
                    Ty::Refine(_, _) => {
                        found = true;
                        break;
                    }
                    Ty::Ref(element)
                    | Ty::RefMut(element)
                    | Ty::PtrConst(element)
                    | Ty::PtrMut(element)
                    | Ty::Vector(element, _)
                    | Ty::Tensor(element, _)
                    | Ty::Rc(element) => work.push(&mut self.frames, Frame::Visit(element))?,
                    Ty::Tuple(elements) => {
                        work.push(&mut self.frames, Frame::Children(elements))?
                    }
                    // Deliberately do not follow any table/nominal identity.
                    // Exhaustive terminals force review when Ty gains a case.
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
                    | Ty::Dialect(_)
                    | Ty::Handle(_) => {}
                    Ty::Ext(extension) => extension.unreachable(),
                },
            }
        }
        work.retire_refs(&mut self.frames);
        // Retirement can be the original first refusal; never turn that stop
        // into a boolean answer or further diagnostic-building permission.
        work.admit(1, 0)?;
        Ok(found)
    }
}
