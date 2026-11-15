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
        self.check(ty, Context::Module, work)?;
        work.retire(take(&mut self.location));
        work.admit(1, 0)
    }

    pub(super) fn check<O: ExecutionObserver>(
        &mut self,
        ty: &'a Ty,
        context: Context,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.push(&mut self.frames, Frame::Visit(ty))?;
        while !self.frames.is_empty() {
            work.admit(41, size_of::<Frame<'_>>())?;
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
                    Ty::Vector(element, lanes) => {
                        self.vector(ty, element, *lanes, context, work)?;
                        // Even an invalid outer vector recurses into its
                        // element after ALL three original ordered checks.
                        work.push(&mut self.frames, Frame::Visit(element))?;
                    }
                    Ty::Tuple(elements) => {
                        work.push(&mut self.frames, Frame::Children(elements))?
                    }
                    Ty::Tensor(inner, _)
                    | Ty::Ref(inner)
                    | Ty::RefMut(inner)
                    | Ty::PtrConst(inner)
                    | Ty::PtrMut(inner)
                    | Ty::Rc(inner) => work.push(&mut self.frames, Frame::Visit(inner))?,
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
                    | Ty::Error
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

    fn vector<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        element: &Ty,
        lanes: u32,
        context: Context,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if lanes == 0 {
            self.report(ty, "lane count must be nonzero", context, work)?;
        }
        work.admit(1, 0)?;
        if matches!(element, Ty::Vector(_, _)) {
            self.report(ty, "nested vector lanes are not supported", context, work)?;
        }
        work.admit(12, 0)?;
        if !matches!(
            element,
            Ty::Bool
                | Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::F16
                | Ty::F32
                | Ty::F64
        ) {
            self.report(
                ty,
                "lane type must be bool, integer, or float",
                context,
                work,
            )?;
        }
        Ok(())
    }
}
