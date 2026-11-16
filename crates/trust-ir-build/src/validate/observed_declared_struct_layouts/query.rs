// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn query<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<Summary>> {
        work.admit(2, 0)?;
        if self.shape.is_some() || self.error.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        let table = self
            .table
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        match table.ty_layout_observed(ty, work.session, work.site)? {
            Ok(shape) => self.shape = Some(shape),
            Err(error) => self.error = Some(error),
        }
        work.admit(5, size_of::<Summary>())?;
        if let Some(shape) = &self.shape {
            let summary = Summary {
                size: if shape.size_bits.is_multiple_of(8) {
                    Some(shape.size_bits / 8)
                } else {
                    None
                },
                align: shape.align_bits,
            };
            self.retire_shape(work);
            work.admit(1, 0)?;
            Ok(Some(summary))
        } else {
            Ok(None)
        }
    }
    pub(super) fn take_target<O: ExecutionObserver>(
        &mut self,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, 0)?;
        if self.triple.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        match self.error.take() {
            Some(LayoutError::TargetScalarLayoutUnavailable { triple }) => {
                self.triple = triple;
                Ok(true)
            }
            Some(error) => {
                self.error = Some(error);
                self.retire_error(work);
                work.admit(1, 0)?;
                Ok(false)
            }
            None => Err(ObservedValueError::InvalidRange),
        }
    }
}
pub(super) fn zero<O: ExecutionObserver>(
    state: &mut State<'_>,
    module: &Module,
    ty: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, 0)?;
    match ty {
        Ty::Unit => Ok(true),
        Ty::Tuple(elems) => Ok(elems.is_empty()),
        Ty::Array(_, 0) => Ok(true),
        Ty::FnItem(_) => {
            // Use the actual charged header/signature lookup. A spelling alone
            // cannot authenticate the zero-sized nominal type.
            let summary = state.query(ty, work)?;
            state.retire_error(work);
            Ok(summary.is_some_and(|layout| layout.size == Some(0)))
        }
        Ty::Struct(id) => {
            let mut n = 0;
            while let Some(row) = work.at(&module.structs, n)? {
                work.admit(2, size_of::<Option<u64>>())?;
                if row.id == *id {
                    return Ok(row.size == Some(0));
                }
                work.next(&mut n)?;
            }
            Ok(false)
        }
        _ => Ok(false),
    }
}
