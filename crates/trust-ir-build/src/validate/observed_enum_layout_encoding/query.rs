// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
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
        match self
            .table
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?
            .ty_layout_observed(ty, work.session, work.site)?
        {
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
    pub(super) fn size<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<u64>> {
        let summary = self.query(ty, work)?;
        self.retire_error(work);
        work.admit(1, size_of::<Option<u64>>())?;
        Ok(summary.and_then(|summary| summary.size))
    }
    pub(super) fn uninhabited<O: ExecutionObserver>(
        &self,
        variant: &trust_ir::ty::EnumVariant,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        self.table
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?
            .variant_is_uninhabited_observed(variant, work.session, work.site)
    }
}
