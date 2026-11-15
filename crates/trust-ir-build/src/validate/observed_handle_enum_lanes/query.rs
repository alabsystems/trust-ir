// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn size<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'_>,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<u64>> {
        work.admit(
            2,
            size_of::<Option<Arc<TyLayoutShape>>>() + size_of::<Option<LayoutError>>(),
        )?;
        if self.shape.is_some() || self.error.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        // Retain the WHOLE owning child before the next fee, both success and
        // semantic error. The outer operational Result is never collapsed.
        match layouts.ty_layout_observed(ty, work.session, work.site)? {
            Ok(shape) => self.shape = Some(shape),
            Err(error) => self.error = Some(error),
        }
        work.admit(6, size_of::<Option<u64>>() + size_of::<u64>())?;
        let size = match &self.shape {
            Some(shape) => shape.size_bytes(),
            None => None,
        };
        // size_bytes is the actual fixed checked_div/is_multiple_of scalar
        // body, not a recursive shape walk; bind it in the raw support.
        self.retire_shape(work);
        self.retire_error(work);
        work.admit(1, 0)?;
        Ok(size)
    }
}
