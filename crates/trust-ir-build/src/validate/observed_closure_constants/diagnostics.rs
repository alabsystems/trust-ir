// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    fn location_copy<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.text(&self.location, &mut self.detail)
    }
    pub(super) fn mismatch<O: ExecutionObserver>(
        &mut self,
        item: Item<'_>,
        closure_ty_id: u32,
        capture_index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.location_copy(work)?;
        self.expected = item.ty.display_observed(work.session, work.site)?;
        self.actual = item
            .constant
            .shape_label_observed(work.session, work.site)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
        self.errors
            .push(ValidationError::ClosureCaptureTypeMismatch {
                location: take(&mut self.detail),
                closure_ty_id,
                capture_index,
                expected: take(&mut self.expected),
                actual: take(&mut self.actual),
            });
        Ok(())
    }
    pub(super) fn single<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        captures: &[Constant],
        id: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R<&'a [Ty]> {
        let Some(closure) = work.at(&module.closure_types, id as usize)? else {
            self.location_copy(work)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>() + size_of::<String>())?;
            self.errors.push(ValidationError::ClosureTypeNotFound {
                location: take(&mut self.detail),
                closure_ty_id: id,
            });
            return Ok(&[]);
        };
        work.admit(2, 2 * size_of::<usize>())?;
        if captures.len() != closure.captures.len() {
            self.location_copy(work)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>() + size_of::<String>())?;
            self.errors
                .push(ValidationError::ClosureCaptureArityMismatch {
                    location: take(&mut self.detail),
                    closure_ty_id: id,
                    expected: closure.captures.len(),
                    actual: captures.len(),
                });
        }
        Ok(&closure.captures)
    }
}
