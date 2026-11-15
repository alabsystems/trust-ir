// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(6, 0)?;
        if self.op.capacity() != 0
            || self.role.capacity() != 0
            || self.pointer.capacity() != 0
            || self.expected.capacity() != 0
            || self.actual.capacity() != 0
            || self.reason.capacity() != 0
        {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    pub(super) fn commit<O: ExecutionObserver>(
        &mut self,
        kind: Diagnostic,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        let error = match kind {
            Diagnostic::Operand(block) => ValidationError::OperandTypeMismatch {
                block,
                op: take(&mut self.op),
                role: take(&mut self.role),
                expected: take(&mut self.expected),
                actual: take(&mut self.actual),
            },
            Diagnostic::Pointer(block) => ValidationError::PointerOpInvalid {
                block,
                op: take(&mut self.op),
                ptr_ty: take(&mut self.pointer),
                reason: take(&mut self.reason),
            },
            Diagnostic::Metadata(block) => ValidationError::PointerMetadataTypeMismatch {
                block,
                op: take(&mut self.op),
                ptr_ty: take(&mut self.pointer),
                expected: take(&mut self.expected),
                actual: take(&mut self.actual),
            },
            Diagnostic::Select(block) => ValidationError::SelectConditionTypeMismatch {
                block,
                expected: take(&mut self.expected),
                actual: take(&mut self.actual),
            },
        };
        self.errors.push(error);
        Ok(())
    }
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.op));
        work.flat(take(&mut self.role));
        work.flat(take(&mut self.pointer));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
        work.flat(take(&mut self.reason));
        work.session.retirement_step(work.site, 1);
        if let Some(ty) = self.pending_ty.take() {
            // Consuming retirement drains everything even after sticky refusal.
            let _ = ty.retire_observed(work.session, work.site);
        }
    }
    pub(super) fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        let _ = retire_validation_errors_observed(take(&mut self.errors), work.session, work.site);
    }
}
