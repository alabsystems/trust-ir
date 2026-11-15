// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl Diagnostics {
    pub(super) fn count<O: ExecutionObserver>(
        &mut self,
        block: u32,
        target: u32,
        expected: usize,
        actual: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        if expected != actual {
            work.admit(1, size_of::<ValidationError>())?;
            self.pending = Some(ValidationError::BranchArgCountMismatch {
                block,
                target,
                expected,
                actual,
            });
            self.commit(work)?;
        }
        Ok(())
    }
    pub(super) fn mismatch<O: ExecutionObserver>(
        &mut self,
        block: u32,
        target: u32,
        arg_index: usize,
        expected: &Ty,
        actual: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.admit(1, size_of::<String>())?;
        self.expected = expected.display_observed(work.session, work.site)?;
        work.admit(1, size_of::<String>())?;
        self.actual = actual.display_observed(work.session, work.site)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.pending = Some(ValidationError::BranchArgTypeMismatch {
            block,
            target,
            arg_index,
            expected: take(&mut self.expected),
            actual: take(&mut self.actual),
        });
        self.commit(work)
    }
    pub(super) fn commit<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        let error = self
            .pending
            .take()
            .ok_or(ObservedValueError::InvalidRange)?;
        self.errors.push(error);
        Ok(())
    }
    fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(3, 0)?;
        if self.pending.is_some() || self.expected.capacity() != 0 || self.actual.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
}
