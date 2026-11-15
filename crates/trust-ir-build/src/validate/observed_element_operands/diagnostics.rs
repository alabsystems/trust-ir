// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn start<O: ExecutionObserver>(
        &mut self,
        op: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(3, 0)?;
        if self.op.capacity() != 0 || self.reason.capacity() != 0 || self.spelling.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text(op, &mut self.op)
    }
    pub(super) fn ty<O: ExecutionObserver>(&mut self, ty: &Ty, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<String>())?;
        if self.spelling.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.spelling = ty.display_observed(work.session, work.site)?;
        work.text(&self.spelling, &mut self.reason)?;
        work.retire(take(&mut self.spelling));
        work.admit(1, 0)
    }
    pub(super) fn commit<O: ExecutionObserver>(
        &mut self,
        block: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::InvalidVectorElementOp {
            block,
            op: take(&mut self.op),
            reason: take(&mut self.reason),
        });
        Ok(())
    }
    pub(super) fn wrong_kind<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        actual: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.start(op, work)?;
        work.text(
            "operand must be vector, array or sequence, got ",
            &mut self.reason,
        )?;
        self.ty(actual, work)?;
        self.commit(block, work)
    }
    pub(super) fn mismatch<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        prefix: &'static str,
        expected: &Ty,
        actual: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.start(op, work)?;
        work.text(prefix, &mut self.reason)?;
        self.ty(expected, work)?;
        work.text(", got ", &mut self.reason)?;
        self.ty(actual, work)?;
        self.commit(block, work)
    }
}
