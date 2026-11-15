// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn name<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.name.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text(&function.name, &mut self.name)
    }
    pub(super) fn scalar<O: ExecutionObserver>(
        &mut self,
        error: ValidationError,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Private callers pass only fixed Copy-payload diagnostics.
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(error);
        Ok(())
    }
    pub(super) fn transfer_pending<O: ExecutionObserver>(
        &mut self,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, 2 * size_of::<ValidationError>())?;
        self.errors.push(
            self.pending
                .take()
                .ok_or(ObservedValueError::InvalidRange)?,
        );
        Ok(())
    }
    pub(super) fn signature<O: ExecutionObserver>(
        &mut self,
        request: Request<'_>,
        signature: &FuncTy,
        operands: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.name(request.function, work)?;
        work.text("fn(", &mut self.expected)?;
        let mut at = 0;
        while at < operands {
            work.text("usize, ", &mut self.expected)?;
            work.next(&mut at)?;
        }
        work.text("ptr | ref | ptr_const) -> ()", &mut self.expected)?;
        work.text("fn", &mut self.actual)?;
        render::list(&signature.params, &mut self.render, &mut self.actual, work)?;
        if signature.is_vararg {
            work.text(" (variadic)", &mut self.actual)?;
        }
        work.text(" -> ", &mut self.actual)?;
        render::list(&signature.returns, &mut self.render, &mut self.actual, work)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
        self.errors
            .push(ValidationError::PanicEntrySignatureMismatch {
                function: take(&mut self.name),
                block: request.block.index(),
                inst_index: request.index,
                entry: request.panic.entry.index(),
                expected: take(&mut self.expected),
                found: take(&mut self.actual),
            });
        Ok(())
    }
    pub(super) fn operand<O: ExecutionObserver>(
        &mut self,
        request: Request<'_>,
        expected: &Ty,
        actual: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("assert", &mut self.op)?;
        work.text("location", &mut self.role)?;
        self.expected = expected.display_observed(work.session, work.site)?;
        self.actual = actual.display_observed(work.session, work.site)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 4 * size_of::<String>())?;
        self.errors.push(ValidationError::OperandTypeMismatch {
            block: request.block.index(),
            op: take(&mut self.op),
            role: take(&mut self.role),
            expected: take(&mut self.expected),
            actual: take(&mut self.actual),
        });
        Ok(())
    }
}
