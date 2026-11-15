// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn undefined<O: ExecutionObserver>(
        &mut self,
        mode: Mode,
        block: BlockId,
        aggregate: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("aggregate type ", &mut self.reason)?;
        render::ty(aggregate, &mut self.render, &mut self.reason, work)?;
        work.text(" references an undefined definition", &mut self.reason)?;
        self.invalid(mode, block, work)
    }
    pub(super) fn invalid<O: ExecutionObserver>(
        &mut self,
        mode: Mode,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(mode.op(), &mut self.op)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors.push(ValidationError::FieldAccessInvalid {
            block: block.index(),
            op: take(&mut self.op),
            reason: take(&mut self.reason),
        });
        Ok(())
    }
    pub(super) fn checked_mismatch<O: ExecutionObserver>(
        &mut self,
        mode: Mode,
        block: BlockId,
        role: &str,
        expected: &Ty,
        actual: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if expected.structural_eq_observed(actual, work.session, work.site)? {
            return Ok(());
        }
        work.admit(3, size_of::<bool>())?;
        if expected.is_refine() || actual.is_refine() {
            return Ok(());
        }
        self.mismatch(mode, block, role, expected, actual, work)
    }
    pub(super) fn mismatch<O: ExecutionObserver>(
        &mut self,
        mode: Mode,
        block: BlockId,
        role: &str,
        expected: &Ty,
        actual: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.expected = expected.display_observed(work.session, work.site)?;
        self.enum_mismatch(mode, block, role, actual, work)
    }
    pub(super) fn enum_mismatch<O: ExecutionObserver>(
        &mut self,
        mode: Mode,
        block: BlockId,
        role: &str,
        actual: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.actual = actual.display_observed(work.session, work.site)?;
        work.text(mode.op(), &mut self.op)?;
        work.text(role, &mut self.role)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 4 * size_of::<String>())?;
        self.errors.push(ValidationError::OperandTypeMismatch {
            block: block.index(),
            op: take(&mut self.op),
            role: take(&mut self.role),
            expected: take(&mut self.expected),
            actual: take(&mut self.actual),
        });
        Ok(())
    }
}
