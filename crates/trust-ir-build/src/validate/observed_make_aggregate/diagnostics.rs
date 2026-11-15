// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn invalid<O: ExecutionObserver>(
        &mut self,
        block: BlockId,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ty = ty.display_observed(work.session, work.site)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors.push(ValidationError::InvalidMakeAggregate {
            block: block.index(),
            ty: take(&mut self.ty),
            reason: take(&mut self.reason),
        });
        Ok(())
    }
    pub(super) fn because<O: ExecutionObserver>(
        &mut self,
        block: BlockId,
        ty: &Ty,
        reason: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(reason, &mut self.reason)?;
        self.invalid(block, ty, work)
    }
    pub(super) fn arity<O: ExecutionObserver>(
        &mut self,
        block: BlockId,
        ty: &Ty,
        actual: usize,
        expected: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.unsigned(actual as u128, &mut self.reason)?;
        work.text(
            " lane operand(s) supplied, but the type declares ",
            &mut self.reason,
        )?;
        work.unsigned(expected as u128, &mut self.reason)?;
        work.text(" lane(s)", &mut self.reason)?;
        self.invalid(block, ty, work)
    }
    pub(super) fn location<O: ExecutionObserver>(
        &mut self,
        block: BlockId,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("block ", &mut self.location)?;
        work.unsigned(u128::from(block.index()), &mut self.location)?;
        work.text(": make_aggregate ", &mut self.location)?;
        render::ty(ty, &mut self.render, &mut self.location, work)
    }
    pub(super) fn check<O: ExecutionObserver>(
        &mut self,
        block: BlockId,
        ty: &Ty,
        fields: &[ValueId],
        lanes: lanes::Lanes<'_>,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let len = lanes.len(work)?;
        work.admit(1, size_of::<bool>())?;
        if fields.len() != len {
            return self.arity(block, ty, fields.len(), len, work);
        }
        let mut at = 0;
        while let Some(field) = work.at(fields, at)? {
            let expected = lanes
                .at(at, work)?
                .ok_or(ObservedValueError::InvalidRange)?;
            if let Some(actual) = values.get_observed(*field, work.session, work.site)?
                && !actual.structural_eq_observed(expected, work.session, work.site)?
            {
                work.admit(3, size_of::<bool>())?;
                if !(actual.is_refine() || expected.is_refine()) {
                    work.text("make_aggregate", &mut self.op)?;
                    work.text("lane ", &mut self.role)?;
                    work.unsigned(at as u128, &mut self.role)?;
                    self.expected = expected.display_observed(work.session, work.site)?;
                    self.actual = actual.display_observed(work.session, work.site)?;
                    work.reserve(&mut self.errors)?;
                    work.admit(1, size_of::<ValidationError>() + 4 * size_of::<String>())?;
                    self.errors.push(ValidationError::OperandTypeMismatch {
                        block: block.index(),
                        op: take(&mut self.op),
                        role: take(&mut self.role),
                        expected: take(&mut self.expected),
                        actual: take(&mut self.actual),
                    });
                }
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
}
