// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        inst: &Inst,
        values: &ObservedValueTypes,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(8, size_of::<(&Ty, ValueId)>())?;
        let Inst::ArraySplat { ty, value } = inst else {
            return Ok(());
        };
        let Ty::Array(element, len) = ty else {
            return self.invalid(block, ty, "the type is not an array type `[e x n]`", work);
        };
        let Some(expected) = work.at(&module.types, element.as_usize())? else {
            return self.invalid(block, ty, "references an undefined element type", work);
        };
        if let Some(actual) = values.get_observed(*value, work.session, work.site)?
            && !actual.structural_eq_observed(expected, work.session, work.site)?
        {
            work.admit(3, size_of::<bool>())?;
            if !(actual.is_refine() || expected.is_refine()) {
                work.text("array_splat", &mut self.op)?;
                work.text("value", &mut self.role)?;
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
        work.admit(1, size_of::<bool>())?;
        if *len == 0 {
            self.ty = ty.display_observed(work.session, work.site)?;
            work.text("block ", &mut self.location)?;
            work.number(block.index() as usize, &mut self.location)?;
            work.text(": array_splat ", &mut self.location)?;
            work.text(&self.ty, &mut self.location)?;
            work.text(" %", &mut self.location)?;
            work.number(value.index() as usize, &mut self.location)?;
            work.text(
                "zero copies are the empty array `const ",
                &mut self.spelling,
            )?;
            work.text(&self.ty, &mut self.spelling)?;
            work.text(" array[ ]`", &mut self.spelling)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
            self.errors.push(ValidationError::NonCanonicalUniformArray {
                location: take(&mut self.location),
                spelling: take(&mut self.spelling),
            });
        }
        Ok(())
    }
    fn invalid<O: ExecutionObserver>(
        &mut self,
        block: BlockId,
        ty: &Ty,
        reason: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ty = ty.display_observed(work.session, work.site)?;
        work.text(reason, &mut self.reason)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors.push(ValidationError::InvalidArraySplat {
            block: block.index(),
            ty: take(&mut self.ty),
            reason: take(&mut self.reason),
        });
        Ok(())
    }
}
