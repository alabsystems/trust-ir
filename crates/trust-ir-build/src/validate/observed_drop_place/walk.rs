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
        work.admit(8, size_of::<(&str, ValueId)>())?;
        let (op, ptr) = match inst {
            Inst::Drop { ptr, .. } => ("drop", *ptr),
            Inst::DropInvoke { ptr, .. } => ("drop_invoke", *ptr),
            _ => return Ok(()),
        };
        let Some(actual) = values.get_observed(ptr, work.session, work.site)? else {
            return Ok(());
        };
        // Exact current source performs one tag test and at most one direct
        // module.types.get. Eq against payload-free Ptr reads only that tag;
        // this is not a recursive/refinement/layout walk or a validity claim.
        work.admit(8, size_of::<Option<&Ty>>() + size_of::<bool>())?;
        let representation = module.representation_ty(actual);
        if matches!(representation, Some(Ty::Ptr)) {
            return Ok(());
        }
        work.text(op, &mut self.op)?;
        work.text("ptr", &mut self.role)?;
        work.text("ptr", &mut self.expected)?;
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
        Ok(())
    }
}
