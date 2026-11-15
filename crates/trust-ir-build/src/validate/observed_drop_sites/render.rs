// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn type_reason<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        rule: TypeRule,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, size_of::<String>() + size_of::<TypeRule>())?;
        if self.ty.capacity() != 0 || self.reason.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        // Immediately retain the entire owned child spelling before another
        // callback. Partial reason and type spelling coexist through failure.
        self.ty = ty.display_observed(work.session, work.site)?;
        let (prefix, suffix) = match rule {
            TypeRule::Refined => (
                "a drop of the refined type ",
                ": a refinement has its base's representation, so the drop is spelled at the base",
            ),
            TypeRule::Trivial => (
                "a drop of the trivially droppable type ",
                ": a drop that does nothing is spelled by absence",
            ),
        };
        work.text(prefix, &mut self.reason)?;
        work.text(&self.ty, &mut self.reason)?;
        work.text(suffix, &mut self.reason)?;
        work.flat(take(&mut self.ty));
        work.admit(1, 0)
    }
    pub(super) fn direct_reason<O: ExecutionObserver>(
        &mut self,
        callee: FuncId,
        what: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        if self.reason.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text("a direct ", &mut self.reason)?;
        work.text(what, &mut self.reason)?;
        work.text(" of registered drop glue @func.", &mut self.reason)?;
        work.number(callee.index(), &mut self.reason)?;
        work.text(": a destructor runs only through a drop (Drop / DropInvoke), so every destructor run is a site a verifier can find; take the glue's address for dynamic dispatch",&mut self.reason)
    }
    pub(super) fn emit<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        if self.name.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text(&function.name, &mut self.name)?;
        work.reserve(&mut self.errors)?;
        work.admit(
            3,
            size_of::<ValidationError>() + 2 * size_of::<String>() + size_of::<u32>(),
        )?;
        self.errors.push(ValidationError::NonCanonicalDrop {
            function: take(&mut self.name),
            block,
            reason: take(&mut self.reason),
        });
        Ok(())
    }
}
