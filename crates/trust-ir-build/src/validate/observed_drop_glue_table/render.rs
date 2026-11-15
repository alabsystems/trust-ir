// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    fn append_type<O: ExecutionObserver>(&mut self, ty: &Ty, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<String>())?;
        if self.ty.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.ty = ty.display_observed(work.session, work.site)?;
        work.text(&self.ty, &mut self.reason)?;
        work.flat(take(&mut self.ty));
        work.admit(1, 0)
    }
    pub(super) fn order_reason<O: ExecutionObserver>(
        &mut self,
        glue: u32,
        previous: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(
            "rows are strictly ascending by glue, and @func.",
            &mut self.reason,
        )?;
        work.number(glue, &mut self.reason)?;
        work.text(" does not follow @func.", &mut self.reason)?;
        work.number(previous, &mut self.reason)?;
        work.text(" (one glue would destroy two types)", &mut self.reason)
    }
    pub(super) fn duplicate_reason<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("a second row for type ", &mut self.reason)?;
        self.append_type(ty, work)?;
        work.text(": one row per type", &mut self.reason)
    }
    pub(super) fn key_reason<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        rule: KeyRule,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("the key ", &mut self.reason)?;
        self.append_type(ty, work)?;
        work.admit(1, size_of::<KeyRule>())?;
        work.text(match rule {
            KeyRule::Refined=>" is a refinement: a refinement has its base's representation, so its drop is spelled at the base",
            KeyRule::Trivial=>" is trivially droppable: a drop that does nothing is spelled by absence, so it has no glue",
        },&mut self.reason)
    }
    fn type_list<O: ExecutionObserver>(&mut self, types: &[Ty], work: &mut Work<'_, '_, O>) -> R {
        work.text("(", &mut self.reason)?;
        let mut index = 0usize;
        while let Some(ty) = work.at(types, index)? {
            work.admit(1, size_of::<bool>())?;
            if index != 0 {
                work.text(", ", &mut self.reason)?;
            }
            self.append_type(ty, work)?;
            work.next(&mut index)?;
        }
        work.text(")", &mut self.reason)
    }
    pub(super) fn signature_reason<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        signature: &FuncTy,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("the glue '", &mut self.reason)?;
        work.text(&function.name, &mut self.reason)?;
        work.text("' has signature ", &mut self.reason)?;
        self.type_list(&signature.params, work)?;
        work.text(" -> ", &mut self.reason)?;
        self.type_list(&signature.returns, work)?;
        work.text(
            "; drop glue is exactly (ptr) -> () and not variadic",
            &mut self.reason,
        )
    }
    pub(super) fn missing_signature_reason<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("the glue '", &mut self.reason)?;
        work.text(&function.name, &mut self.reason)?;
        work.text("' names function type functy.", &mut self.reason)?;
        work.number(function.ty.index(), &mut self.reason)?;
        work.text(", which does not exist", &mut self.reason)
    }
    pub(super) fn emit<O: ExecutionObserver>(
        &mut self,
        entry: usize,
        glue: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(2, size_of::<ValidationError>() + size_of::<String>())?;
        self.errors.push(ValidationError::InvalidDropGlue {
            entry,
            glue,
            reason: take(&mut self.reason),
        });
        Ok(())
    }
}
