// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::checks::Edge;
use super::*;
impl State {
    pub(super) fn closure<O: ExecutionObserver>(
        &mut self,
        context: &ObservedIndirectCalls<'_, '_>,
        edge: &Edge<'_>,
        signature: &FuncTy,
        values: &ObservedValueTypes,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(Ty::Closure(id)) = values.get_observed(edge.callee, work.session, work.site)?
        else {
            return Ok(());
        };
        let module = context.catalog.source_module();
        let Some(closure) = work.at(&module.closure_types, id.as_usize())? else {
            self.ready(work)?;
            work.text("function '", &mut self.detail)?;
            work.text(&context.function.name, &mut self.detail)?;
            work.text("' bb", &mut self.detail)?;
            work.number(block.index() as usize, &mut self.detail)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::ClosureTypeNotFound {
                location: take(&mut self.detail),
                closure_ty_id: id.index(),
            });
            return Ok(());
        };
        work.admit(1, size_of::<bool>())?;
        if closure.func != edge.sig {
            return self.push(
                ValidationError::CallIndirectClosureSigMismatch {
                    block: block.index(),
                    closure_ty_id: id.index(),
                    declared_sig_id: edge.sig.index(),
                    apparent_sig_id: closure.func.index(),
                },
                work,
            );
        }
        let closures = context
            .closures
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        let Some(target) = closures.get_observed(edge.callee, work.session, work.site)? else {
            return Ok(());
        };
        let Some(function) = context
            .catalog
            .unique_observed(target, work.session, work.site)?
        else {
            return Ok(());
        };
        let Some(actual) = work.at(&module.func_types, function.ty.as_usize())? else {
            return Ok(());
        };
        work.admit(1, size_of::<bool>())?;
        // Borrowed captures ++ apparent params replaces only the original
        // intermediate cloned Vec; raw equality still ignores ABI here.
        if actual.is_vararg
            || !render::joined_equal(&closure.captures, &signature.params, &actual.params, work)?
            || !render::equal(&actual.returns, &signature.returns, work)?
        {
            self.ready(work)?;
            work.text(&function.name, &mut self.name)?;
            work.text("(", &mut self.expected)?;
            render::list(
                &closure.captures,
                &mut self.render,
                &mut self.expected,
                work,
            )?;
            if !closure.captures.is_empty() && !signature.params.is_empty() {
                work.text(", ", &mut self.expected)?;
            }
            render::list(
                &signature.params,
                &mut self.render,
                &mut self.expected,
                work,
            )?;
            work.text(")", &mut self.expected)?;
            // Preserve the original diagnostic's literal spelling exactly.
            work.text(") -> (", &mut self.expected)?;
            render::wrapped_list(
                &signature.returns,
                &mut self.render,
                &mut self.expected,
                work,
            )?;
            render::wrapped_list(&actual.params, &mut self.render, &mut self.actual, work)?;
            work.text(") -> (", &mut self.actual)?;
            render::wrapped_list(&actual.returns, &mut self.render, &mut self.actual, work)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors
                .push(ValidationError::CallIndirectClosureTargetMismatch {
                    block: block.index(),
                    closure_ty_id: id.index(),
                    target: take(&mut self.name),
                    expected: take(&mut self.expected),
                    actual: take(&mut self.actual),
                });
        }
        Ok(())
    }
}
