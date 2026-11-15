// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::checks::Edge;
use super::*;
impl State {
    pub(super) fn pointer<O: ExecutionObserver>(
        &mut self,
        context: &mut ObservedIndirectCalls<'_, '_>,
        edge: &Edge<'_>,
        signature: &FuncTy,
        block: BlockId,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let analysis = context
            .pointers
            .as_mut()
            .ok_or(ObservedValueError::InvalidRange)?;
        let Some(resolution) = analysis.resolve_typed_at_observed(
            edge.callee,
            block,
            index,
            work.session,
            work.site,
        )?
        else {
            return Ok(());
        };
        // Actual context constructed the analysis for its own exact Function.
        // Do not substitute an arbitrary same-ID caller/candidate analysis.
        work.admit(8, size_of::<bool>())?;
        if resolution.containing_function() != context.function.id
            || resolution.queried_value() != edge.callee
            || resolution.use_block() != block
            || resolution.use_instruction_index() != index
        {
            return Err(ObservedValueError::InvalidRange);
        }
        let Some(target) =
            context
                .catalog
                .unique_observed(resolution.function(), work.session, work.site)?
        else {
            return self.push(
                ValidationError::CalleeNotFound {
                    block: block.index(),
                    callee_id: resolution.function().index(),
                },
                work,
            );
        };
        work.admit(1, size_of::<bool>())?;
        if edge.conv != target.calling_conv {
            self.ready(work)?;
            work.text(&target.name, &mut self.name)?;
            render::convention(edge.conv, &mut self.expected, work)?;
            render::convention(target.calling_conv, &mut self.actual, work)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::CallEdgeConvMismatch {
                block: block.index(),
                callee: take(&mut self.name),
                declared: take(&mut self.expected),
                actual: take(&mut self.actual),
            });
        }
        if let Some(actual) = work.at(
            &context.catalog.source_module().func_types,
            target.ty.as_usize(),
        )? {
            work.admit(4, size_of::<bool>())?;
            if resolution.declared_signature() != edge.sig
                || resolution.declared_signature() != target.ty
                || !signature.structural_eq_observed(actual, work.session, work.site)?
            {
                self.ready(work)?;
                work.text(&target.name, &mut self.name)?;
                work.text("call functy.", &mut self.expected)?;
                work.number(edge.sig.index() as usize, &mut self.expected)?;
                work.text(" (", &mut self.expected)?;
                render::wrapped_list(
                    &signature.params,
                    &mut self.render,
                    &mut self.expected,
                    work,
                )?;
                work.text(") -> (", &mut self.expected)?;
                render::wrapped_list(
                    &signature.returns,
                    &mut self.render,
                    &mut self.expected,
                    work,
                )?;
                work.text("); FnDef declares functy.", &mut self.expected)?;
                work.number(
                    resolution.declared_signature().index() as usize,
                    &mut self.expected,
                )?;
                work.text("target functy.", &mut self.actual)?;
                work.number(target.ty.index() as usize, &mut self.actual)?;
                work.text(" (", &mut self.actual)?;
                render::wrapped_list(&actual.params, &mut self.render, &mut self.actual, work)?;
                work.text(") -> (", &mut self.actual)?;
                render::wrapped_list(&actual.returns, &mut self.render, &mut self.actual, work)?;
                work.text(")", &mut self.actual)?;
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>())?;
                self.errors
                    .push(ValidationError::CallEdgeSignatureMismatch {
                        block: block.index(),
                        callee: take(&mut self.name),
                        declared: take(&mut self.expected),
                        actual: take(&mut self.actual),
                    });
            }
        }
        Ok(())
    }
}
