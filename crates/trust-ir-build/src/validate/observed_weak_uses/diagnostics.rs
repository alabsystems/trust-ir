// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn location<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: BlockId,
        index: usize,
        case: Option<usize>,
        panic: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("function '", &mut self.location)?;
        work.text(&function.name, &mut self.location)?;
        work.text("' bb", &mut self.location)?;
        work.unsigned(u128::from(block.index()), &mut self.location)?;
        work.text(" instruction ", &mut self.location)?;
        work.unsigned(index as u128, &mut self.location)?;
        if let Some(case) = case {
            work.text(" case ", &mut self.location)?;
            work.unsigned(case as u128, &mut self.location)?;
        }
        if panic {
            work.text(" (panic site entry)", &mut self.location)?;
        }
        Ok(())
    }
    pub(super) fn direct<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: BlockId,
        index: usize,
        callee: FuncId,
        target: &Function,
        panic: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.location(function, block, index, None, panic, work)?;
        work.text(&target.name, &mut self.name)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors
            .push(ValidationError::DirectCallToWeakDeclaration {
                location: take(&mut self.location),
                callee: callee.index(),
                name: take(&mut self.name),
            });
        Ok(())
    }
    pub(super) fn indirect<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        block: u32,
        decl: &Function,
        sig: FuncTyId,
        conv: CallingConv,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(16, 2 * size_of::<Option<&FuncTy>>())?;
        if conv != decl.calling_conv {
            work.text(&decl.name, &mut self.name)?;
            render::convention(conv, &mut self.declared, work)?;
            render::convention(decl.calling_conv, &mut self.actual, work)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
            self.errors.push(ValidationError::CallEdgeConvMismatch {
                block,
                callee: take(&mut self.name),
                declared: take(&mut self.declared),
                actual: take(&mut self.actual),
            });
        }
        let declared = work.at(&module.func_types, sig.as_usize())?;
        let actual = work.at(&module.func_types, decl.ty.as_usize())?;
        let (Some(declared), Some(actual)) = (declared, actual) else {
            return Ok(());
        };
        if !declared.structural_eq_observed(actual, work.session, work.site)? {
            work.text(&decl.name, &mut self.name)?;
            work.text("call functy.", &mut self.declared)?;
            work.unsigned(u128::from(sig.index()), &mut self.declared)?;
            work.text(" (", &mut self.declared)?;
            render::wrapped_list(&declared.params, &mut self.render, &mut self.declared, work)?;
            work.text(") -> (", &mut self.declared)?;
            render::wrapped_list(
                &declared.returns,
                &mut self.render,
                &mut self.declared,
                work,
            )?;
            work.text(") through the weak address", &mut self.declared)?;
            work.text("target functy.", &mut self.actual)?;
            work.unsigned(u128::from(decl.ty.index()), &mut self.actual)?;
            work.text(" (", &mut self.actual)?;
            render::wrapped_list(&actual.params, &mut self.render, &mut self.actual, work)?;
            work.text(") -> (", &mut self.actual)?;
            render::wrapped_list(&actual.returns, &mut self.render, &mut self.actual, work)?;
            work.text(")", &mut self.actual)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
            self.errors
                .push(ValidationError::CallEdgeSignatureMismatch {
                    block,
                    callee: take(&mut self.name),
                    declared: take(&mut self.declared),
                    actual: take(&mut self.actual),
                });
        }
        Ok(())
    }
}
