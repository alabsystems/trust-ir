// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[cfg(test)]
mod tests;
impl State<'_> {
    pub(super) fn function<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        registry: &HandleRegistry,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some((pin, entry)) =
            registry.entry_for_symbol_observed(&function.name, work.session, work.site)?
        else {
            return Ok(());
        };
        work.admit(1, size_of::<Option<ObservedPinnedFuncTy>>())?;
        if self.expected.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.expected = Some(pin.func_ty_observed(entry, work.session, work.site)?);
        let result = self.check_function(module, function, pin, entry, work);
        self.retire_expected(work);
        result?;
        work.admit(1, 0)
    }
    fn check_function<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        pin: &HandleRuntimePin,
        entry: &HandleEntryPoint,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            1,
            size_of::<Option<&FuncTy>>() + size_of::<trust_ir::value::FuncTyId>(),
        )?;
        match module.func_type(function.ty) {
            Some(actual) => {
                if !signature::same(
                    actual,
                    self.expected
                        .as_ref()
                        .ok_or(ObservedValueError::InvalidRange)?,
                    work,
                )? {
                    work.text("signature ", &mut self.piece)?;
                    render::signature(actual, &mut self.piece, &mut self.render, work)?;
                    work.admit(1, size_of::<bool>())?;
                    if actual.is_vararg {
                        work.text(" (variadic)", &mut self.piece)?;
                    }
                    self.mismatch(work)?;
                }
            }
            None => {
                work.text("dangling signature functy.", &mut self.piece)?;
                work.number(function.ty.index(), &mut self.piece)?;
                self.mismatch(work)?;
            }
        }
        self.attributes(function, pin, entry, work)?;
        work.admit(1, size_of::<usize>())?;
        if self.mismatches != 0 {
            work.text(&function.name, &mut self.symbol)?;
            work.admit(1, size_of::<CallingConv>())?;
            work.text(
                render::convention(pin.calling_conv),
                &mut self.expected_text,
            )?;
            work.text(" ", &mut self.expected_text)?;
            render::signature(
                self.expected
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?
                    .signature(),
                &mut self.expected_text,
                &mut self.render,
                work,
            )?;
            work.text(" (display path ", &mut self.expected_text)?;
            work.quoted(entry.def_path, &mut self.expected_text)?;
            work.text(" or unrecorded)", &mut self.expected_text)?;
            work.reserve(&mut self.errors)?;
            work.admit(
                1,
                size_of::<ValidationError>() + 3 * size_of::<String>() + size_of::<u32>(),
            )?;
            self.errors
                .push(ValidationError::HandleEntryPointSignatureMismatch {
                    function: function.id.index(),
                    symbol: take(&mut self.symbol),
                    expected: take(&mut self.expected_text),
                    actual: take(&mut self.actual),
                });
            work.admit(1, size_of::<usize>())?;
            self.mismatches = 0;
        }
        work.admit(2, size_of::<bool>() + size_of::<Linkage>())?;
        if !function.is_declaration() || function.linkage != Linkage::External {
            work.text(&function.name, &mut self.symbol)?;
            work.reserve(&mut self.errors)?;
            work.admit(
                1,
                size_of::<ValidationError>() + size_of::<String>() + size_of::<u32>(),
            )?;
            self.errors
                .push(ValidationError::HandleEntryPointDefinedLocally {
                    function: function.id.index(),
                    symbol: take(&mut self.symbol),
                });
        }
        Ok(())
    }
    fn attributes<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        pin: &HandleRuntimePin,
        entry: &HandleEntryPoint,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 2 * size_of::<CallingConv>())?;
        if function.calling_conv != pin.calling_conv {
            work.text("calling convention ", &mut self.piece)?;
            work.text(render::convention(function.calling_conv), &mut self.piece)?;
            self.mismatch(work)?;
        }
        work.admit(1, size_of::<bool>())?;
        if function.attrs.naked {
            work.text("naked", &mut self.piece)?;
            self.mismatch(work)?;
        }
        work.admit(1, size_of::<trust_ir::Visibility>())?;
        if function.visibility != trust_ir::Visibility::Default {
            work.text("visibility ", &mut self.piece)?;
            work.text(render::visibility(function.visibility), &mut self.piece)?;
            self.mismatch(work)?;
        }
        work.admit(1, size_of::<Option<&String>>())?;
        if let Some(section) = &function.section {
            work.text("section ", &mut self.piece)?;
            work.quoted(section, &mut self.piece)?;
            self.mismatch(work)?;
        }
        work.admit(1, size_of::<Option<&String>>())?;
        if let Some(path) = &function.display_path
            && !work.equal(path, entry.def_path)?
        {
            work.text("display path ", &mut self.piece)?;
            work.quoted(path, &mut self.piece)?;
            self.mismatch(work)?;
        }
        Ok(())
    }
}
