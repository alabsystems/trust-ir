// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn function_item<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, '_>,
        id: FuncId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let function = symbols
            .functions()
            .unique_observed(id, work.session, work.site)?;
        if let Some(function) = function {
            if work
                .at(&symbols.module().func_types, function.ty.as_usize())?
                .is_some()
            {
                return Ok(());
            }
            work.text("function item func.", &mut self.actual)?;
            work.unsigned(u128::from(id.index()), &mut self.actual)?;
            work.text(" has missing signature functy.", &mut self.actual)?;
            work.unsigned(u128::from(function.ty.index()), &mut self.actual)?;
        } else {
            work.text("missing or ambiguous function item func.", &mut self.actual)?;
            work.unsigned(u128::from(id.index()), &mut self.actual)?;
        }
        work.text(
            "a unique function item with an actual signature",
            &mut self.expected,
        )?;
        self.mismatch_ready(work)
    }
    pub(super) fn structure<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        values: &[Constant],
        id: StructId,
        item: Item<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a [FieldDef]>> {
        let Some(def) = lookup::structure(module, id, work)? else {
            self.missing("struct.", id.index(), work)?;
            return Ok(None);
        };
        work.admit(2, size_of::<bool>())?;
        if values.len() != def.fields.len() {
            self.mismatch(item, work)?;
            return Ok(None);
        }
        Ok(Some(&def.fields))
    }
    pub(super) fn record<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        len: usize,
        id: RecordId,
        item: Item<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a [FieldDef]>> {
        let Some(def) = lookup::record(module, id, work)? else {
            self.missing("record.", id.index(), work)?;
            return Ok(None);
        };
        work.admit(2, size_of::<bool>())?;
        if len != def.fields.len() {
            self.mismatch(item, work)?;
            return Ok(None);
        }
        Ok(Some(&def.fields))
    }
    pub(super) fn function<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, '_>,
        id: FuncId,
        signature: FuncTyId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(f) = symbols
            .functions()
            .unique_observed(id, work.session, work.site)?
        else {
            work.text("a unique module-owned function item", &mut self.expected)?;
            work.text("missing or ambiguous func.", &mut self.actual)?;
            work.unsigned(u128::from(id.index()), &mut self.actual)?;
            return self.mismatch_ready(work);
        };
        work.admit(1, size_of::<bool>())?;
        if f.ty != signature {
            work.text("functy.", &mut self.expected)?;
            work.unsigned(u128::from(f.ty.index()), &mut self.expected)?;
            work.text(" for func.", &mut self.expected)?;
            work.unsigned(u128::from(id.index()), &mut self.expected)?;
            work.text("functy.", &mut self.actual)?;
            work.unsigned(u128::from(signature.index()), &mut self.actual)?;
            self.mismatch_ready(work)?;
        }
        Ok(())
    }
}
