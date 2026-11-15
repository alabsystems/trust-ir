// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original narrow codegen switch front, reusing the actual complete funnel.
use super::*;
#[cfg(test)]
mod tests;
#[derive(Default)]
struct Front<'m> {
    literals: State<'m>,
    layouts: Option<trust_ir::LayoutTable<'m>>,
    catalog: Option<ModuleFunctionCatalog<'m>>,
}
/// Only the actual narrow front: all original module/table/catalog setup, then
/// actual switches. This deliberately does NOT visit global/Const literals or
/// derive any module, SSA, type, proof, input/source or codegen authority.
/// Exact canonical/typed child, lazy unique-catalog selector maps and original
/// diagnostics are shared with the full source literal constituent. All own
/// context/map/error output stays original-owned through transfer or cleanup.
/// No owner/grant/deadline/TLS/fuel/flag/reset/callback/accepting fallback.
pub(in crate::validate) fn codegen_switch_case_literal_errors_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<Front<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = Front::default();
    let result = state.run(module, &mut work);
    state.literals.retire_scratch(&mut work);
    let retirement = state.retire_context(&mut work);
    match result.and(retirement).and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.literals.errors)),
        Err(error) => {
            let _ = retire_validation_errors_observed(
                take(&mut state.literals.errors),
                work.session,
                work.site,
            );
            Err(work.terminal(error))
        }
    }
}
impl<'m> Front<'m> {
    fn run<O: ExecutionObserver>(&mut self, module: &'m Module, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<Option<trust_ir::LayoutTable<'m>>>())?;
        self.layouts = Some(trust_ir::LayoutTable::new_observed(
            module,
            work.session,
            work.site,
        )?);
        work.admit(1, size_of::<Option<ModuleFunctionCatalog<'m>>>())?;
        self.catalog = Some(ModuleFunctionCatalog::new_observed(
            module,
            work.session,
            work.site,
        )?);
        let layouts = self
            .layouts
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        let catalog = self
            .catalog
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        let symbols =
            ObservedConstantSymbols::new_observed(layouts, catalog, work.session, work.site)?;
        let result = self.literals.switches_only(&symbols, work);
        let retirement = symbols.retire_observed(work.session, work.site);
        result.and(retirement)
    }
    fn retire_context<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.step(size_of::<Option<ModuleFunctionCatalog<'m>>>().saturating_add(1));
        let result = match self.catalog.take() {
            Some(catalog) => catalog.retire_observed(work.session, work.site),
            None => Ok(()),
        };
        work.poll();
        work.step(size_of::<Option<trust_ir::LayoutTable<'m>>>().saturating_add(1));
        if let Some(layouts) = self.layouts.take() {
            // This exact constructor leaves the ordinary memo uninitialized. Every
            // query above uses the observed query's independently owned Work;
            // none populates this table's ordinary memo. Only the fixed None
            // table header/Mutex/Option are retired here. Original
            // borrowed module/input and physical allocator/drop bounds remain
            // outside this logical primitive. Never route an ordinary query
            // into this table without extending its owned retirement contract.
            work.fixed(layouts);
        }
        work.poll();
        result
    }
}
impl<'m> State<'m> {
    fn switches_only<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, 'm>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut f = 0;
        while let Some(function) = work.at(&symbols.module().functions, f)? {
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    work.admit(8, size_of::<Option<ValueId>>())?;
                    if let Inst::Switch { value, cases, .. } = &node.inst {
                        self.block_location(function, block.id, work)?;
                        self.switch(symbols, function, *value, cases, work)?;
                        work.flat(take(&mut self.location));
                        work.admit(1, 0)?;
                    }
                    work.next(&mut n)?;
                }
                work.next(&mut b)?;
            }
            self.retire_values(work);
            work.admit(1, 0)?;
            work.next(&mut f)?;
        }
        Ok(())
    }
}
