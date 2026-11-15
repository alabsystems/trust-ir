// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'m> ObservedConstantSymbols<'_, 'm> {
    /// Exact original weak-set membership, not an authority capability. Every
    /// actual physical function row and eligible variable name is observed;
    /// duplicate names are existential just like the original borrowed set.
    pub(in crate::validate) fn weak_symbol_observed<O: ExecutionObserver>(
        &self,
        symbol: &str,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<usize>() + size_of::<bool>())?;
        let mut at = 0;
        let answer = loop {
            let Some(function) = work.at(&self.module().functions, at)? else {
                break false;
            };
            // is_weak_declaration is exactly ExternalWeak+blocks.is_empty,
            // two fixed tags/metadata reads, never source-name/body traversal.
            work.admit(8, size_of::<bool>())?;
            if function.is_weak_declaration() && work.equal(&function.name, symbol)? {
                break true;
            }
            work.next(&mut at)?;
        };
        work.publication(size_of::<bool>())?;
        Ok(answer)
    }
    /// Exact target_global result and error order: count ALL same-name actual
    /// globals and functions, require one global/zero functions, then defined,
    /// non-TLS, non-interposable. No copied symbol table or candidate closure.
    pub(in crate::validate) fn target_global_observed<O: ExecutionObserver>(
        &self,
        symbol: &str,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Result<&'m trust_ir::Global, PointerConstantRefusal>> {
        let mut work = Work { session, site };
        work.admit(
            1,
            3 * size_of::<usize>() + size_of::<Option<&trust_ir::Global>>(),
        )?;
        let (mut globals, mut functions, mut first, mut at) = (0, 0, None, 0);
        while let Some(global) = work.at(&self.module().globals, at)? {
            if work.equal(&global.name, symbol)? {
                work.count(&mut globals)?;
                work.admit(1, size_of::<Option<&trust_ir::Global>>())?;
                if first.is_none() {
                    first = Some(global);
                }
            }
            work.next(&mut at)?;
        }
        let mut at = 0;
        while let Some(function) = work.at(&self.module().functions, at)? {
            if work.equal(&function.name, symbol)? {
                work.count(&mut functions)?;
            }
            work.next(&mut at)?;
        }
        work.admit(
            16,
            size_of::<Result<&trust_ir::Global, PointerConstantRefusal>>(),
        )?;
        let result = if globals == 0 {
            Err(PointerConstantRefusal::NotAModuleGlobal)
        } else if globals != 1 || functions != 0 {
            Err(PointerConstantRefusal::AmbiguousSymbol { globals, functions })
        } else {
            let global = first.ok_or(ObservedValueError::InvalidRange)?;
            if global.initializer.is_none() {
                Err(PointerConstantRefusal::GlobalNotDefined)
            } else if global.tls.is_some() {
                Err(PointerConstantRefusal::ThreadLocal)
            } else if global.linkage.is_interposable() {
                Err(PointerConstantRefusal::InterposableLinkage {
                    linkage: global.linkage,
                })
            } else {
                Ok(global)
            }
        };
        work.publication(size_of::<Result<&trust_ir::Global, PointerConstantRefusal>>())?;
        Ok(result)
    }
}
