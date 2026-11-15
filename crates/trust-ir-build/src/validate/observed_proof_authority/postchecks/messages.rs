// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Post {
    pub(super) fn name<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        id: FuncId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        match catalog.unique_observed(id, w.session, w.site)? {
            Some(function) => self.text(&function.name, w),
            None => {
                self.text("fn#", w)?;
                self.number(id.index(), w)
            }
        }
    }
    fn describe<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        id: FuncId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        match catalog.unique_observed(id, w.session, w.site)? {
            Some(function) => {
                self.text("`", w)?;
                self.text(&function.name, w)?;
                self.text("` (fn#", w)?;
                self.number(id.index(), w)?;
                self.text(")", w)
            }
            None => {
                self.text("fn#", w)?;
                self.number(id.index(), w)
            }
        }
    }
    pub(super) fn imported<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        row: &TvRechecked,
        callee: FuncId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.text("InheritedFromCallee row on obligation #", w)?;
        self.number(row.obligation.index(), w)?;
        self.text(" names ", w)?;
        self.describe(catalog, callee, w)?;
        self.text(" through an import: cross-crate TV composition is authenticated only by validate_linked_module, and an import claim never grounds a kernel-tier clean_backend_tv call edge — REJECTED", w)?;
        self.failure(row.obligation, w)
    }
    pub(super) fn uncalled<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        row: &TvRechecked,
        callee: FuncId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.text("InheritedFromCallee row names ", w)?;
        self.describe(catalog, callee, w)?;
        self.text(", which `", w)?;
        self.name(catalog, row.function, w)?;
        self.text(
            "` never calls — the composition row is not bound to a call edge, REJECTED",
            w,
        )?;
        self.failure(row.obligation, w)
    }
    pub(super) fn repeated<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        row: &TvRechecked,
        callee: FuncId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.text("two InheritedFromCallee rows on obligation #", w)?;
        self.number(row.obligation.index(), w)?;
        self.text(" name callee ", w)?;
        self.describe(catalog, callee, w)?;
        self.text(" — one row per call edge, REJECTED", w)?;
        self.failure(row.obligation, w)
    }
    pub(super) fn ungrounded<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        row: &TvRechecked,
        callee: FuncId,
        inherited: ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.text("callee ", w)?;
        self.describe(catalog, callee, w)?;
        self.text(" has no kernel-rechecked clean_backend_tv obligation of its own: the InheritedFromCallee row on obligation #", w)?;
        self.number(row.obligation.index(), w)?;
        self.text(" cites obligation #", w)?;
        self.number(inherited.index(), w)?;
        self.text(", which is not a Certified TranslationValidation obligation on that callee whose clean_backend_tv recheck passed — REJECTED", w)?;
        self.failure(row.obligation, w)
    }
    pub(super) fn missing<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        row: &TvRechecked,
        callee: FuncId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.text("callee ", w)?;
        self.describe(catalog, callee, w)?;
        self.text(" is called by `", w)?;
        self.name(catalog, row.function, w)?;
        self.text("` but no InheritedFromCallee row on obligation #", w)?;
        self.number(row.obligation.index(), w)?;
        self.text(" names it — the parametric equation is not grounded at the callee actually called, REJECTED", w)?;
        self.failure(row.obligation, w)
    }
}
