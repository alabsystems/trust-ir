// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual typed-constant symbol queries over one exact catalog/layout source.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::size_of;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod queries;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
/// Same borrowed source for every original function/global/weak symbol query.
/// Lazy complete source scans replace only redundant borrowed-key indexes.
/// This context confers no module/initializer/type/proof/source authenticity;
/// every required rule and full original caller census stays mandatory.
pub(super) struct ObservedConstantSymbols<'l, 'm> {
    layouts: &'l trust_ir::LayoutTable<'m>,
    functions: &'l ModuleFunctionCatalog<'m>,
}
impl<'l, 'm> ObservedConstantSymbols<'l, 'm> {
    pub(super) fn new_observed<O: ExecutionObserver>(
        layouts: &'l trust_ir::LayoutTable<'m>,
        functions: &'l ModuleFunctionCatalog<'m>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        let mut work = Work { session, site };
        work.admit(8, size_of::<Self>())?;
        if !core::ptr::eq(layouts.module(), functions.source_module()) {
            return Err(ObservedValueError::InvalidRange);
        }
        work.publication(size_of::<Self>())?;
        Ok(Self { layouts, functions })
    }
    pub(super) fn module(&self) -> &'m Module {
        self.layouts.module()
    }
    pub(super) fn layouts(&self) -> &'l trust_ir::LayoutTable<'m> {
        self.layouts
    }
    pub(super) fn functions(&self) -> &'l ModuleFunctionCatalog<'m> {
        self.functions
    }
    /// No input/index graph is owned here. Do not conflate this fixed borrowed
    /// context disposal with its original catalog/layout/module caller duties.
    pub(super) fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        session.retirement_step(site, size_of::<Self>().saturating_add(1));
        drop(self);
        session.retirement_poll(site);
        Work { session, site }.publication(0)
    }
}
