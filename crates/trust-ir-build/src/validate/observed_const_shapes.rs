// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Full original global/Const/Switch literal funnel under the original owner.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_constant_symbols::ObservedConstantSymbols;
use super::observed_typed_constants::validate_constant_against_ty_observed;
use super::observed_value_types::build_catalog_value_types_observed;
use super::*;
use core::mem::{size_of, take};
use trust_ir::ObservedNominalTypeReachability;
use trust_ir::constant::ConstantChildren;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod canonical;
mod codegen;
pub(super) use codegen::codegen_switch_case_literal_errors_observed;
mod diagnostics;
mod merge;
mod scan;
mod storage;
mod switches;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'m> {
    location: String,
    here: String,
    expected: String,
    actual: String,
    detail: String,
    canonical_current: Option<&'m Constant>,
    canonical_pending: Vec<ConstantChildren<'m>>,
    values: Option<ObservedValueTypes>,
    pending: Vec<ValidationError>,
    row: Option<ValidationError>,
    errors: Vec<ValidationError>,
}
/// Exact original handle-first global-storage, initializer, function/block
/// Const/Switch ordering. The optional nominal summary must be the original
/// complete census lane, never None after a stop; a foreign source is refused.
/// Switch inference is lazy once per actual function and duplicate-aware for
/// direct-call results. Integer canonicality precedes the full typed walk.
/// Whole child maps/errors and partial scratch stay original-owned through
/// transfer or complete cleanup. No owner/grant/deadline/TLS/fuel/flag/callback,
/// validated module/source/proof authority or physical hard bound is created.
pub(super) fn validate_const_shapes_observed<O: ExecutionObserver>(
    layouts: &trust_ir::LayoutTable<'_>,
    functions: &ModuleFunctionCatalog<'_>,
    nominal: Option<&ObservedNominalTypeReachability<'_>>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(
        8,
        size_of::<State<'_>>()
            + size_of::<Work<'_, '_, O>>()
            + size_of::<Option<&ObservedNominalTypeReachability<'_>>>(),
    )?;
    if let Some(nominal) = nominal
        && !core::ptr::eq(nominal.source_module(), layouts.module())
    {
        return Err(ObservedValueError::InvalidRange);
    }
    let symbols =
        ObservedConstantSymbols::new_observed(layouts, functions, work.session, work.site)?;
    let mut state = State::default();
    let result = state.run(&symbols, nominal, &mut work);
    state.retire_scratch(&mut work);
    let context_retirement = symbols.retire_observed(work.session, work.site);
    match result
        .and(context_retirement)
        .and_then(|()| work.publication())
    {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(e) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(e))
        }
    }
}
impl State<'_> {
    fn retire_canonical<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.fixed(self.canonical_current.take());
        loop {
            work.step(size_of::<Option<ConstantChildren<'_>>>().saturating_add(1));
            let Some(frame) = self.canonical_pending.pop() else {
                break;
            };
            work.fixed(frame);
        }
        work.fixed(take(&mut self.canonical_pending));
    }
    fn retire_values<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<ObservedValueTypes>>().saturating_add(1));
        if let Some(values) = self.values.take() {
            let _ = values.retire_observed(work.session, work.site);
        }
        work.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_canonical(work);
        self.retire_values(work);
        work.step(size_of::<Option<ValidationError>>().saturating_add(1));
        if let Some(row) = self.row.take() {
            let _ = retire_validation_error_observed(row, work.session, work.site);
        }
        let _ = retire_validation_errors_observed(take(&mut self.pending), work.session, work.site);
        work.flat(take(&mut self.location));
        work.flat(take(&mut self.here));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
        work.flat(take(&mut self.detail));
    }
}
