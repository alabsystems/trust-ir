// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact original handle/niche overlap diagnostic, with actual observed layouts.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use std::sync::Arc;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::shape::TyLayoutShape;
use trust_ir::ty::{EnumDef, EnumTagEncoding};
use trust_ir::{LayoutError, LayoutTable, ObservedNominalTypeReachability};
mod query;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    shape: Option<Arc<TyLayoutShape>>,
    error: Option<LayoutError>,
    name: String,
    detail: String,
    render: String,
    errors: Vec<ValidationError>,
}
/// Preserve original descriptor/variant/field order and malformed-length skips.
/// The enclosing full module caller must preserve census.handle and a present
/// original nominal summary. This borrowed table's exact module supplies all
/// rows. Actual nominal and layout traversals share the supplied owner/site;
/// an outer operational stop NEVER becomes semantic unavailable/overlap data.
/// Semantic unavailable or non-byte extent is conservatively overlapping as
/// before. This constituent grants no layout/runtime/type/module/proof authority.
///
/// Complete Arc/error/format children are retained before any further fallible
/// operation and consumed under the same original session. Strings/prior errors
/// stay owned through the last transfer; no shorter output is published on stop.
/// Borrowed table/summary/original input disposal and physical hard bounds remain
/// the original caller's obligations. No grant/deadline/TLS/fuel is renewed.
pub(super) fn validate_handle_enum_layouts_observed<O: ExecutionObserver>(
    layouts: &LayoutTable<'_>,
    nominal: &ObservedNominalTypeReachability<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(layouts, nominal, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State {
    fn retire_shape<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Arc<TyLayoutShape>>>() + 1);
        if let Some(shape) = self.shape.take() {
            let _ = shape.retire_arc_observed(work.session, work.site);
        }
        work.poll();
    }
    fn retire_error<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<LayoutError>>() + 1);
        if let Some(error) = self.error.take() {
            let _ = error.retire_observed(work.session, work.site);
        }
        work.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_shape(work);
        self.retire_error(work);
        work.flat(take(&mut self.name));
        work.flat(take(&mut self.detail));
        work.flat(take(&mut self.render));
    }
}
