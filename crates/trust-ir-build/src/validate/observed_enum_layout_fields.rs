// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original descriptor field-list, field-layout and overlapping-pair checks.
use super::*;
use core::mem::{size_of, take};
use std::sync::Arc;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::shape::TyLayoutShape;
use trust_ir::ty::{EnumDef, EnumLayoutDescriptor};
use trust_ir::{LayoutError, LayoutTable};
mod bounds;
mod field;
mod query;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
mod text;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Summary {
    known: bool,
    size: Option<u64>,
    align: Option<u64>,
}
#[derive(Default)]
struct State<'m> {
    table: Option<LayoutTable<'m>>,
    shape: Option<Arc<TyLayoutShape>>,
    error: Option<LayoutError>,
    reason: Option<String>,
    tytext: Option<String>,
    location: String,
    expected: String,
    actual: String,
    ranges: Vec<(usize, u64, u64)>,
    errors: Vec<ValidationError>,
}
/// Exact original FIELD constituent only. The enclosing enum pass supplies its
/// actual enum/descriptor; name, discriminant, global alignment and encoding
/// checks remain that pass's responsibility. Missing-size zero fallback is
/// spelling-only, without resolving known-zero structs or refinement wrappers.
///
/// Every returned Arc/error/type-display String remains owned before later
/// fallible work. Refusal consumes all query scratch, pending/completed text,
/// ranges and diagnostics; no shorter accepting list or authority is returned.
/// This fresh private table uses only observed queries, leaving ordinary Memo
/// empty. General populated-table and old private Work retirement/pricing, full
/// enum/module/native/source/proof authority, successful caller/input disposal
/// and physical std/allocator/deallocator/OOM/panic/unwind/RSS/hardtime stay OPEN.
pub(super) fn validate_enum_layout_fields_observed<O: ExecutionObserver>(
    module: &Module,
    enm: &EnumDef,
    layout: &EnumLayoutDescriptor,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.run(module, enm, layout, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication(1, size_of::<Vec<ValidationError>>())) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State<'_> {
    fn retire_query<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Arc<TyLayoutShape>>>().saturating_add(1));
        if let Some(shape) = self.shape.take() {
            let _ = shape.retire_arc_observed(work.session, work.site);
        }
        work.poll();
        work.step(size_of::<Option<LayoutError>>().saturating_add(1));
        if let Some(error) = self.error.take() {
            let _ = error.retire_observed(work.session, work.site);
        }
        work.poll();
        retire_text_slot(&mut self.reason, work);
        retire_text_slot(&mut self.tytext, work);
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_query(work);
        work.retire_text(take(&mut self.location));
        work.retire_text(take(&mut self.expected));
        work.retire_text(take(&mut self.actual));
        self.retire_ranges(work);
        work.step(size_of::<Option<LayoutTable<'_>>>().saturating_add(1));
        drop(self.table.take());
        work.poll();
    }
    fn retire_ranges<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.step(size_of::<Option<(usize, u64, u64)>>().saturating_add(1));
            let Some(row) = self.ranges.pop() else { break };
            work.fixed(row);
        }
        work.step(size_of::<Vec<(usize, u64, u64)>>().saturating_add(1));
        drop(take(&mut self.ranges));
        work.poll();
    }
}
fn retire_text_slot<O: ExecutionObserver>(slot: &mut Option<String>, work: &mut Work<'_, '_, O>) {
    work.step(size_of::<Option<String>>().saturating_add(1));
    if let Some(text) = slot.take() {
        work.retire_text(text);
    }
    work.poll();
}
