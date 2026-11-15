// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original whole module type-reference inventory and nominal census.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod batch;
mod inventory;
mod location;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use location::Location;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Frame<'a> {
    Visit(&'a Ty),
    Children(&'a [Ty], usize),
}
#[derive(Default)]
struct State<'a> {
    location: String,
    frames: Vec<Frame<'a>>,
    roots: Vec<&'a Ty>,
    errors: Vec<ValidationError>,
    batch: Vec<ValidationError>,
    row: Option<ValidationError>,
    child_census: NominalCensus,
    census: NominalCensus,
}
/// The exact original `validate_type_table_references` stored occurrence walk,
/// locations, one-node checks and census, using actual observed lexical/registry
/// and type traversal under this same original session/site. Inline children
/// use iterative preorder; module-table IDs are checked, never recursively
/// followed. Instruction roots use the actual observed borrowed collector,
/// followed by actual type-valued dialect attributes in original source order.
/// No constants, bodies or source module are cloned.
///
/// Returned child batches/borrowed roots are immediately held before any next
/// fallible fee; pending rows, remaining batches, raw location and prior errors
/// remain owned through transfer or full sticky original-owner retirement.
/// This diagnostic/census does not solve nominal reachability, admit a runtime
/// registry or establish type/module/kernel/proof/source authority. The rest
/// of the ordinary validator is mandatory. Successful caller input/result
/// disposal and physical std/Unicode/allocator/deallocator/OOM/panic/unwind/
/// RSS/hardtime remain OPEN. No owner/grant/deadline/TLS/fuel is reset.
pub(super) fn validate_type_table_references_observed<O: ExecutionObserver>(
    module: &Module,
    registry: &HandleRegistry,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<(Vec<ValidationError>, NominalCensus)> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, registry, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok((take(&mut state.errors), state.census)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State<'_> {
    fn node<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        registry: &HandleRegistry,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            3,
            size_of::<Vec<ValidationError>>()
                + 2 * size_of::<NominalCensus>()
                + size_of::<Option<ValidationError>>(),
        )?;
        if self.batch.capacity() != 0 || self.row.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        // Complete owning tuple is assigned before the next fallible fee.
        (self.batch, self.child_census) = validate_type_reference_node_observed(
            module,
            registry,
            ty,
            &self.location,
            work.session,
            work.site,
        )?;
        work.admit(2, 2 * size_of::<NominalCensus>())?;
        self.census.dialect |= self.child_census.dialect;
        self.census.handle |= self.child_census.handle;
        self.append(work)
    }
    fn retire_roots<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.step(size_of::<Option<&Ty>>().saturating_add(1));
            let Some(_) = self.roots.pop() else { break };
            work.step(size_of::<&Ty>().saturating_add(1));
        }
        work.step(size_of::<Vec<&Ty>>().saturating_add(1));
        drop(take(&mut self.roots));
        work.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.location));
        self.retire_roots(work);
        loop {
            work.step(size_of::<Option<Frame<'_>>>().saturating_add(1));
            let Some(_) = self.frames.pop() else { break };
            work.step(size_of::<Frame<'_>>().saturating_add(1));
        }
        work.step(size_of::<Vec<Frame<'_>>>().saturating_add(1));
        drop(take(&mut self.frames));
        work.poll();
        work.step(size_of::<Option<ValidationError>>().saturating_add(1));
        if let Some(row) = self.row.take() {
            let _ = retire_validation_error_observed(row, work.session, work.site);
        }
        self.retire_batch(work);
        work.poll();
    }
}
