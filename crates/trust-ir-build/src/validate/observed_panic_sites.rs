// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original panic-site V1--V5 diagnostics under actual observation.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_returns::function_signature_observed;
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::{PanicLocation, PanicSite};
mod diagnostics;
mod location;
mod origin;
mod render;
mod shape;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    name: String,
    op: String,
    role: String,
    expected: String,
    actual: String,
    render: String,
    pending: Option<ValidationError>,
    errors: Vec<ValidationError>,
}
#[derive(Clone, Copy)]
struct Request<'a> {
    function: &'a Function,
    block: BlockId,
    index: u32,
    panic: &'a PanicSite,
}
/// Derive actual module/function/block/node from the bound catalog and physical
/// coordinates. Preserve V3/V5 before entry resolution, exact entry shape and
/// strict location equality (no refinement defer). Actual first-definition and
/// global symbol-name scans are observed inside their real work. No candidate
/// resolver/callback, authority, owner/grant/deadline/TLS/fuel reset or accepting
/// operational fallback. All pending errors/Strings stay owned until transfer
/// or complete original-session retirement; mandatory SSA/weak/module/authority
/// validation and physical std/allocator/panic/hard-time/caller duties stay OPEN.
pub(super) fn validate_panic_site_at_observed<O: ExecutionObserver>(
    catalog: &ModuleFunctionCatalog<'_>,
    function: usize,
    block: usize,
    instruction: usize,
    values: &ObservedValueTypes,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(catalog, function, block, instruction, values, &mut work);
    state.retire(&mut work);
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
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.name));
        work.flat(take(&mut self.op));
        work.flat(take(&mut self.role));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
        work.flat(take(&mut self.render));
        work.step(size_of::<Option<ValidationError>>() + 1);
        if let Some(error) = self.pending.take() {
            let _ = retire_validation_error_observed(error, work.session, work.site);
        }
        work.poll();
    }
}
