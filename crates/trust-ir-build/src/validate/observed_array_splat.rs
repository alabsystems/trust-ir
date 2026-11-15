// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual module ArraySplat element/canonical-spelling rule, constant in n.
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
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    ty: String,
    reason: String,
    op: String,
    role: String,
    expected: String,
    actual: String,
    location: String,
    spelling: String,
    errors: Vec<ValidationError>,
}
/// Preserve actual array/element lookup, exact known element type with original
/// TOP-refinement defer, then zero-length canonical spelling in that order.
/// Declared n is compared only, never expanded or exempted. This diagnostic is
/// not layout/SSA/refinement/nominal/origin/source/module/proof authority. All
/// work uses the original supplied session/site/fuel/grant/deadline/TLS; every
/// full child String and prior error stays owned before the next fallible fee.
/// Operational refusal drains all output, never a smaller accepting Vec. Full
/// caller adoption/cleanup and physical std/allocator/panic/hard bounds OPEN.
pub(super) fn validate_array_splat_observed<O: ExecutionObserver>(
    module: &Module,
    inst: &Inst,
    values: &ObservedValueTypes,
    block: BlockId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, inst, values, block, &mut work);
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
        work.flat(take(&mut self.ty));
        work.flat(take(&mut self.reason));
        work.flat(take(&mut self.op));
        work.flat(take(&mut self.role));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
        work.flat(take(&mut self.location));
        work.flat(take(&mut self.spelling));
    }
}
