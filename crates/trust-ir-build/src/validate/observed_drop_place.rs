// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual module Drop/DropInvoke place-type diagnostic, one Refine layer only.
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
    op: String,
    role: String,
    expected: String,
    actual: String,
    errors: Vec<ValidationError>,
}
/// Exact original local diagnostic only: unknown values skip; the place must
/// be Ptr after the actual Module::representation_ty's ONE outer Refine lookup.
/// A nested Refine remains Refine and is refused here, not recursively peeled.
/// No layout/glue/SSA/refinement/edge/module/proof/source authority is issued.
/// All actual value/type/display/output steps use the supplied original
/// session/site/fuel. Own full Strings/prior errors retire before any outer
/// operational error; no accepting fallback or owner/grant/deadline/TLS reset.
/// Physical std/allocator/panic/hard-time and caller input disposal stay OPEN.
pub(super) fn validate_drop_place_observed<O: ExecutionObserver>(
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
        work.flat(take(&mut self.op));
        work.flat(take(&mut self.role));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
    }
}
