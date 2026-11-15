// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original actual signature getter and Return/CoroSuspend value agreement.
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
mod signature;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    expected: String,
    actual: String,
    errors: Vec<ValidationError>,
}
pub(super) use signature::function_signature_observed;
/// Exact original return agreement, shared by Return and a single-value
/// CoroSuspend. Actual original signature/value-map/context remains the full
/// caller's duty. Operational failure is outer Err, never unknown/skipped
/// value or missing-signature success. Top-level refinements defer exactly to
/// the mandatory full consumption rule; no predicate truth is supplied here.
/// Complete type Display children and prior errors stay owned through final
/// transfer or exhaustive same-session retirement. No full signature/edge/
/// module/source/proof authority, new owner/grant/deadline/TLS/fuel. Full caller
/// adoption/input disposal and physical hard bounds remain OPEN.
pub(super) fn validate_return_instruction_observed<O: ExecutionObserver>(
    inst: &Inst,
    signature: &FuncTy,
    values: &ObservedValueTypes,
    block: BlockId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(inst, signature, values, block, &mut work);
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
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
    }
}
