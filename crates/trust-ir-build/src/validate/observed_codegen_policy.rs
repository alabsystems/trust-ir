// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual configuration-selected diagnostic leaves; never a license/replay verdict.
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
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
pub(super) enum Rule {
    GateEvidence,
    GlobalAsm,
    PanicKinds,
    PanicSites,
}
#[derive(Default)]
struct State {
    text: String,
    pending: Option<ValidationError>,
    errors: Vec<ValidationError>,
}
/// One complete original diagnostic leaf only. The enclosing caller retains
/// exact config ordering and every structural/license/replay check. No decoded
/// certificate authority, recognized gate, policy flag or candidate callback is
/// accepted here; operational refusal never returns a smaller diagnostic list.
pub(super) fn codegen_policy_errors_observed<O: ExecutionObserver>(
    module: &Module,
    rule: Rule,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut w = Work { session, site };
    w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, rule, &mut w);
    state.finish(result, &mut w)
}
impl State {
    fn emit<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        w.reserve(&mut self.errors)?;
        w.admit(
            1,
            size_of::<ValidationError>() + size_of::<Option<ValidationError>>(),
        )?;
        self.errors.push(
            self.pending
                .take()
                .ok_or(ObservedValueError::InvalidRange)?,
        );
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<String>());
        w.flat(take(&mut self.text));
        w.record(1, size_of::<Option<ValidationError>>());
        if let Some(error) = self.pending.take() {
            let _ = retire_validation_error_observed(error, w.session, w.site);
        }
        w.poll();
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        w: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(w);
        match result.and_then(|()| w.publication(size_of::<Vec<ValidationError>>())) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                w.record(1, size_of::<Vec<ValidationError>>());
                let _ =
                    retire_validation_errors_observed(take(&mut self.errors), w.session, w.site);
                Err(w.terminal(error))
            }
        }
    }
}
// Mandatory original retirement_record8 and current primitive profiles must be
// joined before compilation. All physical allocator/deallocator/std/RSS/OOM/
// panic/unwind/hard100ms and original caller source/result disposal remain OPEN.
