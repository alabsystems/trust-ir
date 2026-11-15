// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original entry-parameter arity/non-refinement equality diagnostic.
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
    render: String,
    name: String,
    expected: String,
    actual: String,
    errors: Vec<ValidationError>,
}
/// Same actual module signature and first physical entry block. Bodyless,
/// missing signature or absent entry is the original no-diagnostic lane of
/// THIS constituent only: the mandatory signature/structure validators still
/// refuse those defects. Top-level refinement-involving positions defer only
/// to the mandatory full consumption rule, never establish its truth here.
///
/// Borrow original types instead of constructing a redundant cloned list;
/// every actual equality and full diagnostic Display traversal is observed by
/// this same supplied original session/site. Owning Display child, partial
/// fields and prior errors remain held through last transfer or full retirement.
/// No full module/signature/refinement/source/proof authority or owner/grant/
/// deadline/TLS/fuel renewal. Caller input/disposal and physical bounds OPEN.
pub(super) fn validate_entry_params_observed<O: ExecutionObserver>(
    module: &Module,
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, function, &mut work);
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
        work.flat(take(&mut self.render));
        work.flat(take(&mut self.name));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
    }
}
