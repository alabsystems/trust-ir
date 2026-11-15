// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original SeqMap forward-element signature rule, not legalization.
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
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    name: String,
    expected: String,
    actual: String,
    render: String,
    pending: Option<ValidationError>,
    errors: Vec<ValidationError>,
}
/// Exact original existence, actual signature, sequence element and fn(&mut T)
/// rule. Catalog supplies its actual module; module row and structural equality
/// are actually observed. Only redundant element Clone is replaced by borrowing.
/// No result callback/candidate/type ID can manufacture a declaration or module.
///
/// This is a diagnostic constituent, not proof of reversibility or permission
/// to skip mandatory nominal, scalar, edge, refinement or module validators.
/// Returned complete getter error and Display child enter owning State before
/// next fee. All prior errors/partial text drain on refusal in the same original
/// session/site; no shorter success/renewed grant/deadline/TLS/fuel. Successful
/// caller input/output disposal and physical std/allocator/hard bounds OPEN.
pub(super) fn validate_seq_map_observed<O: ExecutionObserver>(
    catalog: &ModuleFunctionCatalog<'_>,
    inst: &Inst,
    block: BlockId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(catalog, inst, block, &mut work);
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
    fn pending<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(
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
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.name));
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
