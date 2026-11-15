// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original module function-contract loop, not complete module authority.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_summary::validate_function_summary_observed;
use super::*;
use core::mem::{size_of, take};
use std::vec::IntoIter;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod aggregate;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    errors: Vec<ValidationError>,
    batch: Option<IntoIter<ValidationError>>,
    pending: Option<ValidationError>,
}
/// Exact physical function loop from the original full module validator:
/// optional summary, then its body effects, then Rust variadic ABI rule.
/// Every child and aggregation uses the supplied original session/site and
/// unchanged import policy. Complete module/body/proof/source authority is
/// a separate enclosing obligation; these diagnostic rows mint none of it.
/// Successful diagnostics and immutable input disposal remain caller-owned.
pub(crate) fn validate_module_function_contracts_observed<O: ExecutionObserver>(
    module: &Module,
    policy: ImportPolicy<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, policy, &mut work);
    state.finish(result, &mut work)
}
impl State {
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        policy: ImportPolicy<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<Option<&Function>>())?;
            let Some(function) = module.functions.get(index) else {
                return Ok(());
            };
            work.admit(1, size_of::<Option<&trust_ir::FunctionSummary>>())?;
            if let Some(summary) = &function.summary {
                self.prepare(work)?;
                self.batch = Some(
                    validate_function_summary_observed(
                        module,
                        function,
                        summary,
                        policy,
                        work.session,
                        work.site,
                    )?
                    .into_iter(),
                );
                self.merge(work)?;
                self.prepare(work)?;
                self.batch = Some(
                    validate_effect_summary_observed(
                        module,
                        function,
                        policy,
                        work.session,
                        work.site,
                    )?
                    .into_iter(),
                );
                self.merge(work)?;
            }
            self.prepare(work)?;
            self.batch = Some(
                validate_function_rust_abi_is_not_variadic_observed(
                    module,
                    function,
                    work.session,
                    work.site,
                )?
                .into_iter(),
            );
            self.merge(work)?;
            work.admit(1, size_of::<usize>())?;
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
    fn prepare<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        // Price the returned Vec and its immediate full iterator capture
        // before invoking a child that can return owned diagnostics.
        work.admit(
            3,
            size_of::<Vec<ValidationError>>()
                + size_of::<Option<IntoIter<ValidationError>>>()
                + size_of::<Option<ValidationError>>(),
        )?;
        if self.batch.is_some() || self.pending.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(work);
        match result.and_then(|()| work.publication()) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                let _ = retire_validation_errors_observed(
                    take(&mut self.errors),
                    work.session,
                    work.site,
                );
                Err(work.terminal(error))
            }
        }
    }
}
