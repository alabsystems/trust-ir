// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact original obligation scope/site resolution; no proof authority.
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
use trust_ir::proof::ProofObligation;
mod lookup;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Resolution<'a> {
    Missing,
    Unique(&'a Function),
    Ambiguous,
}
#[derive(Default)]
struct State {
    errors: Vec<ValidationError>,
}
/// Original scope-first/site-second rule. Function IDs must be unique in the
/// exact source module; blocks keep the original first physical match. No
/// source names, descriptions, signatures or formula/type payloads are read.
/// Fixed kind/instruction pattern tables remain the unchanged ordinary ones.
/// Actual table walks, requested output growth/transport, error retirement and
/// final publication use only the supplied original session/site. This is
/// diagnostic data, not evidence that a module or proof is valid.
pub(crate) fn validate_module_obligation_sites_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, &mut work);
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
    fn run<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        let mut index = 0usize;
        while let Some(obligation) = work.at(&module.proof_obligations, index)? {
            self.row(module, obligation, work)?;
            work.next(&mut index)?;
        }
        Ok(())
    }
    fn row<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        obligation: &ProofObligation,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<FuncId>>())?;
        if let Some(scope) = obligation.function {
            let reason = match work.resolve(module, scope)? {
                Resolution::Unique(_) => None,
                Resolution::Missing => Some("no such function"),
                Resolution::Ambiguous => Some("the id names more than one function"),
            };
            if let Some(reason) = reason {
                self.prepare(work)?;
                self.errors
                    .push(ValidationError::ObligationFunctionScopeUnresolved {
                        obligation: obligation.id.index(),
                        function: scope.index(),
                        reason,
                    });
                return Ok(());
            }
        }
        work.admit(1, size_of::<Option<&trust_ir::proof::ObligationSite>>())?;
        let Some(site) = &obligation.site else {
            return Ok(());
        };
        work.admit(2, size_of::<Option<FuncId>>() + 2 * size_of::<FuncId>())?;
        if let Some(scope) = obligation.function
            && scope != site.function
        {
            self.prepare(work)?;
            self.errors
                .push(ValidationError::ObligationSiteFunctionMismatch {
                    obligation: obligation.id.index(),
                    site_function: site.function.index(),
                    scope_function: scope.index(),
                });
            return Ok(());
        }
        let Resolution::Unique(function) = work.resolve(module, site.function)? else {
            return self.range(obligation, "no such function", work);
        };
        let Some(block) = work.block(function, site.block)? else {
            return self.range(obligation, "no such block in that function", work);
        };
        work.admit(1, size_of::<usize>())?;
        let index =
            usize::try_from(site.inst_index).map_err(|_| ObservedValueError::CapacityOverflow)?;
        let Some(node) = work.at(&block.body, index)? else {
            return self.range(
                obligation,
                "instruction index past the end of the block",
                work,
            );
        };
        // These are only finite discriminant tables (current67 instructions,
        //14 check shapes and fixed obligation variants), never a variable
        // payload or recursive formatter. Price all three table calls first.
        work.admit(256, size_of::<bool>() + 2 * size_of::<&str>())?;
        if !obligation_kind_admits_site_instruction(&obligation.kind, &node.inst) {
            let kind = obligation_kind_name(&obligation.kind);
            let op = instruction_kind(&node.inst);
            self.prepare(work)?;
            self.errors
                .push(ValidationError::ObligationSiteKindMismatch {
                    obligation: obligation.id.index(),
                    kind,
                    op,
                });
        }
        Ok(())
    }
    fn range<O: ExecutionObserver>(
        &mut self,
        obligation: &ProofObligation,
        reason: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<&trust_ir::proof::ObligationSite>>())?;
        let site = obligation
            .site
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        self.prepare(work)?;
        self.errors.push(ValidationError::ObligationSiteOutOfRange {
            obligation: obligation.id.index(),
            function: site.function.index(),
            block: site.block.index(),
            inst_index: site.inst_index,
            reason,
        });
        Ok(())
    }
    fn prepare<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())
    }
}
