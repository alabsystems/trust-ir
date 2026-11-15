// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual foreign handle-origin policy; no import authentication is minted.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::ObservedNominalTypeReachability;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod policy;
mod storage;
#[cfg(test)]
pub(crate) mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    name: String,
    handles: String,
    detail: String,
    errors: Vec<ValidationError>,
}
/// Exact ordinary bodyless/unpinned/handle-reaching rule. The mandatory census
/// and nominal-summary construction remain the enclosing original caller's
/// responsibility; a stopped query cannot choose a no-handle lane. Actual
/// observed lookup, graph queries and sealed import outcomes share this same
/// original owner/site. This only reports diagnostics, never authenticates a
/// claim or grants type/module/source/proof authority.
///
/// Complete diagnostic child output is immediately State-owned. Every partial
/// field and prior row is fully drained on failure before typed refusal, and
/// only the complete vector is published after scratch retirement. Physical
/// hard bounds and successful original input/result disposal remain OPEN.
pub(super) fn validate_handle_foreign_declarations_observed<O: ExecutionObserver>(
    module: &Module,
    registry: &HandleRegistry,
    nominal_types: &ObservedNominalTypeReachability<'_>,
    import_policy: ImportPolicy<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, registry, nominal_types, import_policy, &mut work);
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
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        registry: &HandleRegistry,
        nominal: &ObservedNominalTypeReachability<'_>,
        policy: ImportPolicy<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0usize;
        while let Some(function) = work.at(&module.functions, at)? {
            self.function(module, function, registry, nominal, policy, work)?;
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn function<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        registry: &HandleRegistry,
        nominal: &ObservedNominalTypeReachability<'_>,
        policy: ImportPolicy<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<bool>())?;
        if !function.is_declaration() {
            return Ok(());
        }
        if registry
            .entry_for_symbol_observed(&function.name, work.session, work.site)?
            .is_some()
        {
            return Ok(());
        }
        // func_type is exactly a single indexed Vec::get, with no name fallback.
        work.admit(
            1,
            size_of::<trust_ir::value::FuncTyId>() + size_of::<Option<&FuncTy>>(),
        )?;
        let Some(signature) = module.func_type(function.ty) else {
            return Ok(());
        };
        if !self.reaches_handle(signature, nominal, work)? {
            return Ok(());
        }
        if !self.policy(function, policy, work)? {
            return Ok(());
        }
        // Hold the complete returned owned text before name copying, output
        // allocation or any further fee. No following child can drop it early.
        self.handles = reachable_handles_text_observed(
            module,
            &signature.params,
            &signature.returns,
            work.session,
            work.site,
        )?;
        work.text(&function.name, &mut self.name)?;
        self.emit(function.id.index(), work)
    }
    fn reaches_handle<O: ExecutionObserver>(
        &self,
        signature: &FuncTy,
        nominal: &ObservedNominalTypeReachability<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(2, 2 * size_of::<&[Ty]>())?;
        // Preserve params.chain(returns).any short-circuit order, including
        // unread later slots once an actual query returns true.
        for rows in [&signature.params[..], &signature.returns[..]] {
            let mut at = 0usize;
            while let Some(ty) = work.at(rows, at)? {
                if nominal.contains_handle_observed(ty, work.session, work.site)? {
                    return Ok(true);
                }
                work.next(&mut at)?;
            }
        }
        Ok(false)
    }
    fn emit<O: ExecutionObserver>(&mut self, function: u32, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(
            1,
            size_of::<ValidationError>() + 3 * size_of::<String>() + size_of::<u32>(),
        )?;
        self.errors.push(ValidationError::HandleForeignDeclaration {
            function,
            name: take(&mut self.name),
            handle: take(&mut self.handles),
            detail: take(&mut self.detail),
        });
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.name));
        work.flat(take(&mut self.handles));
        work.flat(take(&mut self.detail));
    }
}
