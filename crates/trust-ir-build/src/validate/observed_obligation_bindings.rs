// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original obligation free names, function places and faithful type-sort rule.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::FuncTy;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofObligation};
use trust_ir::value::ValueId;
mod places;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
mod typing;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    detail: String,
    render: Option<String>,
    values: Option<ObservedValueTypes>,
    errors: Vec<ValidationError>,
}
/// Execute exactly the ordinary non-spec obligation binding rule. Scope is
/// `function`, otherwise `site.function`; a missing/ambiguous scope skips this
/// constituent, as its separate scope rule reports it. No accepting substitute
/// owner/type is constructed. All actual names/definitions/type inference,
/// borrowed place resolution, recursive type-sort tests, formatting and storage
/// use only the supplied original session/site. Diagnostics are not authority.
pub(crate) fn validate_module_obligation_bindings_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, &mut work);
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
    fn run<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        let mut at = 0usize;
        while let Some(obligation) = work.at(&module.proof_obligations, at)? {
            self.row(module, obligation, work)?;
            self.clear_values(work)?;
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn row<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        obligation: &ProofObligation,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<&trust_ir::proof::ProofFormula>>())?;
        let Some(formula) = &obligation.formula else {
            return Ok(());
        };
        work.admit(1, size_of::<usize>())?;
        if formula.bindings.is_empty() {
            return Ok(());
        }
        work.admit(2, size_of::<Option<FuncId>>())?;
        let scope = obligation
            .function
            .or_else(|| obligation.site.map(|site| site.function));
        let owner = match scope {
            None => None,
            Some(id) => match work.resolve(module, id)? {
                Some(function) => Some(function),
                None => return Ok(()),
            },
        };
        let signature = match owner {
            Some(function) => {
                work.admit(1, size_of::<usize>())?;
                let index = usize::try_from(function.ty.index())
                    .map_err(|_| ObservedValueError::CapacityOverflow)?;
                work.at(&module.func_types, index)?
            }
            None => None,
        };
        let mut at = 0usize;
        while let Some((name, binding)) = work.at(&formula.bindings, at)? {
            if work.blank(name)? {
                work.text("binds a blank free name, which can never be the name of a variable in the formula",&mut self.detail)?;
                self.emit(obligation, work)?;
            }
            let mut earlier = 0usize;
            let mut duplicate = false;
            while earlier < at {
                let (prior, _) = work
                    .at(&formula.bindings, earlier)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                if work.equal(prior, name)? {
                    duplicate = true;
                    break;
                }
                work.next(&mut earlier)?;
            }
            if duplicate {
                work.text("binds ", &mut self.detail)?;
                work.quoted(name, &mut self.detail)?;
                work.text(" more than once; `bindings` is a name -> (sort, place) map, so a repeated name leaves the formula's free variable ambiguous",&mut self.detail)?;
                self.emit(obligation, work)?;
            }
            work.admit(12, size_of::<ClausePlace>())?;
            if !matches!(
                binding.place,
                ClausePlace::World | ClausePlace::SpecVar { .. } | ClausePlace::SpecVarNext { .. }
            ) {
                if let Some(function) = owner {
                    self.places(module, function, signature, obligation, name, binding, work)?;
                    self.typing(module, function, obligation, name, binding, work)?;
                } else {
                    self.bind_prefix(name, binding.place, work)?;
                    work.text(", but the obligation has neither a `function` scope nor a `site`, so there is no function to resolve the place in; an unscoped obligation may bind only World",&mut self.detail)?;
                    self.emit(obligation, work)?;
                }
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn emit<O: ExecutionObserver>(
        &mut self,
        obligation: &ProofObligation,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + size_of::<String>())?;
        self.errors.push(ValidationError::InvalidObligationBinding {
            obligation: obligation.id.index(),
            detail: take(&mut self.detail),
        });
        Ok(())
    }
    fn bind_prefix<O: ExecutionObserver>(
        &mut self,
        name: &str,
        place: ClausePlace,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.detail.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text("binds ", &mut self.detail)?;
        work.quoted(name, &mut self.detail)?;
        work.text(" to ", &mut self.detail)?;
        place_text(place, &mut self.detail, work)
    }
    fn clear_values<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.step(size_of::<Option<ObservedValueTypes>>().saturating_add(1));
        if let Some(values) = self.values.take() {
            let _ = values.retire_observed(work.session, work.site);
        }
        work.admit(1, 0)
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.detail));
        work.step(size_of::<Option<String>>().saturating_add(1));
        if let Some(text) = self.render.take() {
            work.flat(text);
        }
        work.step(size_of::<Option<ObservedValueTypes>>().saturating_add(1));
        if let Some(values) = self.values.take() {
            let _ = values.retire_observed(work.session, work.site);
        }
        work.poll();
    }
}
fn place_text<O: ExecutionObserver>(
    place: ClausePlace,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(12, size_of::<ClausePlace>())?;
    let (label, index) = match place {
        ClausePlace::Param { index } => ("Param ", Some(index)),
        ClausePlace::ResultSlot { index } => ("ResultSlot ", Some(index)),
        ClausePlace::MutParamExit { index } => ("MutParamExit ", Some(index)),
        ClausePlace::World => ("World", None),
        ClausePlace::WorldPre => ("WorldPre", None),
        ClausePlace::WorldPost => ("WorldPost", None),
        ClausePlace::Unwind => ("Unwind", None),
        ClausePlace::Value(value) => ("SSA value v", Some(value.index())),
        ClausePlace::SpecVar { index } => ("SpecVar ", Some(index)),
        ClausePlace::SpecVarNext { index } => ("SpecVarNext ", Some(index)),
        ClausePlace::ParamPointeeEntry { index } => ("ParamPointeeEntry ", Some(index)),
    };
    work.text(label, out)?;
    if let Some(index) = index {
        work.number(u128::from(index), out)?;
    }
    Ok(())
}
// No function/module/proof/source/native authority. Successful caller/input
// disposal and physical std/allocator/deallocator/OOM/panic/unwind/RSS/hardtime
// remain OPEN; no original owner, grant, deadline, TLS or fuel reset.
