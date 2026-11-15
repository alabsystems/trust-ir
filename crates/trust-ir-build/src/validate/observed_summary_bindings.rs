// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original summary clause/binding rules, not proof authentication.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort, ProofFormula};
use trust_ir::{FuncTy, FunctionSummary};
mod places;
mod storage;
#[cfg(test)]
mod tests;
mod typing;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    detail: String,
    render: Option<String>,
    values: Option<ObservedValueTypes>,
    errors: Vec<ValidationError>,
}
/// Exact first clause/binding loop of validate_function_summary, including
/// schema/name/role/place resolution and faithful type-sort checks. Does not
/// check param-name/effect shape, backing, parsing or proof authority. No
/// ordinary type-map/clone/formatter is called inside observed work.
pub fn validate_function_summary_bindings_observed<O: ExecutionObserver>(
    module: &Module,
    function: &Function,
    summary: &FunctionSummary,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.walk(module, function, summary, &mut work);
    state.finish(result, &mut work)
}
impl State {
    fn issue<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::InvalidFunctionSummary {
            function: function.id.index(),
            detail: take(&mut self.detail),
        });
        Ok(())
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        work.retire_text(take(&mut self.detail));
        work.step(size_of::<Option<String>>().saturating_add(1));
        if let Some(text) = self.render.take() {
            work.retire_text(text);
        }
        work.step(size_of::<Option<ObservedValueTypes>>().saturating_add(1));
        if let Some(values) = self.values.take() {
            let _ = values.retire_observed(work.session, work.site);
        }
        match result.and_then(|()| work.publication(1, size_of::<Vec<ValidationError>>())) {
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
fn clause_prefix<O: ExecutionObserver>(
    role: ContractClauseRole,
    index: usize,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(1, size_of::<ContractClauseRole>())?;
    work.text(role.name(), out)?;
    work.text(" clause ", out)?;
    work.number(index as u128, out)
}
fn binding_prefix<O: ExecutionObserver>(
    role: ContractClauseRole,
    index: usize,
    name: &str,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    clause_prefix(role, index, out, work)?;
    work.text(" binding '", out)?;
    work.text(name, out)?;
    work.text("'", out)
}
fn place_text<O: ExecutionObserver>(
    place: ClausePlace,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(11, size_of::<ClausePlace>())?;
    let (label, index) = match place {
        ClausePlace::Param { index } => ("Param ", Some(index)),
        ClausePlace::ResultSlot { index } => ("ResultSlot ", Some(index)),
        ClausePlace::MutParamExit { index } => ("MutParamExit ", Some(index)),
        ClausePlace::World => ("World", None),
        ClausePlace::WorldPre => ("WorldPre", None),
        ClausePlace::WorldPost => ("WorldPost", None),
        ClausePlace::Unwind => ("Unwind", None),
        ClausePlace::Value(id) => ("SSA value v", Some(id.index())),
        ClausePlace::SpecVar { index } => ("SpecVar ", Some(index)),
        ClausePlace::SpecVarNext { index } => ("SpecVarNext ", Some(index)),
        ClausePlace::ParamPointeeEntry { index } => ("ParamPointeeEntry ", Some(index)),
    };
    work.text(label, out)?;
    if let Some(index) = index {
        work.number(index as u128, out)?;
    }
    Ok(())
}
