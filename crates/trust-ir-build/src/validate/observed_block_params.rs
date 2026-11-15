// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Exact block-edge count/type diagnostics under the caller's original scope.
use super::observed_value_types::{
    ObservedValueTypes, build_function_value_types_observed, build_module_value_types_observed,
};
use super::{EdgeKind, Function, Inst, Module, Ty, ValidationError, ValueId};
use core::mem::{size_of, take};
use trust_ir::Edge;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod diagnostics;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Default)]
struct Diagnostics {
    errors: Vec<ValidationError>,
    pending: Option<ValidationError>,
    expected: String,
    actual: String,
}
#[derive(Default)]
struct State<'f> {
    values: Option<ObservedValueTypes>,
    edges: Vec<Edge<'f>>,
    diagnostics: Diagnostics,
}

/// Exact original block-parameter count diagnostics followed by each normal
/// edge's zipped type diagnostics, with Switch defaults first. The supplied
/// optional module is the existing type context, not a new authority flag.
/// Actual value inference, lookups, equality, diagnostic spelling and owned
/// cleanup use the same original session/site. No partial error Vec returns
/// on refusal. This component alone establishes no CFG/SSA/type validity or
/// source/proof authority. Successful output/input and physical allocator/time
/// containment remain caller duties.
pub fn validate_function_block_params_observed<O: ExecutionObserver>(
    function: &Function,
    module: Option<&Module>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.run(function, module, &mut work);
    state.retire_scratch(&mut work);
    let result = result.and_then(|()| work.publication());
    match result {
        Ok(()) => Ok(take(&mut state.diagnostics.errors)),
        Err(error) => {
            state.diagnostics.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}
