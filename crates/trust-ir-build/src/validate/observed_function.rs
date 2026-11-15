// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual structural/debug and scalar function-metadata constituents.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod debug;
mod metadata;
mod storage;
mod structure;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct Checking {
    errors: Vec<ValidationError>,
    pending: Option<ValidationError>,
    text: String,
    definitions: Vec<u32>,
    names: Vec<u32>,
    blocks: Vec<u32>,
}
enum Component {
    Structure,
    BodyGate,
    Symbols,
}

/// Exact ordinary structural diagnostics, including the full debug-metadata
/// prefix, with actual traversal/storage/copy under the original session/site.
/// Empty output is ONLY this constituent, never complete module validation or
/// a ModuleValidationReport/source/proof capability. Successful output disposal
/// remains the caller's duty. Physical allocator/panic/clock bounds are separate.
pub fn validate_function_structure_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    component(function, Component::Structure, session, site)
}
/// Exact body-gate/display-path spelling errors only; this grants no gate license.
pub fn validate_function_body_gate_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    component(function, Component::BodyGate, session, site)
}
/// Exact function section and visibility/linkage diagnostics only.
pub fn validate_function_symbol_attributes_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    component(function, Component::Symbols, session, site)
}
fn component<O: ExecutionObserver>(
    function: &Function,
    component: Component,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<Checking>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut work = Work { session, site };
    let mut state = Checking::default();
    let result = match component {
        Component::Structure => state
            .debug(function, &mut work)
            .and_then(|()| state.structure(function, &mut work)),
        Component::BodyGate => state.body_gate(function, &mut work),
        Component::Symbols => state.symbols(function, &mut work),
    };
    state.retire_scratch(&mut work);
    let result = result.and_then(|()| work.publication());
    match result {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            state.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}
impl Checking {
    fn commit<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        if let Some(error) = self.pending.take() {
            self.errors.push(error);
        }
        Ok(())
    }
    fn fixed<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> ValidationError,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Private callers capture only Copy fields, never an owned payload.
        work.admit(1, size_of::<ValidationError>())?;
        self.pending = Some(make());
        self.commit(work)
    }
    fn detail<O: ExecutionObserver>(
        &mut self,
        text: &str,
        make: impl FnOnce(String) -> ValidationError,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(text, &mut self.text)?;
        self.built_detail(make, work)
    }
    fn built_detail<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce(String) -> ValidationError,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<ValidationError>())?;
        self.pending = Some(make(take(&mut self.text)));
        self.commit(work)
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        if let Some(error) = self.pending.take() {
            retire_error(error, work);
        }
        work.retire(take(&mut self.text));
        work.retire(take(&mut self.definitions));
        work.retire(take(&mut self.names));
        work.retire(take(&mut self.blocks));
    }
    fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(error) = self.errors.pop() {
                retire_error(error, work);
            }
        }
        work.retire(take(&mut self.errors));
    }
}
fn retire_error<O: ExecutionObserver>(error: ValidationError, work: &mut Work<'_, '_, O>) {
    work.session.retirement_step(work.site, 1);
    match error {
        ValidationError::InvalidValueName { detail, .. }
        | ValidationError::InvalidScopeTree { detail, .. }
        | ValidationError::InvalidInlinedScope { detail, .. }
        | ValidationError::InvalidBodyGate { detail, .. }
        | ValidationError::InvalidDisplayPath { detail, .. }
        | ValidationError::InvalidFunctionSection { detail, .. } => work.retire(detail),
        ValidationError::MidBlockTerminator { op, .. } => work.retire(op),
        // The only other errors made by this private constituent have fixed
        // scalar/enum fields. This is NOT arbitrary ValidationError retirement.
        fixed => work.retire(fixed),
    }
    work.session.retirement_poll(work.site);
}
