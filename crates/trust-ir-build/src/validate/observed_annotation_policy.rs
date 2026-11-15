// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual function memory-role and havoc-placement diagnostic constituents.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod havoc;
mod memory;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct Checking {
    errors: Vec<ValidationError>,
    pending: Option<ValidationError>,
    text: String,
    name: String,
    roles: Vec<String>,
}
enum Component {
    MemoryRoles,
    Havoc,
}
/// Exact ordered memory-role conflicts only. No address-space, whole validator
/// or source/proof capability is conferred by a component diagnostic Vec.
pub fn validate_function_memory_roles_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    component(function, Component::MemoryRoles, session, site)
}
/// Exact original havoc-marker placement errors, without interpreting a marker
/// as authority. Successful output/input disposal remains caller-owned.
pub fn validate_function_havoc_placement_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    component(function, Component::Havoc, session, site)
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
    let mut state = Checking::default();
    let mut work = Work { session, site };
    let result = match component {
        Component::MemoryRoles => state.memory(function, &mut work),
        Component::Havoc => state.havoc(function, &mut work),
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
}
