// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Concrete last-definition type rows, with no opaque lookup callback.
use super::*;
use core::mem::{replace, size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod catalog_values;
mod closure_results;
mod plan;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
pub(super) use catalog_values::build_catalog_value_types_observed;
pub(super) use closure_results::module_closure_results_observed;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

/// Plain inferred types, not a validation result or proof/source authority.
/// Unique keys retain the last physical declaration just like the original
/// map. Linear lookup is observed; callers must retire successful owned rows.
#[derive(Default)]
pub struct ObservedValueTypes {
    rows: Vec<(u32, Ty)>,
}

#[derive(Default)]
struct State {
    output: ObservedValueTypes,
    pending: Option<Ty>,
    borrows: Vec<(ValueId, Ty)>,
}

#[derive(Clone, Copy)]
enum Context<'a> {
    Function,
    Module(&'a Module),
    Catalog(&'a ModuleFunctionCatalog<'a>),
}

/// Preserve the standalone map's partial result inference and second-phase
/// borrow-chain correction under the caller's original session and site.
pub fn build_function_value_types_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ObservedValueTypes> {
    build(function, Context::Function, session, site)
}

/// Resolve module call/signature, multi-result, dialect and landing-pad types
/// before the same original second-phase borrow correction. No opaque ordinary
/// result_tys, derived Clone or tree lookup runs inside the observed traversal.
pub fn build_module_value_types_observed<O: ExecutionObserver>(
    function: &Function,
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ObservedValueTypes> {
    build(function, Context::Module(module), session, site)
}

fn build<O: ExecutionObserver>(
    function: &Function,
    context: Context<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ObservedValueTypes> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.walk(function, context, &mut work);
    state.retire_scratch(&mut work);
    let result = result.and_then(|()| work.publication(size_of::<ObservedValueTypes>()));
    match result {
        Ok(()) => Ok(take(&mut state.output)),
        Err(error) => {
            state.output.retire(&mut work);
            Err(work.terminal(error))
        }
    }
}

impl ObservedValueTypes {
    pub fn get_observed<O: ExecutionObserver>(
        &self,
        value: ValueId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<&Ty>> {
        let mut work = Work { session, site };
        let index = work.find(&self.rows, value.index())?;
        work.publication(size_of::<Option<&Ty>>())?;
        Ok(index.map(|index| &self.rows[index].1))
    }

    /// Drain every owned nested type and buffer before the final stop check.
    /// Logical retirement cannot bound allocator/deallocator or unwind latency.
    pub fn retire_observed<O: ExecutionObserver>(
        mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        self.retire(&mut work);
        work.publication(0)
    }

    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.rows.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some((_, ty)) = self.rows.pop() {
                let _ = ty.retire_observed(work.session, work.site);
            }
        }
        work.retire(take(&mut self.rows));
    }
}

impl State {
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_type(self.pending.take());
        while !self.borrows.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some((_, ty)) = self.borrows.pop() {
                work.retire_type(Some(ty));
            }
        }
        work.retire(take(&mut self.borrows));
    }

    fn commit<O: ExecutionObserver>(&mut self, value: u32, work: &mut Work<'_, '_, O>) -> R {
        let index = work.find(&self.output.rows, value)?;
        if index.is_none() {
            work.reserve(&mut self.output.rows)?;
        }
        work.admit(1, size_of::<(u32, Ty)>())?;
        let Some(ty) = self.pending.take() else {
            return Err(ObservedValueError::InvalidRange);
        };
        if let Some(index) = index {
            // Retain the displaced owned tree immediately before cleanup.
            self.pending = Some(replace(&mut self.output.rows[index].1, ty));
            work.retire_type(self.pending.take());
            work.admit(1, 0)?;
        } else {
            self.output.rows.push((value, ty));
        }
        Ok(())
    }
}
