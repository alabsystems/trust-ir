// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original function type pass with actual observed constituents.
use super::*;
use core::mem::{size_of, take};
use trust_ir::Block;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod dispatch;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    values: Option<ObservedValueTypes>,
    constants: Vec<(u32, i128)>,
    pending: Vec<ValidationError>,
    errors: Vec<ValidationError>,
}
#[derive(Clone, Copy)]
enum Route {
    Numeric,
    Basic,
    Cast,
    PointerSelect,
    Element,
    /// An original rule with no observed constituent yet: the pass stops
    /// (`UnsupportedValue`) rather than publish a list that omits it.
    Unsupported,
    None,
}

/// Complete original function type pass, including full inferred values,
/// both vector passes, last qualifying integer constants, all original operand
/// families and the original borrow/Rust-reference diagnostic tail. Actual
/// traversal, comparisons, construction, helpers and cleanup share exactly the
/// supplied original session/site. No partial list escapes operational refusal.
///
/// None selects original standalone FunctionOnly cast policy/default width;
/// Some(module) selects original module DeferLayoutSensitive policy and actual
/// target width. The module's separate layout/refinement and every other
/// function/module/source/proof pass remain mandatory caller obligations.
/// This diagnostic list alone confers no validation or source authority.
/// Successful output/input disposal remains the caller's responsibility.
pub fn validate_function_types_observed<O: ExecutionObserver>(
    function: &Function,
    module: Option<&Module>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 4,
        copy_bytes: size_of::<State>()
            + size_of::<Work<'_, '_, O>>()
            + size_of::<ValidationContext<'_>>(),
    })?;
    // Module::pointer_bits reads one optional fixed target field and performs
    // one checked multiply; it neither scans a triple nor allocates.
    let context = ValidationContext {
        cast_mode: if module.is_some() {
            CastValidationMode::DeferLayoutSensitive
        } else {
            CastValidationMode::FunctionOnly
        },
        pointer_bits: module.map_or(DEFAULT_POINTER_BITS, Module::pointer_bits),
        module,
    };
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.run(function, context, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            state.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}
impl State {
    fn run<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        context: ValidationContext<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<ObservedValueTypes>>())?;
        self.values = Some(match context.module {
            None => build_function_value_types_observed(function, work.session, work.site)?,
            Some(module) => {
                build_module_value_types_observed(function, module, work.session, work.site)?
            }
        });
        self.first_pass(function, work)?;
        self.second_pass(function, context, work)?;
        self.prepare(work)?;
        self.pending = validate_function_borrow_structure_observed(
            function,
            self.values
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?,
            work.session,
            work.site,
        )?;
        self.append(work)?;
        self.prepare(work)?;
        self.pending =
            validate_function_rust_reference_spelling_observed(function, work.session, work.site)?;
        self.append(work)
    }
    fn prepare<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, 0)?;
        if self.pending.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn append<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        let start = self.errors.len();
        // Every successful helper Vec is already retained in pending. Reserve
        // BEFORE moving each row; no locally owned row spans a fallible step.
        loop {
            work.admit(1, 0)?;
            if self.pending.is_empty() {
                break;
            }
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            let error = self.pending.pop().ok_or(ObservedValueError::InvalidRange)?;
            self.errors.push(error);
        }
        // Pop reversed the helper's rows; reverse ONLY this appended suffix.
        // All rows remain retained on any refused swap, so cleanup can consume
        // them completely without ever publishing an out-of-order partial list.
        let mut left = start;
        let mut end = self.errors.len();
        while left < end {
            work.admit(1, 2 * size_of::<ValidationError>())?;
            end = end.checked_sub(1).ok_or(ObservedValueError::InvalidRange)?;
            if left >= end {
                break;
            }
            self.errors.swap(left, end);
            left = left
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        work.flat(take(&mut self.pending));
        work.admit(1, 0)
    }
    fn vector<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        block: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.prepare(work)?;
        self.pending = validate_vector_type_observed(ty, block, work.session, work.site)?;
        self.append(work)
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        let _ = retire_validation_errors_observed(take(&mut self.pending), work.session, work.site);
        work.session.retirement_step(work.site, 1);
        if let Some(values) = self.values.take() {
            let _ = values.retire_observed(work.session, work.site);
        }
        loop {
            work.session.retirement_step(work.site, 1);
            if self.constants.pop().is_none() {
                break;
            }
        }
        work.flat(take(&mut self.constants));
    }
    fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        let _ = retire_validation_errors_observed(take(&mut self.errors), work.session, work.site);
    }
}
