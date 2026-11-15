// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Shared generation-sensitive frame validation, with actual inner admission.
use super::observed_value_query::function_value_type_observed;
use super::*;
use core::mem::{size_of, take};
use trust_ir::Edge;
use trust_ir::inst::BindingSlot;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod collect;
mod flow;
mod storage;
#[cfg(test)]
mod tests;
mod uses;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

/// The ordinary entry point shares the same analysis and diagnostics. It has
/// no caller budget; internal inability to complete is still a refusal.
pub(super) fn ordinary(function: &Function) -> Vec<ValidationError> {
    struct Unbounded;
    impl ExecutionObserver for Unbounded {
        type Refusal = core::convert::Infallible;
        fn admit(&mut self, _: ExecutionProgress) -> Result<(), Self::Refusal> {
            Ok(())
        }
    }
    let mut observer = Unbounded;
    let mut session = ObservedSession::new(
        trust_ir::interpret::InterpretOptions::default(),
        &mut observer,
    );
    ordinary_result(validate_function_binding_frames_observed(
        function,
        &mut session,
        ExecutionSite::Entry(function.id),
    ))
}

fn ordinary_result(result: R<Vec<ValidationError>>) -> Vec<ValidationError> {
    match result {
        Ok(errors) => errors,
        Err(error) => vec![ValidationError::BindingFrameAnalysisFailed {
            reason: error.to_string(),
        }],
    }
}

#[derive(Default)]
struct State<'a> {
    declarations: Vec<(u32, &'a [BindingSlot])>,
    opens: Vec<(u32, u32)>,
    closes: Vec<(u32, u32)>,
    flow: flow::Flow<'a>,
    actual_type: Option<Ty>,
    expected: String,
    actual: String,
    errors: Vec<ValidationError>,
}

/// Frame-generation may-alias and provenance joins across the complete CFG.
/// A possible closed or non-frame input is refused; origin alternatives are
/// all type-checked. This is conservative at correlated joins and does not
/// establish CFG-wide LIFO or closure on every exit. Same session/site throughout scans,
/// type queries, equality, spelling and cleanup; no partial accepting output.
/// Successful diagnostics/input disposal and physical allocator/time bounds
/// remain caller responsibilities. No source/proof authority is established.
pub fn validate_function_binding_frames_observed<O: ExecutionObserver>(
    function: &Function,
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
    let result = state
        .collect(function, &mut work)
        .and_then(|()| state.propagate(function, &mut work))
        .and_then(|()| state.count_opens(function, &mut work))
        .and_then(|()| state.uses(function, &mut work))
        .and_then(|()| state.unclosed(function, &mut work));
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

impl State<'_> {
    fn fixed<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> ValidationError,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Private call sites capture only fixed Copy IDs/counts. Complete
        // admission precedes the actual enum construction and nonallocating push.
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(make());
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_type(&mut self.actual_type);
        work.drain(&mut self.declarations);
        work.drain(&mut self.opens);
        work.drain(&mut self.closes);
        self.flow.retire(work);
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
    }
    fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(error) = self.errors.pop() {
                match error {
                    ValidationError::BindingSlotTypeMismatch {
                        expected, actual, ..
                    }
                    | ValidationError::BindingBindTypeMismatch {
                        expected, actual, ..
                    } => {
                        work.flat(expected);
                        work.flat(actual);
                    }
                    // All other variants made by this private module own only IDs.
                    fixed => work.flat(fixed),
                }
            }
        }
        work.flat(take(&mut self.errors));
    }
}
