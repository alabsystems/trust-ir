// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original function-local exhaustive-switch shape rule, not enum coverage.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod cases;
mod diagnostics;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'f> {
    values: Option<ObservedValueTypes>,
    seen: Vec<(u128, &'f Constant)>,
    first: String,
    second: String,
    ty: String,
    reason: String,
    errors: Vec<ValidationError>,
}
/// Exactly the function-local original default-edge/target/selector-alias rule.
/// Module enum-case coverage is a separate mandatory pass; a clean diagnostic
/// list cannot establish the producer's exhaustiveness hint or source authority.
/// Preserve the original last actual terminator, first duplicate target, lazy
/// standalone value map and first stored constant per masked selector key.
///
/// Every actual scan, full inferred-map construction, width query, constant/type
/// spelling, bounded text copy and storage allocation uses the supplied original
/// session/site. Any operational refusal drains retained state before returning
/// no partial list. Successful output/input disposal remains caller-owned.
pub fn validate_function_exhaustive_switch_shape_observed<O: ExecutionObserver>(
    function: &Function,
    pointer_bits: u32,
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
    let result = state.walk(function, pointer_bits, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            state.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}
impl State<'_> {
    fn retire_text<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.first));
        work.flat(take(&mut self.second));
        work.flat(take(&mut self.ty));
        work.flat(take(&mut self.reason));
    }
    fn retire_seen<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.session.retirement_step(work.site, 1);
            if self.seen.pop().is_none() {
                break;
            }
        }
        work.flat(take(&mut self.seen));
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_text(work);
        self.retire_seen(work);
        work.session.retirement_step(work.site, 1);
        if let Some(values) = self.values.take() {
            let _ = values.retire_observed(work.session, work.site);
        }
    }
    fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        let _ = retire_validation_errors_observed(take(&mut self.errors), work.session, work.site);
    }
}
