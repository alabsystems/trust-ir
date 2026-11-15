// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual ordinary invoke/landing-pad/resume structural validation.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod edges;
mod pads;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct Checking<'a> {
    errors: Vec<ValidationError>,
    pending: Option<ValidationError>,
    text: String,
    leading: Vec<(u32, bool)>,
    unwind: Vec<u32>,
    normal: Vec<(u32, u32)>,
    results: Vec<(ValueId, usize)>,
    literals: Vec<ValueId>,
    edges: Vec<trust_ir::Edge<'a>>,
    has_pad: bool,
}
/// Exact function-local unwind diagnostics only, with actual original-session
/// edge/index/text traversal and owned scratch/error retirement. No complete
/// validator, source/proof authority or resumed admission is established.
/// Successful diagnostics/input disposal and physical allocator/panic/time
/// bounds remain caller duties.
pub fn validate_function_unwind_structure_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<Checking<'_>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = Checking::default();
    let mut work = Work { session, site };
    let result = state
        .leading(function, &mut work)
        .and_then(|()| state.edges(function, &mut work))
        .and_then(|()| state.pads(function, &mut work))
        .and_then(|()| state.resumes(function, &mut work));
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
impl Checking<'_> {
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
        block: u32,
        target: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<ValidationError>())?;
        self.pending = Some(ValidationError::UnwindDestWithoutLandingPad { block, target });
        self.commit(work)
    }
    fn reason<O: ExecutionObserver>(&mut self, block: u32, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<ValidationError>())?;
        self.pending = Some(ValidationError::MisplacedLandingPad {
            block,
            reason: take(&mut self.text),
        });
        self.commit(work)
    }
}
