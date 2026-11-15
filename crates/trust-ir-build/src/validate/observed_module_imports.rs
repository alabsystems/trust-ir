// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original whole-row import interning and digest/name coherence.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::{ModuleImport, Producer};
mod equality;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    first: String,
    second: String,
    errors: Vec<ValidationError>,
}
/// Exact original import-table interning errors followed by artifact digest/name
/// coherence errors. Whole ModuleImport identity includes its name, full digest,
/// recorded/unrecorded producer (including full Other text) and identity scheme.
/// Complete struct/enum destructuring forces future fields/variants to be
/// classified; no hand-listed partial key silently admits a distinct row.
///
/// Actual borrowed linear searches replace discarded hash indexes. Preserve
/// first-equivalent row and original saturated diagnostic IDs, without claiming
/// the original hash complexity. Every comparison/copy/growth and refused-output
/// cleanup uses this original session/site. No partial result escapes a stop.
/// This is not dependency authentication, import/source/proof authority or full
/// module validity. Successful output/input disposal and physical allocator/
/// deallocator/stdlib/OOM/panic/RSS/hard-time containment remain caller duties.
pub fn validate_module_imports_observed<O: ExecutionObserver>(
    module: &Module,
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
    let result = state
        .interning(module, &mut work)
        .and_then(|()| state.identity(module, &mut work));
    state.retire_text(&mut work);
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
    fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(2, 0)?;
        if self.first.capacity() != 0 || self.second.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn retire_text<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_text(&mut self.first);
        work.retire_text(&mut self.second);
    }
}
