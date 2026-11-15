// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original AlwaysMemory aggregate-slot diagnostic rule.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    slot: String,
    tytext: Option<String>,
    errors: Vec<ValidationError>,
}
/// Whole original FuncTy table, parameters then returns, only when the actual
/// pinned target policy is AlwaysMemory. Single-refinement aggregate-slot
/// classification and full type Display use actual observed APIs, not opaque
/// callbacks. This is a diagnostic rule, not an ABI/module/producer authority.
pub fn validate_module_always_memory_struct_passing_observed<O: ExecutionObserver>(
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
    let result = state.run(module, &mut work);
    state.finish(result, &mut work)
}
impl State {
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_text(&mut self.slot);
        work.step(size_of::<Option<String>>().saturating_add(1));
        if let Some(mut text) = self.tytext.take() {
            work.retire_text(&mut text);
        }
        work.poll();
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(work);
        match result.and_then(|()| work.publication()) {
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
// Original session/site; no new grant/deadline/TLS/fuel/flag/fallback. Full ABI/
// module/source/proof/native/MC orchestration, caller/input disposal and physical
// std/allocator/deallocator/OOM/panic/unwind/RSS/hard100ms remain OPEN.
