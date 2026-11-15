// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact original tuple/closure layout table diagnostic prelude.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::{LayoutError, LayoutTable};
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'m> {
    table: Option<LayoutTable<'m>>,
    pending: Option<LayoutError>,
    spelled: String,
    reason: String,
    errors: Vec<ValidationError>,
}
/// Exact original tuple-layout diagnostic followed by independent closure-layout
/// diagnostic, using actual observed validation and exact observed LayoutError
/// spelling. The original closure reason prefix remains unchanged. Preserve
/// semantic errors as diagnostics; operational refusal yields no smaller list.
///
/// The table is freshly constructed here, never escapes this private state and
/// is passed ONLY to these two exact observed methods, which do not populate its
/// ordinary memo. Its fixed empty-memo release below is specific to this path;
/// this is NOT general retirement of a caller-supplied/populated LayoutTable.
/// Query work/state is actually observed and retired by each original method;
/// repeated analyses are charged, without an ordinary memo-sharing claim.
///
/// Same supplied original session/site, no authority/flags/owner callbacks or
/// accepting fallback. Successful diagnostics and input remain caller-owned;
/// scalar std initialization/allocator/deallocator/OOM/panic/RSS/hard-time limits
/// remain OPEN. No module/layout/ABI/source/proof capability follows.
pub fn validate_module_layout_prelude_observed<O: ExecutionObserver>(
    module: &Module,
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
    let result = state.run(module, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State<'_> {
    fn retire_error<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.session.retirement_step(
            work.site,
            size_of::<Option<LayoutError>>().saturating_add(1),
        );
        if let Some(error) = self.pending.take() {
            let _ = error.retire_observed(work.session, work.site);
        }
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_error(work);
        work.retire_text(&mut self.spelled);
        work.retire_text(&mut self.reason);
        // Actual constructor + observed-only use above prove this memo empty.
        // No external table or callback can enter this private owning state.
        work.session.retirement_step(
            work.site,
            size_of::<Option<LayoutTable<'_>>>().saturating_add(1),
        );
        drop(self.table.take());
        work.session.retirement_poll(work.site);
    }
}
