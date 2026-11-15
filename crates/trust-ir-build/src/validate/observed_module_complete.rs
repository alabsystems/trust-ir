// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Strict completeness-claim labels and diagnostic custody, never truth/proof.
use super::{CompletenessError, Module};
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::{ModuleCompleteness, UnloweredRow};
mod clone_rows;
mod display;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

struct State {
    symbol: String,
    path: Option<String>,
    reason: String,
    rows: Vec<UnloweredRow>,
    outcome: Result<(), CompletenessError>,
}
impl Default for State {
    fn default() -> Self {
        Self {
            symbol: String::new(),
            path: None,
            reason: String::new(),
            rows: Vec::new(),
            outcome: Ok(()),
        }
    }
}

/// Exact strict claim check: None is unclaimed, Partial returns every copied
/// physical row, and only Some(Complete) returns the original Ok label. This
/// neither runs module validation nor proves that a Complete claim is true.
/// Original input is borrowed; success result disposal remains caller owned.
/// Every stop consumes pending fields, finished rows and any owned outcome in
/// this same session/site, without publishing a smaller error. No new owner,
/// grant, deadline, TLS, fuel or policy is introduced. Logical accounting does
/// not establish allocator/deallocator/OOM/panic/unwind/RSS/hard-time bounds.
pub fn validate_module_complete_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Result<(), CompletenessError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.walk(module, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication(1, size_of::<Result<(), CompletenessError>>())) {
        Ok(()) => Ok(core::mem::replace(&mut state.outcome, Ok(()))),
        Err(error) => {
            retirement::outcome(core::mem::replace(&mut state.outcome, Ok(())), &mut work);
            Err(work.terminal(error))
        }
    }
}

impl CompletenessError {
    /// Existing Display spelling with actual observed row/text traversal.
    /// Returned String and borrowed input disposal remain caller owned. Fixed
    /// scalar std escaping is a primitive boundary, not physical time proof.
    pub fn display_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<String> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<String>())?;
        let mut output = String::new();
        match display::write(self, &mut work, &mut output)
            .and_then(|()| work.publication(1, size_of::<String>()))
        {
            Ok(()) => Ok(output),
            Err(error) => {
                work.retire_text(output);
                Err(work.terminal(error))
            }
        }
    }

    /// Fully consume all owned rows/fields even after an original sticky stop;
    /// terminal publication then refuses without replacing that first cause.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        retirement::error(self, &mut work);
        work.publication(0, 0)
    }
}

impl State {
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_text(take(&mut self.symbol));
        retirement::path(self.path.take(), work);
        work.retire_text(take(&mut self.reason));
        retirement::rows(take(&mut self.rows), work);
    }
}
