// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Entire always-on handle symbol namespace rule, under the original owner.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod constants;
mod functions;
mod render;
mod signature;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'m> {
    expected: Option<ObservedPinnedFuncTy>,
    expected_text: String,
    actual: String,
    piece: String,
    render: String,
    symbol: String,
    other: String,
    location: String,
    mismatches: usize,
    stack: Vec<&'m Constant>,
    errors: Vec<ValidationError>,
}
/// Preserve every original function/global/constant namespace check in source
/// order, whether a module's census contains handles or not. The expected
/// signature is closed owned DATA, not authority. Every actual lookup, scalar
/// type clone, type equality/display, diagnostic and constant child cursor
/// shares the supplied original session/site. No ABI payload is compared when
/// the closed expected signature has ABI=None, exactly as derived equality.
///
/// Complete child results immediately enter State, remain held across every
/// later failure, and are exhaustively retired before refusal/publication.
/// No partial diagnostics or shorter successful result is returned on stop.
/// Registry admission/full module authority, physical hard bounds and original
/// successful input/result disposal remain the enclosing caller's obligations.
pub(super) fn validate_handle_entry_points_observed<O: ExecutionObserver>(
    module: &Module,
    registry: &HandleRegistry,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, registry, &mut work);
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
impl<'m> State<'m> {
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        registry: &HandleRegistry,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0usize;
        while let Some(function) = work.at(&module.functions, at)? {
            self.function(module, function, registry, work)?;
            work.next(&mut at)?;
        }
        let mut at = 0usize;
        while let Some(global) = work.at(&module.globals, at)? {
            if registry
                .entry_for_symbol_observed(&global.name, work.session, work.site)?
                .is_some()
            {
                work.text(&global.name, &mut self.other)?;
                work.text(&global.name, &mut self.symbol)?;
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
                self.errors
                    .push(ValidationError::HandleEntryPointShadowedByGlobal {
                        global: take(&mut self.other),
                        symbol: take(&mut self.symbol),
                    });
            }
            work.next(&mut at)?;
        }
        self.constants(module, registry, work)
    }
    fn retire_expected<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<ObservedPinnedFuncTy>>());
        if let Some(expected) = self.expected.take() {
            let _ = expected.retire_observed(work.session, work.site);
        }
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_expected(work);
        work.rows(&mut self.stack);
        work.flat(take(&mut self.expected_text));
        work.flat(take(&mut self.actual));
        work.flat(take(&mut self.piece));
        work.flat(take(&mut self.render));
        work.flat(take(&mut self.symbol));
        work.flat(take(&mut self.other));
        work.flat(take(&mut self.location));
    }
}
