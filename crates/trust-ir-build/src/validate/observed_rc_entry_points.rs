// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete always-on pinned RC namespace and effect-claim rule.
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
/// This rule is ALWAYS on, even in scalar-only modules. Only the actual static
/// TRUSTED_RC_RUNTIMES supplies pins; no candidate registry/callback is accepted.
/// Its exact borrowed scalar slices stand for RcEntryPoint::func_ty's params,
/// returns, vararg=false and ABI=None; no redundant owned signature is needed.
/// Actual equality, effects, diagnostics and all constant descendants preserve
/// original order and short circuits under the supplied original session/site.
/// Full returned display children/partial fields/prior rows stay owned through
/// every failure and retire before refusal or complete publication. No shorter
/// answer, new grant/deadline/TLS/fuel or runtime/module/proof authority results.
/// Full caller adoption, original successful input/output disposal and physical
/// std/allocator/panic/RSS/hard bounds remain separate obligations.
pub(super) fn validate_rc_entry_points_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
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
fn lookup<O: ExecutionObserver>(
    symbol: &str,
    work: &mut Work<'_, '_, O>,
) -> R<Option<(&'static RcRuntimePin, &'static RcEntryPoint)>> {
    let mut p = 0;
    while let Some(pin) = work.at(TRUSTED_RC_RUNTIMES, p)? {
        let mut e = 0;
        while let Some(entry) = work.at(pin.entry_points, e)? {
            if work.equal(entry.symbol, symbol)? {
                return Ok(Some((pin, entry)));
            }
            work.next(&mut e)?;
        }
        work.next(&mut p)?;
    }
    Ok(None)
}
impl<'m> State<'m> {
    fn run<O: ExecutionObserver>(&mut self, module: &'m Module, work: &mut Work<'_, '_, O>) -> R {
        let mut at = 0;
        while let Some(function) = work.at(&module.functions, at)? {
            self.function(module, function, work)?;
            work.next(&mut at)?;
        }
        let mut at = 0;
        while let Some(global) = work.at(&module.globals, at)? {
            if lookup(&global.name, work)?.is_some() {
                work.text(&global.name, &mut self.other)?;
                work.text(&global.name, &mut self.symbol)?;
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
                self.errors
                    .push(ValidationError::RcEntryPointShadowedByGlobal {
                        global: take(&mut self.other),
                        symbol: take(&mut self.symbol),
                    });
            }
            work.next(&mut at)?;
        }
        self.constants(module, work)
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
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
