// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original function-symbol tripwire and duplicate-row attribution.
use super::{Module, SYNTHETIC_SYMBOL_MARKER, ValidationError, retire_validation_errors_observed};
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::{Function, Producer};
mod clone_fields;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    name: String,
    first_producer: Option<Producer>,
    second_producer: Option<Producer>,
    first_path: Option<String>,
    second_path: Option<String>,
    errors: Vec<ValidationError>,
}
/// Exact original module function-name block: inspect every physical row,
/// report its synthetic marker first, then any same-name collision with the
/// first physical holder. IDs, producers and paths never excuse a collision.
/// Their recorded payloads are copied verbatim, including None/Some-empty.
///
/// Actual fixed-marker substring scans, bounded name equality/copies and
/// owned attribution construction use the same original session/site. A
/// borrowed linear prior-row search replaces the discarded index; worst-case
/// quadratic work is charged without claiming the original tree complexity.
/// Pending fields and completed errors remain owned through every fallible
/// reserve/header/publication step and are fully consumed on refusal.
/// No symbol/source/proof authority, whole module verdict or producer-truth
/// claim follows. Successful input/output disposal and physical allocator/
/// deallocator/RSS/OOM/panic/unwind/observer/hard-time bounds remain open.
pub fn validate_module_function_symbols_observed<O: ExecutionObserver>(
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
    let result = state.walk(module, &mut work);
    state.retire_pending(&mut work);
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
        work.admit(5, 0)?;
        if self.name.capacity() != 0
            || self.first_producer.is_some()
            || self.second_producer.is_some()
            || self.first_path.is_some()
            || self.second_path.is_some()
        {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
}
