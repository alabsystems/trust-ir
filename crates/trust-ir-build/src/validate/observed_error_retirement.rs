// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Consuming diagnostic cleanup under the original caller's observer.
use super::{PointerConstantRefusal, ValidationError};
use core::mem::size_of;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod errors;
mod nested;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R = Result<(), ObservedValueError>;

/// Consume every diagnostic and actual owned payload, even if this session
/// was already stopped or refuses during cleanup. No scratch allocation or
/// normal admission can return early while any input remains owned here.
/// The original first cause remains sticky; terminal publication then fails.
/// This cleanup receipt grants no validation/source/proof authority or
/// allocator/deallocator latency, RSS/OOM, panic/unwind or hard-time bound.
pub fn retire_validation_errors_observed<O: ExecutionObserver>(
    mut errors: Vec<ValidationError>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    session.retirement_step(site, 1);
    let mut work = Work { session, site };
    loop {
        work.step(size_of::<ValidationError>().saturating_add(1));
        let Some(error) = errors.pop() else { break };
        work.error(error);
    }
    // All elements have been consumed explicitly. Only an empty buffer remains.
    work.step(size_of::<Vec<ValidationError>>().saturating_add(1));
    drop(errors);
    work.poll();
    work.finish()
}

/// Consume one diagnostic without constructing a temporary Vec. Exactly the
/// same exhaustive payload path and original-session stop rules apply.
pub fn retire_validation_error_observed<O: ExecutionObserver>(
    error: ValidationError,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    session.retirement_step(site, 1);
    let mut work = Work { session, site };
    work.error(error);
    work.finish()
}
