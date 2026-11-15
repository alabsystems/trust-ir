// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original target presence/scalar checks and actual first-FFI-boundary walk.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod boundary;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    boundary: String,
    errors: Vec<ValidationError>,
}
/// Exact original target-info checks. Present targets are checked for their
/// original pointer-size/empty-triple rules only. Missing targets require the
/// first original duplicate-aware FFI boundary, with unchanged complete text.
/// This is a diagnostic constituent, not target/layout/ABI or proof authority.
/// Actual nested declaration/instruction/lookup/text work uses the supplied
/// original session/site; no opaque catalog construction or boundary helper is
/// called. Linear lookup preserves Missing/Ambiguous refusal and charges all
/// actual repeated visits, without claiming indexed complexity.
///
/// Partial boundary and completed diagnostics remain owned through all later
/// fallible work and are consumed after sticky refusal. No smaller list/new
/// owner/grant/deadline/TLS/fuel/flag/accepting fallback. Successful output/input
/// disposal and physical std/allocator/deallocator/OOM/panic/unwind/RSS/hard100ms
/// remain OPEN, as do full module/source/HIR/proof/native orchestration and MC.
pub fn validate_module_target_info_observed<O: ExecutionObserver>(
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
    work.retire_text(&mut state.boundary);
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
    fn run<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<Option<&trust_ir::TargetInfo>>())?;
        if let Some(target) = &module.target_info {
            work.admit(1, size_of::<u32>())?;
            if !matches!(target.pointer_size, 1 | 2 | 4 | 8) {
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>())?;
                self.errors.push(ValidationError::TargetPointerSizeInvalid {
                    pointer_size: target.pointer_size,
                });
            }
            work.admit(1, size_of::<usize>())?;
            if target.triple.is_empty() {
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>())?;
                self.errors.push(ValidationError::TargetTripleEmpty);
            }
        } else if boundary::first(module, work, &mut self.boundary)? {
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::TargetInfoRequired {
                boundary: take(&mut self.boundary),
            });
        }
        Ok(())
    }
}
