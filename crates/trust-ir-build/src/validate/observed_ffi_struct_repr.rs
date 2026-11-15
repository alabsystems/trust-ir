// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original direct-struct FFI repr and Rust variadic-signature constituents.
use super::*;
use core::mem::{size_of, take};
use trust_ir::StructRepr;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod ffi;
mod storage;
#[cfg(test)]
mod tests;
mod vararg;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Default)]
struct State {
    reprs: Vec<(u32, StructRepr)>,
    name: String,
    detail: String,
    errors: Vec<ValidationError>,
}
/// Exact original FFI rule: bodyless external/external_weak, every convention
/// except precisely Rust, and only direct Struct parameters then returns.
/// Same-ID repr rows retain the original last-definition lookup semantics.
/// This diagnostic constituent does not validate an ABI, type or full module.
pub fn validate_module_ffi_struct_repr_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.ffi(module, &mut work);
    state.finish(result, &mut work)
}
/// Exact original Rust+is_vararg signature rule on the supplied function,
/// including definitions and functions not physically present in the module.
/// A missing function-type slot retains the original no-diagnostic behavior.
/// Refusal never publishes a shorter list or creates a new owner or authority.
pub fn validate_function_rust_abi_is_not_variadic_observed<O: ExecutionObserver>(
    module: &Module,
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.vararg(module, function, &mut work);
    state.finish(result, &mut work)
}
fn header<O: ExecutionObserver>(session: &mut ObservedSession<'_, O>, site: ExecutionSite) -> R {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
        })
        .map_err(Into::into)
}
impl State {
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(work);
        match result.and_then(|()| work.publication(1, size_of::<Vec<ValidationError>>())) {
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
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_text(take(&mut self.name));
        work.retire_text(take(&mut self.detail));
        loop {
            work.step(size_of::<Option<(u32, StructRepr)>>().saturating_add(1));
            let Some(row) = self.reprs.pop() else { break };
            work.fixed(row);
        }
        work.step(size_of::<Vec<(u32, StructRepr)>>().saturating_add(1));
        drop(take(&mut self.reprs));
        work.poll();
    }
}
// Successful output/input disposal, physical std/allocator/deallocator work,
// RSS/OOM/panic/unwind/hard-time and whole-module/native/proof authority remain
// OPEN. No new owner/grant/deadline/TLS/fuel/cancellation/configuration flag.
