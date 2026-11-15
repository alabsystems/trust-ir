// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! The two separate original module ID diagnostic groups.
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
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    ids: Vec<u32>,
    errors: Vec<ValidationError>,
}
/// Original physical Struct-ID loop only, at its original module position.
/// Report each repeated occurrence, not one row per unique ambiguous ID.
/// Paid short-circuit searches of the actual preceding physical prefix replace
/// discarded set construction; no opaque hash/randomness or name lookup.
/// Data diagnostics only; all enum/type/layout/function/proof rules mandatory.
pub(super) fn validate_module_struct_ids_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut w = Work { session, site };
    w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.structs(module, &mut w);
    state.finish(result, &mut w)
}
/// Original catalog ambiguous Func-ID group only, after complete enum rules
/// and before symbol checks. Enumerate the exact source-bound catalog once in
/// numeric unique order; do not rebuild it or choose any ambiguous declaration.
/// Same original owner/site; no candidate callback or validation authority.
pub(super) fn validate_module_function_ids_observed<O: ExecutionObserver>(
    catalog: &ModuleFunctionCatalog<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut w = Work { session, site };
    w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.functions(catalog, &mut w);
    state.finish(result, &mut w)
}
impl State {
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        w: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        w.rows(take(&mut self.ids));
        match result.and_then(|()| w.publication()) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                let _ =
                    retire_validation_errors_observed(take(&mut self.errors), w.session, w.site);
                Err(w.terminal(error))
            }
        }
    }
}
// Complete catalog-returned IDs and prior diagnostics remain owned before any
// later fee and fully drain on refusal. No owner/grant/deadline/TLS/fuel/cap/
// flags/fallback. Successful original caller source/catalog/result disposal and
// physical std/allocator/deallocator/OOM/panic/unwind/RSS/hard100ms OPEN.
