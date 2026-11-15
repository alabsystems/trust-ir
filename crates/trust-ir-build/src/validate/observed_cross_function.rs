// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Whole original per-function module-table/cross-edge diagnostic group.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_handle_enum_guards::ObservedHandleEnumGuards;
use super::observed_indirect_calls::ObservedIndirectCalls;
use super::observed_sealed_slots::ObservedSealedHandleSlots;
use super::*;
use core::mem::{size_of, take};
use trust_ir::ObservedNominalTypeReachability;
use trust_ir::dialect::schema::DialectSchemaRegistry;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod initialize;
mod merge;
mod nodes;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'c, 'm> {
    signature: Option<&'m FuncTy>,
    getter: Option<Result<&'m FuncTy, ValidationError>>,
    values: Option<ObservedValueTypes>,
    guards: Option<ObservedHandleEnumGuards<'m>>,
    slots: Option<ObservedSealedHandleSlots<'m>>,
    indirect: Option<ObservedIndirectCalls<'c, 'm>>,
    pending: Vec<ValidationError>,
    errors: Vec<ValidationError>,
}
/// The complete original cross-function closure, in its exact semantic error
/// order, with actual function derived from physical catalog coordinates. The
/// caller supplies its actual full inventory census and the corresponding
/// nominal summary, never a candidate-selected exemption; presence and source
/// identity are checked. Layout and catalog must borrow the SAME source Module.
/// All original deep SSA/module/refinement/ABI/authority/proof validators remain
/// mandatory. This is diagnostic data, not their result or a source capability.
///
/// Every complete getter/batch/map/guard/slot/indirect child is held in State
/// before the next fallible step; no operational failure becomes missing data,
/// an empty analysis or a shorter successful result. All children and prior
/// errors retire under the SAME original session/site/fuel/grant/deadline/TLS.
/// The closure target map remains eager once per function as originally. Its
/// pointer component starts as borrowed empty state and builds actual analysis
/// only at an indirect query: no additional unobserved census or claimed reuse
/// of a separately retired deep SSA analysis. Fixed empty pointer setup is
/// honestly charged even in a function with no indirect edge.
/// Successful caller source/layout/catalog/nominal/output disposal and physical
/// std/allocator/deallocator/OOM/panic/unwind/RSS/hard-time bounds remain OPEN.
pub(super) fn validate_cross_function_observed<'m, O: ExecutionObserver>(
    layouts: &trust_ir::LayoutTable<'m>,
    catalog: &ModuleFunctionCatalog<'m>,
    physical_function: usize,
    census: NominalCensus,
    nominal: Option<&ObservedNominalTypeReachability<'m>>,
    schemas: Option<&DialectSchemaRegistry>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_, '_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(
        layouts,
        catalog,
        physical_function,
        census,
        nominal,
        schemas,
        &mut work,
    );
    let cleanup = state.retire_children(&mut work);
    match result.and(cleanup).and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
