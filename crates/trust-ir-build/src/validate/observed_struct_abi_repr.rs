// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original transparent/packed ABI repr diagnostics.
use super::*;
use core::mem::{size_of, take};
use std::sync::Arc;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::shape::TyLayoutShape;
use trust_ir::{LayoutError, LayoutTable, StructRepr};
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'m> {
    table: Option<LayoutTable<'m>>,
    shape: Option<Arc<TyLayoutShape>>,
    error: Option<LayoutError>,
    errors: Vec<ValidationError>,
}
/// Original physical struct repr rule, separate from declared byte layout and
/// FFI checks. Transparent counts every field not exactly size=0/align=1 using
/// actual module-aware observed layout. Semantic layout errors count as
/// nontrivial, preserving the original conservative rule. Packed diagnoses
/// precisely zero/non-power-of-two clamps. No ABI/module/source/proof authority.
pub fn validate_module_struct_abi_repr_observed<O: ExecutionObserver>(
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
    state.finish(result, &mut work)
}
impl State<'_> {
    fn query<O: ExecutionObserver>(&mut self, ty: &Ty, work: &mut Work<'_, '_, O>) -> R<bool> {
        work.admit(2, 0)?;
        if self.shape.is_some() || self.error.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        match self
            .table
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?
            .ty_layout_observed(ty, work.session, work.site)?
        {
            Ok(shape) => self.shape = Some(shape),
            Err(error) => self.error = Some(error),
        }
        work.admit(7, size_of::<bool>())?;
        let trivial = self
            .shape
            .as_ref()
            .is_some_and(|shape| shape.size_bits == 0 && shape.align_bits == Some(8));
        self.retire_query(work);
        work.admit(1, 0)?;
        Ok(trivial)
    }
    fn retire_query<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Arc<TyLayoutShape>>>().saturating_add(1));
        if let Some(shape) = self.shape.take() {
            let _ = shape.retire_arc_observed(work.session, work.site);
        }
        work.poll();
        work.step(size_of::<Option<LayoutError>>().saturating_add(1));
        if let Some(error) = self.error.take() {
            let _ = error.retire_observed(work.session, work.site);
        }
        work.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_query(work);
        // Private fresh table with observed calls only: ordinary memo empty.
        // Fixed release is specific here, not general populated memo cleanup.
        work.step(size_of::<Option<LayoutTable<'_>>>().saturating_add(1));
        drop(self.table.take());
        work.poll();
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(work);
        match result.and_then(|()| work.publication()) {
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
}
// Original supplied session/site; no owner/grant/deadline/TLS/fuel/flag/fallback.
// Full ABI/module/native orchestration, old layout Work pricing/retirement,
// successful caller/input disposal and physical std/allocator/deallocator/OOM/
// panic/unwind/RSS/hard100ms remain OPEN.
