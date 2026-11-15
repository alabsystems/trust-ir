// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact T1–T7 drop-glue table rules; claims never authenticate destructors.
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
mod checks;
mod render;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    ty: String,
    reason: String,
    errors: Vec<ValidationError>,
}
/// Preserve every ordinary drop-glue table diagnostic in physical row order.
/// Duplicate type keys use exact observed structural equality; function IDs
/// resolve only when unique in the exact source module, matching its catalog.
/// No hash-map/tree/string traversal runs opaquely beneath a bracket. The
/// replacement scans may be quadratic and remain subject to the same caller
/// budget. This checks carried table spelling, not source-language destructor,
/// runtime/body/proof authority, completeness or full module validity.
pub(crate) fn validate_module_drop_glue_table_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, &mut work);
    state.finish(result, &mut work)
}
impl State {
    fn run<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        let mut entry = 0usize;
        let mut previous = None;
        while let Some(row) = work.at(&module.drop_glue, entry)? {
            work.admit(2, size_of::<u32>() + size_of::<Option<u32>>())?;
            let glue = row.glue.index();
            if let Some(before) = previous
                && glue <= before
            {
                self.order_reason(glue, before, work)?;
                self.emit(entry, glue, work)?;
            }
            previous = Some(glue);
            let mut earlier = 0usize;
            loop {
                work.admit(1, 2 * size_of::<usize>())?;
                if earlier >= entry {
                    break;
                }
                let prior = work
                    .at(&module.drop_glue, earlier)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                if row
                    .ty
                    .structural_eq_observed(&prior.ty, work.session, work.site)?
                {
                    self.duplicate_reason(&row.ty, work)?;
                    self.emit(entry, glue, work)?;
                    break;
                }
                work.next(&mut earlier)?;
            }
            work.admit(1, size_of::<bool>())?;
            if matches!(&row.ty, Ty::Refine(..)) {
                self.key_reason(&row.ty, KeyRule::Refined, work)?;
                self.emit(entry, glue, work)?;
            } else if row.ty.is_trivially_droppable_observed(
                &module.types,
                work.session,
                work.site,
            )? {
                self.key_reason(&row.ty, KeyRule::Trivial, work)?;
                self.emit(entry, glue, work)?;
            }
            if let Some(function) = work.unique(module, row.glue)? {
                self.function(module, function, entry, glue, work)?;
            } else {
                work.text(
                    "the glue names no function of this module (or a duplicated id)",
                    &mut self.reason,
                )?;
                self.emit(entry, glue, work)?;
            }
            work.next(&mut entry)?;
        }
        Ok(())
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        work.flat(take(&mut self.ty));
        work.flat(take(&mut self.reason));
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
#[derive(Clone, Copy)]
enum KeyRule {
    Refined,
    Trivial,
}
