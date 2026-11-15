// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact original make_aggregate structural/enum/array/lane diagnostics.
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
use trust_ir::ty::{EnumDef, FieldDef, RecordDef, StructDef};
use trust_ir::value::{EnumId, RecordId, StructId};
mod diagnostics;
mod enums;
mod lanes;
mod lookup;
mod render;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    ty: String,
    reason: String,
    op: String,
    role: String,
    expected: String,
    actual: String,
    render: String,
    location: String,
    enum_name: String,
    variant_name: String,
    spelling: String,
    discriminants: Vec<i128>,
    errors: Vec<ValidationError>,
}
/// Source is the exact table's borrowed module. Preserve nominal lookup,
/// enum tag/discriminants/inhabitedness, arity-before-lanes, uniform-array
/// spelling then known lane checks, in the original order. Borrowed field
/// views omit only redundant cloned Ty vectors (including repeated array
/// elements), never an ordinary check. Original caller must construct its
/// actual layout table observably and preserve full census/SSA/refinement/
/// nominal/source/proof checks; this local rule grants no such authority.
/// Same original session/site/fuel; child output is owned before any next fee.
/// All partial/prior diagnostics drain on operational refusal, never a shorter
/// success. Physical std/allocation/panic/RSS/hard-time bounds remain OPEN.
pub(super) fn validate_make_aggregate_observed<O: ExecutionObserver>(
    layouts: &trust_ir::LayoutTable<'_>,
    inst: &Inst,
    values: &ObservedValueTypes,
    block: BlockId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(layouts, inst, values, block, &mut work);
    state.retire(&mut work);
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
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.ty));
        work.flat(take(&mut self.reason));
        work.flat(take(&mut self.op));
        work.flat(take(&mut self.role));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
        work.flat(take(&mut self.render));
        work.flat(take(&mut self.location));
        work.flat(take(&mut self.enum_name));
        work.flat(take(&mut self.variant_name));
        work.flat(take(&mut self.spelling));
        work.rows(take(&mut self.discriminants));
    }
}
