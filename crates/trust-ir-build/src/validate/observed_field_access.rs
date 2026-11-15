// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual module ExtractField/InsertField structural and enum-lane rules.
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
#[derive(Clone, Copy)]
enum Mode {
    Extract,
    Insert(ValueId),
}
impl Mode {
    fn op(self) -> &'static str {
        match self {
            Self::Extract => "extract_field",
            Self::Insert(_) => "insert_field",
        }
    }
}
#[derive(Default)]
struct State<'m> {
    op: String,
    role: String,
    reason: String,
    expected: String,
    actual: String,
    render: String,
    tag: Option<Ty>,
    lanes: Vec<(&'m str, &'m Ty)>,
    errors: Vec<ValidationError>,
}
/// Exact original result-before-lane error order, real nominal index+ID/first
/// fallback lookup, register closure captures and enum candidate-lane matching.
/// Borrowed declarations replace redundant cloned field/name/type Vecs only;
/// mandatory full inventory/SSA/refinement/handle guards/module/source/proof
/// remain separate. All actual traversal/child/diagnostic growth uses the same
/// original session/site/fuel, with complete owning scratch/output retirement.
/// No fallback on operational stop or new owner/grant/deadline/TLS/flags;
/// physical std/allocator/panic/hard-time and original caller duties stay OPEN.
pub(super) fn validate_field_access_observed<O: ExecutionObserver>(
    module: &Module,
    inst: &Inst,
    values: &ObservedValueTypes,
    block: BlockId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, inst, values, block, &mut work);
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
impl State<'_> {
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.op));
        work.flat(take(&mut self.role));
        work.flat(take(&mut self.reason));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
        work.flat(take(&mut self.render));
        work.step(size_of::<Option<Ty>>() + 1);
        if let Some(ty) = self.tag.take() {
            let _ = ty.retire_observed(work.session, work.site);
        }
        work.poll();
        work.rows(take(&mut self.lanes));
    }
}
