// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original register-level handle lane rule, with actual inner work.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_handle_enum_guards::ObservedHandleEnumGuards;
use super::observed_value_types::ObservedValueTypes;
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::ty::{EnumDef, FieldDef, StructDef};
use trust_ir::value::{EnumId, StructId};
mod extract;
mod insert;
mod lanes;
mod lookup;
mod make;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    reason: String,
    render: String,
    discriminants: Vec<i128>,
    selected: Vec<usize>,
    tag_ty: Option<Ty>,
}
/// Exact semantic rule; inner Err(String) is a complete original diagnostic,
/// outer Err is operational refusal and NEVER semantic unavailability. Borrowed
/// lanes replace only redundant cloned declarations; module index+ID-checked
/// fast paths and original off-index first-match scans remain actually observed.
/// Original module/value/nominal/guard data and same owner/site are required.
/// This is not a module/SSA/handle-origin/proof or source authority. Every owning
/// child enters State before any next fee; scratch and partial reason are fully
/// consumed after stop. Full caller adoption/mandatory checks, input/successful
/// output disposal and physical std/allocator/panic/hard bounds remain OPEN.
pub(super) fn handle_aggregate_lane_rule_observed<O: ExecutionObserver>(
    module: &Module,
    inst: &Inst,
    values: &ObservedValueTypes,
    nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
    block: BlockId,
    guards: Option<&ObservedHandleEnumGuards<'_>>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Result<(), String>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, inst, values, nominal, block, guards, &mut work);
    state.retire_scratch(&mut work);
    if matches!(&result, Ok(true)) {
        work.flat(take(&mut state.reason));
    }
    match result.and_then(|answer| {
        work.publication_result()?;
        Ok(answer)
    }) {
        Ok(true) => Ok(Ok(())),
        Ok(false) => Ok(Err(take(&mut state.reason))),
        Err(error) => {
            work.flat(take(&mut state.reason));
            Err(work.terminal(error))
        }
    }
}
impl State {
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        inst: &Inst,
        values: &ObservedValueTypes,
        nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
        block: BlockId,
        guards: Option<&ObservedHandleEnumGuards<'_>>,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(
            1,
            size_of::<&Inst>()
                + size_of::<Option<u32>>()
                + 2 * size_of::<ValueId>()
                + size_of::<u32>(),
        )?;
        match inst {
            Inst::MakeAggregate {
                ty,
                variant,
                fields,
            } => self.make(module, ty, *variant, fields, values, nominal, work),
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => self.extract(module, ty, *aggregate, *field, values, block, guards, work),
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => self.insert(module, ty, *aggregate, *field, *value, values, work),
            _ => {
                work.admit(1, size_of::<trust_ir::inst::InstShape>())?;
                work.text("`", &mut self.reason)?;
                work.text(inst.shape().name(), &mut self.reason)?;
                work.text("` is not an aggregate lane operation", &mut self.reason)?;
                Ok(false)
            }
        }
    }
    fn ty<O: ExecutionObserver>(&mut self, ty: &Ty, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<String>())?;
        if self.render.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.render = ty.display_observed(work.session, work.site)?;
        work.text(&self.render, &mut self.reason)?;
        work.flat(take(&mut self.render));
        work.admit(1, 0)
    }
    fn carrier<O: ExecutionObserver>(&mut self, ty: &Ty, work: &mut Work<'_, '_, O>) -> R<bool> {
        work.text("`", &mut self.reason)?;
        self.ty(ty, work)?;
        work.text("` is not a handle carrier: an opaque runtime handle may sit only in a struct, tuple or enum lane (a record, array, closure, vector, set, sequence, refinement or global carrying one is refused)",&mut self.reason)?;
        Ok(false)
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Ty>>() + 1);
        if let Some(ty) = self.tag_ty.take() {
            let _ = ty.retire_observed(work.session, work.site);
        }
        work.poll();
        work.rows(&mut self.discriminants);
        work.rows(&mut self.selected);
        work.flat(take(&mut self.render));
    }
}
fn exact<O: ExecutionObserver>(
    values: &ObservedValueTypes,
    value: ValueId,
    expected: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    match values.get_observed(value, work.session, work.site)? {
        Some(actual) => actual.structural_eq_observed(expected, work.session, work.site),
        None => Ok(false),
    }
}
