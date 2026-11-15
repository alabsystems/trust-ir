// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Entire original slot_shape, with observed actual layout and owned children.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_sealable_slot::sealable_slot_type_observed;
use super::*;
use core::mem::{size_of, take};
use std::sync::Arc;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::shape::{PointerMetadataShape, TyLayoutKind, TyLayoutShape, TyShape};
use trust_ir::{LayoutError, LayoutTable};
mod layout_text;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    shape: Option<Arc<TyLayoutShape>>,
    error: Option<LayoutError>,
    render: String,
    reason: String,
}
/// Complete original Alloca count/carrier/layout/natural-alignment predicate.
/// Semantic Err is a full original String; outer Err is operational and never
/// substitutes a carrier or layout refusal. The table supplies the actual
/// original module and no layout callback/candidate result is accepted.
/// Full Arc/error/display children immediately enter State before the next fee.
/// All owned scratch drains before complete result publication even after stop.
/// No grant/deadline/TLS/owner/fuel or successful module/proof/source authority is
/// introduced. Original caller table/summary and successful input/output disposal,
/// full slot analysis/module adoption and physical hard bounds remain OPEN.
pub(super) fn slot_shape_observed<O: ExecutionObserver>(
    layouts: &LayoutTable<'_>,
    nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
    ty: &Ty,
    has_count: bool,
    align: Option<u64>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Result<u64, String>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(layouts, nominal, ty, has_count, align, &mut work);
    state.retire_scratch(&mut work);
    if matches!(&result, Ok(Some(_))) {
        work.flat(take(&mut state.reason));
    }
    match result.and_then(|answer| {
        work.publication_result()?;
        Ok(answer)
    }) {
        Ok(Some(natural)) => Ok(Ok(natural)),
        Ok(None) => Ok(Err(take(&mut state.reason))),
        Err(error) => {
            work.flat(take(&mut state.reason));
            Err(work.terminal(error))
        }
    }
}
impl State {
    fn run<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'_>,
        nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
        ty: &Ty,
        has_count: bool,
        align: Option<u64>,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<u64>> {
        work.admit(1, size_of::<bool>())?;
        if has_count {
            work.text(
                "an `Alloca` with a dynamic count is an array of `",
                &mut self.reason,
            )?;
            self.ty(ty, work)?;
            work.text(
                "`, and a handle slot holds exactly one value",
                &mut self.reason,
            )?;
            return Ok(None);
        }
        if !sealable_slot_type_observed(layouts.module(), nominal, ty, work.session, work.site)? {
            work.text("`", &mut self.reason)?;
            self.ty(ty, work)?;
            work.text("` is not a sealable slot type: a slot holds a handle, or a struct or tuple whose handle-reaching lanes are themselves handles, structs or tuples (an enum, record, array, closure, vector, set, sequence, refinement or reference carrying a handle stays refused)",&mut self.reason)?;
            return Ok(None);
        }
        work.admit(1, size_of::<Result<Arc<TyLayoutShape>, LayoutError>>())?;
        match layouts.ty_layout_observed(ty, work.session, work.site)? {
            Ok(shape) => self.shape = Some(shape),
            Err(error) => self.error = Some(error),
        }
        work.admit(1, size_of::<bool>())?;
        if self.error.is_some() {
            work.text("`", &mut self.reason)?;
            self.ty(ty, work)?;
            work.text("` has no computable layout (", &mut self.reason)?;
            work.admit(1, size_of::<String>())?;
            self.render = self
                .error
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?
                .display_observed(work.session, work.site)?;
            work.text(&self.render, &mut self.reason)?;
            work.flat(take(&mut self.render));
            work.admit(1, 0)?;
            work.text(")", &mut self.reason)?;
            return Ok(None);
        }
        self.project(ty, align, work)
    }
    fn project<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        align: Option<u64>,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<u64>> {
        work.admit(5, 2 * size_of::<Option<u64>>() + size_of::<u64>())?;
        let shape = self
            .shape
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        let size = shape.size_bytes();
        let bits = shape.align_bits;
        let natural = match (size, bits) {
            (Some(_), Some(bits)) if bits >= 8 && bits.is_multiple_of(8) => bits / 8,
            _ => {
                work.text("`", &mut self.reason)?;
                self.ty(ty, work)?;
                work.text("` has no byte-exact size and alignment (", &mut self.reason)?;
                work.admit(1, size_of::<String>())?;
                self.render = layout_text::shape(
                    self.shape
                        .as_deref()
                        .ok_or(ObservedValueError::InvalidRange)?,
                    work,
                )?;
                work.text(&self.render, &mut self.reason)?;
                work.flat(take(&mut self.render));
                work.admit(1, 0)?;
                work.text(
                    "), so its slot image is not a checkable memory cell",
                    &mut self.reason,
                )?;
                return Ok(None);
            }
        };
        work.admit(
            3,
            size_of::<Option<u64>>() + size_of::<u64>() + size_of::<bool>(),
        )?;
        if let Some(align) = align
            && (align < natural || !align.is_power_of_two())
        {
            work.text("the `Alloca` align ", &mut self.reason)?;
            work.unsigned(u128::from(align), &mut self.reason)?;
            work.text(
                " is not a power of two at least the natural alignment ",
                &mut self.reason,
            )?;
            work.unsigned(u128::from(natural), &mut self.reason)?;
            work.text(" of `", &mut self.reason)?;
            self.ty(ty, work)?;
            work.text("`", &mut self.reason)?;
            return Ok(None);
        }
        Ok(Some(natural))
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
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Arc<TyLayoutShape>>>() + 1);
        if let Some(shape) = self.shape.take() {
            let _ = shape.retire_arc_observed(work.session, work.site);
        }
        work.poll();
        work.step(size_of::<Option<LayoutError>>() + 1);
        if let Some(error) = self.error.take() {
            let _ = error.retire_observed(work.session, work.site);
        }
        work.poll();
        work.flat(take(&mut self.render));
    }
}
