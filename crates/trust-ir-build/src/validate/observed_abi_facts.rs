// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Whole actual ABI placement/reconciliation/signature-table module group.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_abi_lanes::ObservedAbiLanes;
use super::*;
use core::mem::{size_of, take};
use std::sync::Arc;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::shape::TyLayoutShape;
use trust_ir::{ArgExt, LayoutError, LayoutTable, ParamAttrs, PassMode};
mod casts;
mod scan;
mod slots;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'m> {
    lanes: Option<ObservedAbiLanes<'m>>,
    layout: Option<Result<Arc<TyLayoutShape>, LayoutError>>,
    pending_abi: Option<Result<(), String>>,
    render: String,
    slot: String,
    pending_slot: String,
    detail: String,
    errors: Vec<ValidationError>,
}
/// The complete original ABI group: once-per-module lane context; for each
/// physical function all legacy slot facts then its descriptor reconciliation;
/// then each stored signature's descriptor validation and ONLY on success its
/// target agreement. This table supplies the actual module and every source
/// row. It is diagnostic data, not physical ABI/source/module/proof authority.
/// Full caller must still run all original type/layout/target/ABI and authority
/// constituents; missing signature is skipped here only as originally, never
/// as an operational fallback. Wire-unrepresentable records retain the core
/// observed descriptor's typed outer refusal, not an accepted smaller result.
/// Every complete layout/ABI detail child, partial full String and prior error
/// is held before later fees. All scratch/lane context and refused outputs are
/// consumed in the SAME original session/site/fuel/grant/deadline/TLS; no new
/// owner, flag or exemption. Caller input/success output disposal and physical
/// std/allocator/deallocator/kernel/OOM/panic/unwind/RSS/hard-time remain OPEN.
pub(super) fn validate_module_abi_facts_observed<'m, O: ExecutionObserver>(
    layouts: &LayoutTable<'m>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut w = Work { session, site };
    w.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(layouts, &mut w);
    let cleanup = state.retire_scratch(&mut w);
    match result.and(cleanup).and_then(|()| w.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
            Err(w.terminal(error))
        }
    }
}
impl State<'_> {
    fn text_ty<O: ExecutionObserver>(&mut self, ty: &Ty, w: &mut Work<'_, '_, O>) -> R {
        w.admit(1, size_of::<String>())?;
        if self.render.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.render = ty.display_observed(w.session, w.site)?;
        w.text(&self.render, &mut self.detail)?;
        w.flat(take(&mut self.render));
        w.admit(1, 0)
    }
    fn commit<O: ExecutionObserver>(&mut self, function: &Function, w: &mut Work<'_, '_, O>) -> R {
        w.text(&self.slot, &mut self.pending_slot)?;
        w.reserve(&mut self.errors)?;
        w.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors.push(ValidationError::InvalidAbiSlotFact {
            function: function.id.index(),
            slot: take(&mut self.pending_slot),
            detail: take(&mut self.detail),
        });
        Ok(())
    }
    fn size<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'_>,
        ty: &Ty,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<u64>> {
        w.admit(
            1,
            size_of::<Option<Result<Arc<TyLayoutShape>, LayoutError>>>(),
        )?;
        if self.layout.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.layout = Some(layouts.ty_layout_observed(ty, w.session, w.site)?);
        w.admit(6, size_of::<Option<u64>>())?;
        let size = match &self.layout {
            Some(Ok(shape)) => shape.size_bytes(),
            _ => None,
        };
        self.retire_layout(w)?;
        w.admit(1, 0)?;
        Ok(size)
    }
    fn retire_layout<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        w.step(size_of::<Option<Result<Arc<TyLayoutShape>, LayoutError>>>().saturating_add(1));
        let result = match self.layout.take() {
            Some(Ok(shape)) => shape.retire_arc_observed(w.session, w.site),
            Some(Err(error)) => error.retire_observed(w.session, w.site),
            None => Ok(()),
        };
        w.poll();
        result.map_err(|e| w.terminal(e))
    }
    fn retire_abi<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.step(size_of::<Option<Result<(), String>>>().saturating_add(1));
        if let Some(Err(text)) = self.pending_abi.take() {
            w.flat(text)
        }
        w.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        let first = self.retire_layout(w);
        self.retire_abi(w);
        w.flat(take(&mut self.render));
        w.flat(take(&mut self.slot));
        w.flat(take(&mut self.pending_slot));
        w.flat(take(&mut self.detail));
        w.step(size_of::<Option<ObservedAbiLanes<'_>>>().saturating_add(1));
        let last = match self.lanes.take() {
            Some(lanes) => lanes.retire_observed(w.session, w.site),
            None => Ok(()),
        };
        w.poll();
        first.and(last)
    }
    fn abi_ready<O: ExecutionObserver>(&self, w: &mut Work<'_, '_, O>) -> R {
        w.admit(1, size_of::<Option<Result<(), String>>>())?;
        if self.pending_abi.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn abi_commit<O: ExecutionObserver>(&mut self, signature: u32, w: &mut Work<'_, '_, O>) -> R {
        w.admit(1, 0)?;
        if matches!(&self.pending_abi, Some(Err(_))) {
            w.reserve(&mut self.errors)?;
        }
        w.admit(
            1,
            size_of::<ValidationError>() + size_of::<Option<Result<(), String>>>(),
        )?;
        if let Some(Err(detail)) = self.pending_abi.take() {
            self.errors
                .push(ValidationError::InvalidSignatureAbi { signature, detail });
        }
        Ok(())
    }
}
