// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Default)]
struct Query {
    reason: String,
    render: String,
}
/// Complete original access rule over actual closed analysis data. Operational
/// refusal is outer Err and never missing analysis/slot or semantic Err text.
/// Complete original reason stays held through final full-result publication.
pub(in crate::validate) fn handle_slot_rule_observed<O: ExecutionObserver>(
    inst: &Inst,
    results: &[ValueId],
    values: &ObservedValueTypes,
    block: BlockId,
    index: usize,
    slots: Option<&ObservedSealedHandleSlots<'_>>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Result<(), String>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<Query>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = Query::default();
    let result = state.run(inst, results, values, (block, index), slots, &mut work);
    work.flat(take(&mut state.render));
    if matches!(&result, Ok(true)) {
        work.flat(take(&mut state.reason));
    }
    match result.and_then(|answer| {
        work.publication(size_of::<Result<(), String>>())?;
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
impl Query {
    fn ty<O: ExecutionObserver>(&mut self, ty: &Ty, work: &mut Work<'_, '_, O>) -> R {
        scan::text_type(ty, &mut self.render, &mut self.reason, work)
    }
    fn not_slot<O: ExecutionObserver>(
        &mut self,
        op: &str,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.text("`", &mut self.reason)?;
        work.text(op, &mut self.reason)?;
        work.text("` at `", &mut self.reason)?;
        self.ty(ty, work)?;
        work.text("` goes through a pointer that is not a sealed handle slot; a handle is loaded and stored only through a function-local `alloca` of exactly its type whose pointer never escapes (a handle behind a `Ref` / `RefMut` parameter is WS3.7 phase 2, and a handle-typed global is refused)",&mut self.reason)?;
        Ok(false)
    }
    fn option<O: ExecutionObserver>(
        &mut self,
        value: Option<u64>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<u64>>())?;
        match value {
            None => work.text("None", &mut self.reason),
            Some(value) => {
                work.text("Some(", &mut self.reason)?;
                work.unsigned(u128::from(value), &mut self.reason)?;
                work.text(")", &mut self.reason)
            }
        }
    }
    fn access<O: ExecutionObserver>(
        &mut self,
        op: &str,
        slot: &Slot,
        volatile: bool,
        align: Option<u64>,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, size_of::<bool>())?;
        if volatile {
            work.text("`", &mut self.reason)?;
            work.text(op, &mut self.reason)?;
            work.text("` of a handle slot of `", &mut self.reason)?;
            self.ty(&slot.ty, work)?;
            work.text("` may not be volatile", &mut self.reason)?;
            return Ok(false);
        }
        work.admit(2, 2 * size_of::<Option<u64>>() + size_of::<bool>())?;
        match (align, slot.natural_align) {
            (None, Some(_)) => Ok(true),
            (Some(align), Some(natural)) if align == natural => Ok(true),
            (align, natural) => {
                work.text("`", &mut self.reason)?;
                work.text(op, &mut self.reason)?;
                work.text("` of a handle slot of `", &mut self.reason)?;
                self.ty(&slot.ty, work)?;
                work.text("` states align ", &mut self.reason)?;
                self.option(align, work)?;
                work.text(", not the type's natural alignment ", &mut self.reason)?;
                self.option(natural, work)?;
                Ok(false)
            }
        }
    }
    fn run<O: ExecutionObserver>(
        &mut self,
        inst: &Inst,
        results: &[ValueId],
        values: &ObservedValueTypes,
        at: Point,
        slots: Option<&ObservedSealedHandleSlots<'_>>,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(
            1,
            size_of::<&Inst>()
                + size_of::<usize>()
                + size_of::<Option<&ObservedSealedHandleSlots<'_>>>(),
        )?;
        match inst {
            Inst::Alloca { ty, .. } => {
                work.admit(1, size_of::<Option<&Slot>>() + size_of::<ValueId>())?;
                let slot = match (slots, results) {
                    (Some(slots), [result]) => work.slot(&slots.slots, result.index())?,
                    _ => None,
                };
                let Some(slot) = slot else {
                    work.text("`Alloca` of `", &mut self.reason)?;
                    self.ty(ty, work)?;
                    work.text("`: ", &mut self.reason)?;
                    work.text(SEALED, &mut self.reason)?;
                    work.text(
                        "; this allocation defines no single slot pointer",
                        &mut self.reason,
                    )?;
                    return Ok(false);
                };
                work.admit(1, size_of::<Option<&String>>())?;
                match &slot.unsealed {
                    None => Ok(true),
                    Some(reason) => {
                        work.text("`Alloca` of `", &mut self.reason)?;
                        self.ty(ty, work)?;
                        work.text("`: ", &mut self.reason)?;
                        work.text(SEALED, &mut self.reason)?;
                        work.text("; ", &mut self.reason)?;
                        work.text(reason, &mut self.reason)?;
                        Ok(false)
                    }
                }
            }
            Inst::Load {
                ty,
                ptr,
                volatile,
                align,
            } => {
                let Some(slots) = slots else {
                    return self.not_slot("Load", ty, work);
                };
                let Some((owner, slot)) = slots.slot_of(*ptr, work)? else {
                    return self.not_slot("Load", ty, work);
                };
                work.admit(1, size_of::<Option<&String>>())?;
                if let Some(reason) = &slot.unsealed {
                    work.text("`Load` at `", &mut self.reason)?;
                    self.ty(ty, work)?;
                    work.text("` reads the slot %", &mut self.reason)?;
                    work.unsigned(u128::from(owner), &mut self.reason)?;
                    work.text(", which is not sealed: ", &mut self.reason)?;
                    work.text(reason, &mut self.reason)?;
                    return Ok(false);
                }
                if !ty.structural_eq_observed(&slot.ty, work.session, work.site)? {
                    work.text("`Load` at `", &mut self.reason)?;
                    self.ty(ty, work)?;
                    work.text("` reads the slot %", &mut self.reason)?;
                    work.unsigned(u128::from(owner), &mut self.reason)?;
                    work.text(" of `", &mut self.reason)?;
                    self.ty(&slot.ty, work)?;
                    work.text("`; ", &mut self.reason)?;
                    work.text(SEALED, &mut self.reason)?;
                    return Ok(false);
                }
                if !self.access("Load", slot, *volatile, *align, work)? {
                    return Ok(false);
                }
                if slots.initialized_at(slot, at, work)? {
                    return Ok(true);
                }
                work.text(
                    "load of a handle slot not dominated by a store: `Load` in bb",
                    &mut self.reason,
                )?;
                work.unsigned(u128::from(at.0.index()), &mut self.reason)?;
                work.text(" reads the slot %", &mut self.reason)?;
                work.unsigned(u128::from(owner), &mut self.reason)?;
                work.text(" of `", &mut self.reason)?;
                self.ty(ty, work)?;
                work.text("` where no store into it dominates the read, and an uninitialized word would be a forged handle",&mut self.reason)?;
                Ok(false)
            }
            Inst::Store {
                ty,
                ptr,
                value,
                volatile,
                align,
            } => {
                let Some(slots) = slots else {
                    return self.not_slot("Store", ty, work);
                };
                let Some((owner, slot)) = slots.slot_of(*ptr, work)? else {
                    return self.not_slot("Store", ty, work);
                };
                work.admit(1, size_of::<Option<&String>>())?;
                if let Some(reason) = &slot.unsealed {
                    work.text("`Store` at `", &mut self.reason)?;
                    self.ty(ty, work)?;
                    work.text("` writes the slot %", &mut self.reason)?;
                    work.unsigned(u128::from(owner), &mut self.reason)?;
                    work.text(", which is not sealed: ", &mut self.reason)?;
                    work.text(reason, &mut self.reason)?;
                    return Ok(false);
                }
                if !ty.structural_eq_observed(&slot.ty, work.session, work.site)? {
                    work.text("`Store` at `", &mut self.reason)?;
                    self.ty(ty, work)?;
                    work.text("` writes the slot %", &mut self.reason)?;
                    work.unsigned(u128::from(owner), &mut self.reason)?;
                    work.text(" of `", &mut self.reason)?;
                    self.ty(&slot.ty, work)?;
                    work.text("`; ", &mut self.reason)?;
                    work.text(SEALED, &mut self.reason)?;
                    return Ok(false);
                }
                let exact = match values.get_observed(*value, work.session, work.site)? {
                    Some(actual) => actual.structural_eq_observed(ty, work.session, work.site)?,
                    None => false,
                };
                if !exact {
                    work.text("`Store` into the handle slot %", &mut self.reason)?;
                    work.unsigned(u128::from(owner), &mut self.reason)?;
                    work.text(" of `", &mut self.reason)?;
                    self.ty(ty, work)?;
                    work.text("` needs a value of exactly that type", &mut self.reason)?;
                    return Ok(false);
                }
                self.access("Store", slot, *volatile, *align, work)
            }
            _ => {
                work.admit(1, size_of::<trust_ir::inst::InstShape>())?;
                work.text("`", &mut self.reason)?;
                work.text(inst.shape().name(), &mut self.reason)?;
                work.text("` is not a slot access", &mut self.reason)?;
                Ok(false)
            }
        }
    }
}
