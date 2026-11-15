// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn extract<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        ty: &Ty,
        aggregate: ValueId,
        field: u32,
        values: &ObservedValueTypes,
        block: BlockId,
        guards: Option<&ObservedHandleEnumGuards<'_>>,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let Some(aggregate_ty) = values.get_observed(aggregate, work.session, work.site)? else {
            work.text(
                "extract_field reads an aggregate of unknown type",
                &mut self.reason,
            )?;
            return Ok(false);
        };
        work.admit(1, size_of::<u32>())?;
        if let Ty::Enum(id) = aggregate_ty {
            let Some(def) = lookup::enumeration(module, *id, work)? else {
                return self.carrier(aggregate_ty, work);
            };
            let Some(repr) = def.canonical_tag_repr_observed(work.session, work.site)? else {
                work.text("enum `", &mut self.reason)?;
                self.ty(aggregate_ty, work)?;
                work.text(
                    "` has no canonical tag repr, so no lane of it can be projected",
                    &mut self.reason,
                )?;
                return Ok(false);
            };
            work.admit(1, size_of::<u32>())?;
            if field == 0 {
                work.admit(1, size_of::<Option<Ty>>())?;
                self.tag_ty = Some(repr.ty());
                let tag = self
                    .tag_ty
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?;
                if ty.structural_eq_observed(tag, work.session, work.site)? {
                    return Ok(true);
                }
                work.text("the tag lane of `", &mut self.reason)?;
                self.ty(aggregate_ty, work)?;
                work.text("` is `", &mut self.reason)?;
                // Type display is immediately retained before the next parent copy.
                work.admit(1, size_of::<String>())?;
                let tag = self
                    .tag_ty
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?;
                self.render = tag.display_observed(work.session, work.site)?;
                work.text(&self.render, &mut self.reason)?;
                work.flat(take(&mut self.render));
                work.admit(1, 0)?;
                work.text("`, not `", &mut self.reason)?;
                self.ty(ty, work)?;
                work.text("`", &mut self.reason)?;
                return Ok(false);
            }
            match def.effective_discriminants_observed(work.session, work.site)? {
                Some(discs) => self.discriminants = discs,
                None => {
                    work.text("enum `", &mut self.reason)?;
                    self.ty(aggregate_ty, work)?;
                    work.text("` has no resolvable discriminants", &mut self.reason)?;
                    return Ok(false);
                }
            }
            work.admit(1, size_of::<Option<&ObservedHandleEnumGuards<'_>>>())?;
            let Some(guards) = guards else {
                work.text("a handle lane of `", &mut self.reason)?;
                self.ty(aggregate_ty, work)?;
                work.text("` is read only under a tag switch that selects a variant carrying it, and no guard analysis is available here",&mut self.reason)?;
                return Ok(false);
            };
            self.selected = guards.variants_selected_at_observed(
                block,
                aggregate.index(),
                &self.discriminants,
                work.session,
                work.site,
            )?;
            let mut at = 0;
            while let Some(variant) = work.at(&self.selected, at)? {
                work.admit(1, size_of::<usize>())?;
                let variant = *variant;
                if let Some(row) = work.at(&def.variants, variant)? {
                    work.admit(1, size_of::<usize>())?;
                    if let Some(lane) = work.at(&row.fields, (field - 1) as usize)?
                        && lane.structural_eq_observed(ty, work.session, work.site)?
                    {
                        return Ok(true);
                    }
                }
                work.next(&mut at)?;
            }
            work.text("a handle lane of an enum is read only under a tag switch that selects a variant carrying it: lane ",&mut self.reason)?;
            work.unsigned(u128::from(field), &mut self.reason)?;
            work.text(" of `", &mut self.reason)?;
            self.ty(aggregate_ty, work)?;
            work.text("` is read as `", &mut self.reason)?;
            self.ty(ty, work)?;
            work.text("` in bb", &mut self.reason)?;
            work.unsigned(u128::from(block.index()), &mut self.reason)?;
            work.text(
                ", which no dominating switch case on that value's tag selects at that exact type",
                &mut self.reason,
            )?;
            return Ok(false);
        }
        let Some(lanes) = lanes::register(module, aggregate_ty, work)? else {
            return self.carrier(aggregate_ty, work);
        };
        work.admit(1, size_of::<usize>())?;
        let Some(lane) = lanes.at(field as usize, work)? else {
            work.text("extract_field lane ", &mut self.reason)?;
            work.unsigned(u128::from(field), &mut self.reason)?;
            work.text(" is out of range for `", &mut self.reason)?;
            self.ty(aggregate_ty, work)?;
            work.text("`", &mut self.reason)?;
            return Ok(false);
        };
        if lane.structural_eq_observed(ty, work.session, work.site)? {
            return Ok(true);
        }
        work.text("lane ", &mut self.reason)?;
        work.unsigned(u128::from(field), &mut self.reason)?;
        work.text(" of `", &mut self.reason)?;
        self.ty(aggregate_ty, work)?;
        work.text("` is `", &mut self.reason)?;
        self.ty(lane, work)?;
        work.text("`, not `", &mut self.reason)?;
        self.ty(ty, work)?;
        work.text(
            "`; a lane of a handle-bearing aggregate is read only at exactly its declared type",
            &mut self.reason,
        )?;
        Ok(false)
    }
}
