// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn make<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        ty: &Ty,
        variant: Option<u32>,
        fields: &[ValueId],
        values: &ObservedValueTypes,
        nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let lanes = if let Ty::Enum(id) = ty {
            let Some(def) = lookup::enumeration(module, *id, work)? else {
                return self.carrier(ty, work);
            };
            work.admit(1, size_of::<Option<u32>>())?;
            let Some(variant) = variant else {
                return self.carrier(ty, work);
            };
            work.admit(1, size_of::<usize>())?;
            let Some(row) = work.at(&def.variants, variant as usize)? else {
                return self.carrier(ty, work);
            };
            lanes::Lanes::Types(&row.fields)
        } else {
            let Some(lanes) = lanes::register(module, ty, work)? else {
                return self.carrier(ty, work);
            };
            lanes
        };
        work.admit(1, size_of::<usize>())?;
        let declared = lanes.len(work)?;
        if fields.len() != declared {
            work.text("make_aggregate at `", &mut self.reason)?;
            self.ty(ty, work)?;
            work.text("` supplies ", &mut self.reason)?;
            work.unsigned(fields.len() as u128, &mut self.reason)?;
            work.text(" lane operand(s) for ", &mut self.reason)?;
            work.unsigned(declared as u128, &mut self.reason)?;
            work.text(
                " declared lane(s); a handle-bearing aggregate is built whole or not at all",
                &mut self.reason,
            )?;
            return Ok(false);
        }
        let mut index = 0;
        while let Some(operand) = work.at(fields, index)? {
            let lane = lanes
                .at(index, work)?
                .ok_or(ObservedValueError::InvalidRange)?;
            if nominal.contains_handle_observed(lane, work.session, work.site)? {
                work.admit(1, size_of::<ValueId>())?;
                if !exact(values, *operand, lane, work)? {
                    work.text("make_aggregate lane ", &mut self.reason)?;
                    work.unsigned(index as u128, &mut self.reason)?;
                    work.text(" of `", &mut self.reason)?;
                    self.ty(ty, work)?;
                    work.text("` is declared `", &mut self.reason)?;
                    self.ty(lane, work)?;
                    work.text("`, which reaches an opaque runtime handle, so it must be fed by an operand of exactly that type",&mut self.reason)?;
                    return Ok(false);
                }
            }
            work.next(&mut index)?;
        }
        Ok(true)
    }
}
