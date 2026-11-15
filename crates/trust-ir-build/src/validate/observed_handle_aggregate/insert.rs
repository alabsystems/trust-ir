// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn insert<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        ty: &Ty,
        aggregate: ValueId,
        field: u32,
        value: ValueId,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let base = values.get_observed(aggregate, work.session, work.site)?;
        work.admit(2, 2 * size_of::<bool>())?;
        if matches!(ty, Ty::Enum(_)) || base.is_some_and(|actual| matches!(actual, Ty::Enum(_))) {
            work.text("insert_field cannot rewrite a lane of a handle-bearing enum; construct the variant whole with make_aggregate",&mut self.reason)?;
            return Ok(false);
        }
        let Some(lanes) = lanes::register(module, ty, work)? else {
            return self.carrier(ty, work);
        };
        if !exact(values, aggregate, ty, work)? {
            work.text(
                "insert_field on a handle-bearing aggregate needs a base operand of exactly `",
                &mut self.reason,
            )?;
            self.ty(ty, work)?;
            work.text("`", &mut self.reason)?;
            return Ok(false);
        }
        work.admit(1, size_of::<usize>())?;
        let Some(lane) = lanes.at(field as usize, work)? else {
            work.text("insert_field lane ", &mut self.reason)?;
            work.unsigned(u128::from(field), &mut self.reason)?;
            work.text(" is out of range for `", &mut self.reason)?;
            self.ty(ty, work)?;
            work.text("`", &mut self.reason)?;
            return Ok(false);
        };
        if exact(values, value, lane, work)? {
            return Ok(true);
        }
        work.text("lane ", &mut self.reason)?;
        work.unsigned(u128::from(field), &mut self.reason)?;
        work.text(" of `", &mut self.reason)?;
        self.ty(ty, work)?;
        work.text("` is `", &mut self.reason)?;
        self.ty(lane, work)?;
        work.text("`; a lane of a handle-bearing aggregate is written only with a value of exactly that type",&mut self.reason)?;
        Ok(false)
    }
}
