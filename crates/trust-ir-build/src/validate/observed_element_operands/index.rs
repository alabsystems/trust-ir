// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn index<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        index: ValueId,
        aggregate: Option<&Ty>,
        values: &ObservedValueTypes,
        constants: &[(u32, i128)],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let sequence = matches!(aggregate, Some(Ty::Sequence(_)));
        if let Some(index_ty) = values.get_observed(index, work.session, work.site)? {
            // Original integer/signed predicates are fixed shallow tables.
            work.admit(41, 0)?;
            if !index_ty.is_integer() {
                self.start(op, work)?;
                work.text("index must be integer, got ", &mut self.reason)?;
                self.ty(index_ty, work)?;
                self.commit(block, work)?;
            } else if sequence && index_ty.is_signed() {
                self.start(op, work)?;
                work.text(
                    "a sequence index must be an unsigned integer (a sequence has no static \
                     length, so non-negativity is decidable only from the index type), got ",
                    &mut self.reason,
                )?;
                self.ty(index_ty, work)?;
                self.commit(block, work)?;
            }
        }
        let Some(value) = work.constant(constants, index.index())? else {
            return Ok(());
        };
        work.admit(3, size_of::<Option<u32>>())?;
        // Exactly element_op_lane_count: an array longer than u32::MAX
        // has no finite count here. Do not widen this original constituent.
        let lanes = match aggregate {
            Some(Ty::Vector(_, lanes)) => Some(*lanes),
            Some(Ty::Array(_, length)) => u32::try_from(*length).ok(),
            _ => None,
        };
        work.admit(3, 0)?;
        match lanes {
            Some(lanes) => {
                work.admit(2, 0)?;
                if value < 0 || value >= i128::from(lanes) {
                    self.start(op, work)?;
                    work.text("constant lane index ", &mut self.reason)?;
                    work.signed(value, &mut self.reason)?;
                    work.text(" is out of range for ", &mut self.reason)?;
                    work.number(u128::from(lanes), &mut self.reason)?;
                    work.text(" lanes", &mut self.reason)?;
                    self.commit(block, work)?;
                }
            }
            None if aggregate.is_some() && value < 0 => {
                self.start(op, work)?;
                work.text("constant element index ", &mut self.reason)?;
                work.signed(value, &mut self.reason)?;
                work.text(" is negative", &mut self.reason)?;
                self.commit(block, work)?;
            }
            None => {}
        }
        Ok(())
    }
}
