// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn exact_pair<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Comparison/overflow identity never peels a Refine.
        let left = values.get_observed(lhs, work.session, work.site)?;
        let right = values.get_observed(rhs, work.session, work.site)?;
        if let (Some(left), Some(right)) = (left, right)
            && !left.structural_eq_observed(right, work.session, work.site)?
        {
            self.mismatch(Diagnostic::Operands(block), op, None, left, right, work)?;
        }
        work.admit(2, 2 * (size_of::<ValueId>() + size_of::<&str>()))?;
        for (role, value) in [("lhs", lhs), ("rhs", rhs)] {
            work.admit(1, size_of::<ValueId>() + size_of::<&str>())?;
            self.exact_operand(block, op, role, ty, value, values, work)?;
        }
        Ok(())
    }
    pub(super) fn exact_operand<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        role: &'static str,
        ty: &Ty,
        value: ValueId,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if let Some(actual) = values.get_observed(value, work.session, work.site)?
            && !actual.structural_eq_observed(ty, work.session, work.site)?
        {
            self.mismatch(Diagnostic::Operand(block), op, Some(role), ty, actual, work)?;
        }
        Ok(())
    }
    pub(super) fn integer_compare<O: ExecutionObserver>(
        &mut self,
        block: u32,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.exact_pair(block, "icmp", ty, lhs, rhs, values, work)?;
        work.admit(41, 0)?;
        if !(ty.is_integer()
            || ty.is_integer_vector()
            || ty.is_bool_vector()
            || matches!(ty, Ty::Ptr | Ty::Bool | Ty::Char))
        {
            self.category_error(Diagnostic::ICmp(block), None, ty, work)?;
        }
        Ok(())
    }
    pub(super) fn float_compare<O: ExecutionObserver>(
        &mut self,
        block: u32,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.exact_pair(block, "fcmp", ty, lhs, rhs, values, work)?;
        if !binary::category_matches(Category::Float, ty, work)? {
            self.category_error(Diagnostic::FCmp(block), None, ty, work)?;
        }
        Ok(())
    }
    pub(super) fn overflow<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: OverflowOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let token = tokens::overflow(op, work)?;
        self.exact_pair(block, token, ty, lhs, rhs, values, work)?;
        if !binary::category_matches(Category::Integer, ty, work)? {
            self.category_error(Diagnostic::OverflowInteger(block), Some(token), ty, work)?;
        }
        Ok(())
    }
}
