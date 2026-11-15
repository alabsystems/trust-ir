// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn unary<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: UnOp,
        ty: &Ty,
        operand: ValueId,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let token = tokens::unary(op, work)?;
        self.exact_operand(block, token, "operand", ty, operand, values, work)?;
        work.admit(13, 0)?;
        let category = match op {
            UnOp::Neg | UnOp::CtPop | UnOp::CtLz | UnOp::CtTz | UnOp::BSwap | UnOp::BitReverse => {
                Category::Integer
            }
            UnOp::Not => {
                work.admit(1, 0)?;
                if matches!(ty, Ty::Bool) {
                    self.ready(work)?;
                    return self.commit(Diagnostic::ScalarBoolNot(block), work);
                }
                // Scalar Bool was separately refused, so the common union
                // below now admits only integer or integer/bool vectors.
                Category::IntegerOrBool
            }
            UnOp::FNeg | UnOp::FAbs | UnOp::FSqrt | UnOp::FFloor | UnOp::FCeil | UnOp::FTrunc => {
                Category::Float
            }
        };
        if !binary::category_matches(category, ty, work)? {
            let kind = match category {
                Category::Float => Diagnostic::Float(block),
                Category::Integer | Category::IntegerOrBool => Diagnostic::Integer(block),
                Category::Bool => return Err(ObservedValueError::InvalidRange),
            };
            self.category_error(kind, Some(token), ty, work)?;
        }
        Ok(())
    }
}
