// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn binary<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: BinOp,
        declared: &Ty,
        lhs: ValueId,
        rhs: ValueId,
        values: &ObservedValueTypes,
        module: Option<&Module>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let token = tokens::binary(op, work)?;
        // Preserve the original short-circuit any-refined lookup, including
        // its check before the standalone declared-type condition.
        let mut refined = false;
        work.admit(2, 2 * size_of::<ValueId>())?;
        for value in [lhs, rhs] {
            work.admit(1, size_of::<ValueId>())?;
            if let Some(ty) = values.get_observed(value, work.session, work.site)? {
                work.admit(1, 0)?;
                if matches!(ty, Ty::Refine(..)) {
                    refined = true;
                    break;
                }
            }
        }
        work.admit(2, 0)?;
        if module.is_none() && (matches!(declared, Ty::Refine(..)) || refined) {
            return Ok(());
        }
        self.pair(block, token, lhs, rhs, values, module, work)?;
        work.admit(2, 2 * (size_of::<ValueId>() + size_of::<&str>()))?;
        for (role, value) in [("lhs", lhs), ("rhs", rhs)] {
            work.admit(1, size_of::<ValueId>() + size_of::<&str>())?;
            if let Some(actual) = values.get_observed(value, work.session, work.site)? {
                let actual_repr = representation(module, actual, work)?;
                let declared_repr = representation(module, declared, work)?;
                if let (Some(actual_repr), Some(declared_repr)) = (actual_repr, declared_repr)
                    && !actual_repr.structural_eq_observed(
                        declared_repr,
                        work.session,
                        work.site,
                    )?
                {
                    self.mismatch(
                        Diagnostic::Operand(block),
                        token,
                        Some(role),
                        declared,
                        actual,
                        work,
                    )?;
                }
            }
        }
        let Some(category_ty) = representation(module, declared, work)? else {
            return Ok(());
        };
        work.admit(26, size_of::<Category>())?;
        let category = match op {
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::UDiv
            | BinOp::SDiv
            | BinOp::URem
            | BinOp::SRem
            | BinOp::Shl
            | BinOp::LShr
            | BinOp::AShr
            | BinOp::RotL
            | BinOp::RotR => Category::Integer,
            BinOp::BAnd | BinOp::BOr | BinOp::BXor => Category::Bool,
            BinOp::And | BinOp::Or | BinOp::Xor => Category::IntegerOrBool,
            BinOp::FAdd
            | BinOp::FSub
            | BinOp::FMul
            | BinOp::FDiv
            | BinOp::FRem
            | BinOp::FMin
            | BinOp::FMax
            | BinOp::FCopySign => Category::Float,
        };
        if !category_matches(category, category_ty, work)? {
            let kind = match category {
                Category::Integer | Category::IntegerOrBool => Diagnostic::Integer(block),
                Category::Bool => Diagnostic::Bool(block),
                Category::Float => Diagnostic::Float(block),
            };
            self.category_error(kind, Some(token), declared, work)?;
        }
        Ok(())
    }

    pub(super) fn pair<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        lhs: ValueId,
        rhs: ValueId,
        values: &ObservedValueTypes,
        module: Option<&Module>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let left = values.get_observed(lhs, work.session, work.site)?;
        let right = values.get_observed(rhs, work.session, work.site)?;
        if let (Some(left), Some(right)) = (left, right) {
            let left_repr = representation(module, left, work)?;
            let right_repr = representation(module, right, work)?;
            if let (Some(lrepr), Some(rrepr)) = (left_repr, right_repr)
                && !lrepr.structural_eq_observed(rrepr, work.session, work.site)?
            {
                self.mismatch(Diagnostic::Operands(block), op, None, left, right, work)?;
            }
        }
        Ok(())
    }
}

fn representation<'a, O: ExecutionObserver>(
    module: Option<&'a Module>,
    ty: &'a Ty,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'a Ty>> {
    work.admit(1, size_of::<Option<&Ty>>())?;
    match ty {
        Ty::Refine(base, _) => {
            let Some(module) = module else {
                return Ok(None);
            };
            work.admit(1, size_of::<usize>())?;
            Ok(module.types.get(base.as_usize()))
        }
        other => Ok(Some(other)),
    }
}
pub(super) fn category_matches<O: ExecutionObserver>(
    category: Category,
    ty: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    // The called original predicates are fixed shallow discriminant tables,
    // with at most one vector-element test and no recursive nominal walk.
    work.admit(41, 0)?;
    Ok(match category {
        Category::Integer => ty.is_integer() || ty.is_integer_vector(),
        Category::Bool => matches!(ty, Ty::Bool) || ty.is_bool_vector(),
        Category::IntegerOrBool => {
            ty.is_integer()
                || ty.is_integer_vector()
                || ty.is_bool_vector()
                || matches!(ty, Ty::Bool)
        }
        Category::Float => ty.is_float() || ty.is_float_vector(),
    })
}
