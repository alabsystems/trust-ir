// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::graph::Flow;
use super::*;
use trust_ir::inst::{BinOp, CastOp};
impl Flow<'_> {
    pub(super) fn derive<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        inst: &Inst,
        repr: Option<Option<(i128, i128)>>,
        work: &mut Work<'_, '_, O>,
    ) -> R<Fact> {
        work.admit(1, size_of::<(Fact, Fact, Option<(i128, i128)>)>())?;
        match inst {
            Inst::Copy { operand, .. } => self.assumed(module, *operand, work),
            Inst::Select {
                then_val, else_val, ..
            } => {
                let a = self.assumed(module, *then_val, work)?;
                let b = self.assumed(module, *else_val, work)?;
                self.facts.join(module, a, b, work)
            }
            Inst::Const { ty, value } => {
                let range = repr.unwrap_or_else(|| trust_ir::propagate::integer_value_range(ty));
                Ok(match (range, value) {
                    (Some((lo, hi)), Constant::Int(v)) if lo <= *v && *v <= hi => {
                        Fact::Interval(*v, *v)
                    }
                    (Some(_), Constant::Bool(b)) => {
                        let n = i128::from(*b);
                        Fact::Interval(n, n)
                    }
                    _ => Fact::Top,
                })
            }
            Inst::ICmp { ty, .. } | Inst::FCmp { ty, .. } => Ok(if matches!(ty, Ty::Vector(..)) {
                Fact::Top
            } else {
                Fact::Interval(0, 1)
            }),
            Inst::BinOp {
                op: op @ (BinOp::Add | BinOp::Sub),
                ty,
                lhs,
                rhs,
            } => {
                let a = self.assumed(module, *lhs, work)?;
                let b = self.assumed(module, *rhs, work)?;
                let Some((tlo, thi)) =
                    repr.unwrap_or_else(|| trust_ir::propagate::integer_value_range(ty))
                else {
                    return Ok(Fact::Top);
                };
                let (Some((al, ah)), Some((bl, bh))) = (
                    lattice::bounds(module, self.facts.view(module, a, work)?, 0, work)?,
                    lattice::bounds(module, self.facts.view(module, b, work)?, 0, work)?,
                ) else {
                    return Ok(Fact::Top);
                };
                let (lo, hi) = if *op == BinOp::Add {
                    (al.checked_add(bl), ah.checked_add(bh))
                } else {
                    (al.checked_sub(bh), ah.checked_sub(bl))
                };
                Ok(match (lo, hi) {
                    (Some(lo), Some(hi)) if tlo <= lo && lo <= hi && hi <= thi => {
                        Fact::Interval(lo, hi)
                    }
                    _ => Fact::Top,
                })
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let fact = self.assumed(module, *operand, work)?;
                let Some((lo, hi)) =
                    lattice::bounds(module, self.facts.view(module, fact, work)?, 0, work)?
                else {
                    return Ok(Fact::Top);
                };
                let Some((dl, dh)) = trust_ir::propagate::integer_value_range(dst_ty) else {
                    return Ok(Fact::Top);
                };
                let survives = match op {
                    CastOp::ZExt => lo >= 0,
                    CastOp::SExt => src_ty.is_signed(),
                    CastOp::Trunc => dl <= lo && hi <= dh,
                    _ => false,
                };
                Ok(if survives && dl <= lo && lo <= hi && hi <= dh {
                    Fact::Interval(lo, hi)
                } else {
                    Fact::Top
                })
            }
            _ => Ok(Fact::Top),
        }
    }
}
