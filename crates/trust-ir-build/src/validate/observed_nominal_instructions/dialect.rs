// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    clippy::if_same_then_else,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn dialect<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        inst: &Inst,
        values: &ObservedValueTypes,
        nominal: &ObservedNominalTypeReachability<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R<Decision> {
        work.admit(1, size_of::<&Inst>())?;
        let yes = match inst {
            Inst::Copy { ty, operand } => census::exact(*operand, ty, values, work)?,
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                census::exact(*cond, &Ty::Bool, values, work)?
                    && census::exact(*then_val, ty, values, work)?
                    && census::exact(*else_val, ty, values, work)?
            }
            Inst::Const {
                ty: Ty::Func(_),
                value: Constant::FnDef(_),
            } => true,
            Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::FnItem(id),
                dst_ty: Ty::Func(signature),
                ..
            } => census::exact_item(module, *id, *signature, work)?,
            Inst::Call { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::Invoke { .. }
            | Inst::AssertInvoke { .. }
            | Inst::Return { .. }
            | Inst::Br { .. }
            | Inst::DialectOp(_) => true,
            Inst::CallIndirect { callee, sig, .. }
            | Inst::CallIndirectCannotUnwind { callee, sig, .. }
            | Inst::InvokeIndirect { callee, sig, .. } => {
                let actual = values.get_observed(*callee, work.session, work.site)?;
                work.admit(1, size_of::<bool>())?;
                match actual {
                    Some(Ty::Func(actual)) if actual == sig => true,
                    Some(Ty::FnItem(id)) => census::exact_item(module, *id, *sig, work)?,
                    Some(ty) => {
                        // Actual fixed-discriminant original shape predicate; no nested walk.
                        work.admit(1, size_of::<bool>())?;
                        if !ty.is_pointer_like() {
                            false
                        } else if nominal.contains_dialect_observed(ty, work.session, work.site)? {
                            false
                        } else if Self::returns_dialect(module, *sig, nominal, work)? {
                            work.text("a pointer-like indirect callee cannot originate a nominal dialect value; call through the exact `Ty::Func` signature",&mut self.detail)?;
                            return Ok(Decision::DetailedRefusal);
                        } else {
                            true
                        }
                    }
                    None => false,
                }
            }
            Inst::CondBr { cond, .. } => census::exact(*cond, &Ty::Bool, values, work)?,
            Inst::Switch { value, .. } => {
                match values.get_observed(*value, work.session, work.site)? {
                    Some(ty) => !nominal.contains_dialect_observed(ty, work.session, work.site)?,
                    None => false,
                }
            }
            _ => false,
        };
        Ok(if yes {
            Decision::Allowed
        } else {
            Decision::GenericRefusal
        })
    }
    fn returns_dialect<O: ExecutionObserver>(
        module: &Module,
        sig: trust_ir::value::FuncTyId,
        nominal: &ObservedNominalTypeReachability<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let Some(signature) = work.at(&module.func_types, sig.as_usize())? else {
            return Ok(true);
        };
        let mut at = 0;
        while let Some(ty) = work.at(&signature.returns, at)? {
            if nominal.contains_dialect_observed(ty, work.session, work.site)? {
                return Ok(true);
            }
            work.next(&mut at)?;
        }
        Ok(false)
    }
}
