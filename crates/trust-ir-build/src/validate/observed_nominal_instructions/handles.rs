// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn handles<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        node: &InstrNode,
        values: &ObservedValueTypes,
        nominal: &ObservedNominalTypeReachability<'_>,
        block: BlockId,
        index: usize,
        guards: Option<&ObservedHandleEnumGuards<'_>>,
        slots: Option<&ObservedSealedHandleSlots<'_>>,
        work: &mut Work<'_, '_, O>,
    ) -> R<Decision> {
        work.admit(1, size_of::<&Inst>())?;
        let yes = match &node.inst {
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
            | Inst::Br { .. } => true,
            Inst::CallIndirect { callee, sig, .. }
            | Inst::CallIndirectCannotUnwind { callee, sig, .. }
            | Inst::InvokeIndirect { callee, sig, .. } => {
                census::exact_function(module, *callee, *sig, values, work)?
            }
            Inst::CondBr { cond, .. } => census::exact(*cond, &Ty::Bool, values, work)?,
            Inst::Switch { value, .. } => {
                match values.get_observed(*value, work.session, work.site)? {
                    Some(ty) => !nominal.contains_handle_observed(ty, work.session, work.site)?,
                    None => false,
                }
            }
            Inst::MakeAggregate { .. } | Inst::ExtractField { .. } | Inst::InsertField { .. } => {
                return match handle_aggregate_lane_rule_observed(
                    module,
                    &node.inst,
                    values,
                    nominal,
                    block,
                    guards,
                    work.session,
                    work.site,
                )? {
                    Ok(()) => Ok(Decision::Allowed),
                    Err(reason) => {
                        self.detail = reason;
                        Ok(Decision::DetailedRefusal)
                    }
                };
            }
            Inst::Alloca { .. } | Inst::Load { .. } | Inst::Store { .. } => {
                return match handle_slot_rule_observed(
                    &node.inst,
                    &node.results,
                    values,
                    block,
                    index,
                    slots,
                    work.session,
                    work.site,
                )? {
                    Ok(()) => Ok(Decision::Allowed),
                    Err(reason) => {
                        self.detail = reason;
                        Ok(Decision::DetailedRefusal)
                    }
                };
            }
            _ => false,
        };
        Ok(if yes {
            Decision::Allowed
        } else {
            Decision::GenericRefusal
        })
    }
}
