// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn compatibility<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: CastOp,
        src: &Ty,
        dst: &Ty,
        mode: CastValidationMode,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(19, 0)?;
        if mode == CastValidationMode::DeferLayoutSensitive && op.is_layout_sensitive() {
            return Ok(());
        }
        if matches!(op, CastOp::Bitcast | CastOp::Transmute)
            && !src.structural_eq_observed(dst, work.session, work.site)?
            && (src.has_bool_lanes_observed(work.session, work.site)?
                || dst.has_bool_lanes_observed(work.session, work.site)?)
        {
            self.describe(op, src, dst, work)?;
            work.admit(82, 2 * size_of::<TyShape>())?;
            let from = src.shape();
            let to = dst.shape();
            work.shape(from, &mut self.reason)?;
            work.text(" -> ", &mut self.reason)?;
            work.shape(to, &mut self.reason)?;
            work.text(": a bool lane is one bit of value in one byte of storage, so no bit-image reinterpretation is defined for it (the reference interpreter and the Lean model both refuse it); spell int<->bool as trunc/zext and obtain a logical <N x bool> mask by comparing", &mut self.reason)?;
            return self.commit(block, Diagnostic::Layout, work);
        }
        let valid = if src.contains_handle_observed(work.session, work.site)?
            || dst.contains_handle_observed(work.session, work.site)?
        {
            false
        } else {
            compatible(op, src, dst, work)?
        };
        if !valid {
            self.describe(op, src, dst, work)?;
            self.commit(block, Diagnostic::Incompatible, work)?;
        }
        Ok(())
    }
}
fn integer<O: ExecutionObserver>(ty: &Ty, work: &mut Work<'_, '_, O>) -> R<bool> {
    work.admit(12, 0)?;
    Ok(ty.is_integer())
}
fn floating<O: ExecutionObserver>(ty: &Ty, work: &mut Work<'_, '_, O>) -> R<bool> {
    work.admit(3, 0)?;
    Ok(ty.is_float())
}
fn resize<O: ExecutionObserver>(ty: &Ty, work: &mut Work<'_, '_, O>) -> R<bool> {
    if integer(ty, work)? {
        return Ok(true);
    }
    work.admit(2, 0)?;
    Ok(matches!(ty, Ty::Bool | Ty::Char))
}
fn compatible<O: ExecutionObserver>(
    op: CastOp,
    src: &Ty,
    dst: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(17, 0)?;
    Ok(match op {
        CastOp::Trunc | CastOp::ZExt | CastOp::SExt => resize(src, work)? && resize(dst, work)?,
        CastOp::FPTrunc | CastOp::FPExt => floating(src, work)? && floating(dst, work)?,
        CastOp::FPToUI | CastOp::FPToSI | CastOp::FPToUISat | CastOp::FPToSISat => {
            floating(src, work)? && integer(dst, work)?
        }
        CastOp::UIToFP | CastOp::SIToFP => integer(src, work)? && floating(dst, work)?,
        CastOp::PtrToInt => {
            work.admit(1, 0)?;
            matches!(src, Ty::Ptr) && integer(dst, work)?
        }
        CastOp::IntToPtr => {
            let is_integer = integer(src, work)?;
            if is_integer {
                work.admit(1, 0)?;
                matches!(dst, Ty::Ptr)
            } else {
                false
            }
        }
        CastOp::PtrToPtr => pointer::relative(src, dst, work)?,
        CastOp::Bitcast => pointer::bitcast(src, dst, work)?,
        CastOp::ReifyFnPointer => {
            work.admit(1, 0)?;
            if matches!(src, Ty::Func(_)) {
                match pointer::layout(dst, work)? {
                    Some(layout) => {
                        work.admit(1, 0)?;
                        !layout.is_fat()
                    }
                    None => false,
                }
            } else {
                false
            }
        }
        CastOp::Transmute => false,
    })
}
