// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn casts<O: ExecutionObserver>(
        &mut self,
        layouts: &trust_ir::LayoutTable<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut f = 0;
        while let Some(function) = work.at(&layouts.module().functions, f)? {
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    work.admit(32, size_of::<Option<CastOp>>())?;
                    if let Inst::Cast {
                        op, src_ty, dst_ty, ..
                    } = &node.inst
                        && op.is_layout_sensitive()
                    {
                        self.cast(layouts, block.id.index(), *op, src_ty, dst_ty, work)?;
                    }
                    work.next(&mut n)?;
                }
                work.next(&mut b)?;
            }
            work.next(&mut f)?;
        }
        Ok(())
    }
    fn cast<O: ExecutionObserver>(
        &mut self,
        layouts: &trust_ir::LayoutTable<'_>,
        block: u32,
        op: CastOp,
        src: &Ty,
        dst: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            1,
            size_of::<Option<Result<CastLayoutEvidence, LayoutError>>>(),
        )?;
        self.result = Some(layouts.layout_sensitive_cast_evidence_observed(
            op,
            src,
            dst,
            work.session,
            work.site,
        )?);
        if let Some(Err(error)) = &self.result {
            // All child-returned owning payloads are assigned directly into this State
            // before any next fallible admission; the full original error stays here
            // while its complete message and both type strings are built.
            work.admit(64, size_of::<String>() + 64)?;
            self.op = op.to_string();
            self.src = src.display_observed(work.session, work.site)?;
            self.dst = dst.display_observed(work.session, work.site)?;
            self.reason = error.display_observed(work.session, work.site)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>() + 4 * size_of::<String>())?;
            self.errors.push(ValidationError::CastLayoutUnsupported {
                block,
                op: take(&mut self.op),
                src: take(&mut self.src),
                dst: take(&mut self.dst),
                reason: take(&mut self.reason),
            });
        }
        self.retire_result(work);
        work.admit(1, 0)
    }
}
