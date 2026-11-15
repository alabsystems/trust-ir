// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn operand_and_width<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: CastOp,
        src: &Ty,
        dst: &Ty,
        operand: ValueId,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if let Some(actual) = values.get_observed(operand, work.session, work.site)?
            && !actual.structural_eq_observed(src, work.session, work.site)?
        {
            self.ready(work)?;
            let token = work.opcode(op)?;
            work.text(token, &mut self.op)?;
            work.spelling(src, &mut self.src)?;
            work.spelling(actual, &mut self.actual)?;
            self.commit(block, Diagnostic::Operand, work)?;
        }
        work.admit(17, 0)?;
        match op {
            CastOp::Trunc | CastOp::ZExt | CastOp::SExt => {
                let from = src.bit_width_observed(work.session, work.site)?;
                let to = dst.bit_width_observed(work.session, work.site)?;
                if let (Some(from), Some(to)) = (from, to) {
                    work.admit(3, 0)?;
                    let invalid = if op == CastOp::Trunc {
                        from <= to
                    } else {
                        from >= to
                    };
                    if invalid {
                        self.describe(op, src, dst, work)?;
                        let token = work.opcode(op)?;
                        work.text(token, &mut self.reason)?;
                        work.text(" requires src width (", &mut self.reason)?;
                        work.decimal(from, &mut self.reason)?;
                        work.text(
                            if op == CastOp::Trunc {
                                ") > dst width ("
                            } else {
                                ") < dst width ("
                            },
                            &mut self.reason,
                        )?;
                        work.decimal(to, &mut self.reason)?;
                        work.text(")", &mut self.reason)?;
                        self.commit(block, Diagnostic::Width, work)?;
                    }
                }
            }
            CastOp::FPTrunc
            | CastOp::FPExt
            | CastOp::FPToUI
            | CastOp::FPToSI
            | CastOp::UIToFP
            | CastOp::SIToFP
            | CastOp::PtrToInt
            | CastOp::IntToPtr
            | CastOp::PtrToPtr
            | CastOp::Bitcast
            | CastOp::Transmute
            | CastOp::ReifyFnPointer
            | CastOp::FPToSISat
            | CastOp::FPToUISat => {}
        }
        Ok(())
    }
}
