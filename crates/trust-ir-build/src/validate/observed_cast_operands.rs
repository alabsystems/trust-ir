// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! The original two cast operand/type checks under one supplied owner.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::shape::{PointerLayoutShape, TyShape};
mod compatibility;
mod operand;
mod pointer;
mod spelling;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    op: String,
    src: String,
    dst: String,
    actual: String,
    reason: String,
    errors: Vec<ValidationError>,
}
#[derive(Clone, Copy)]
enum Diagnostic {
    Incompatible,
    Layout,
    Operand,
    Width,
}

/// Exact `check_cast_compatibility` followed by `check_cast_operand_and_width`.
/// The existing mode defers only compatibility for layout-sensitive opcodes;
/// operand equality and integer width direction still execute afterward.
/// This is one constituent, never full function/module/source/proof validity.
/// Input and successful result disposal remain caller-owned.
pub(super) fn validate_cast_operands_observed<O: ExecutionObserver>(
    block: u32,
    op: CastOp,
    src: &Ty,
    dst: &Ty,
    operand: ValueId,
    values: &ObservedValueTypes,
    mode: super::CastValidationMode,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state
        .compatibility(block, op, src, dst, mode, &mut work)
        .and_then(|()| state.operand_and_width(block, op, src, dst, operand, values, &mut work));
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            // Generic consuming cleanup covers all nested payloads. Its unit
            // receipt is not diagnostic publication; any cleanup refusal is
            // latched in this original session and selected by terminal below.
            let _ = super::retire_validation_errors_observed(
                take(&mut state.errors),
                work.session,
                work.site,
            );
            Err(work.terminal(error))
        }
    }
}
impl State {
    fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(5, 0)?;
        if self.op.capacity() != 0
            || self.src.capacity() != 0
            || self.dst.capacity() != 0
            || self.actual.capacity() != 0
            || self.reason.capacity() != 0
        {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn describe<O: ExecutionObserver>(
        &mut self,
        op: CastOp,
        src: &Ty,
        dst: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        let token = work.opcode(op)?;
        work.text(token, &mut self.op)?;
        work.spelling(src, &mut self.src)?;
        work.spelling(dst, &mut self.dst)
    }
    fn commit<O: ExecutionObserver>(
        &mut self,
        block: u32,
        kind: Diagnostic,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(4, size_of::<ValidationError>())?;
        // No fallible work follows the retained field moves.
        let error = match kind {
            Diagnostic::Incompatible => ValidationError::CastIncompatible {
                block,
                op: take(&mut self.op),
                src: take(&mut self.src),
                dst: take(&mut self.dst),
            },
            Diagnostic::Layout => ValidationError::CastLayoutUnsupported {
                block,
                op: take(&mut self.op),
                src: take(&mut self.src),
                dst: take(&mut self.dst),
                reason: take(&mut self.reason),
            },
            Diagnostic::Operand => ValidationError::CastOperandTypeMismatch {
                block,
                op: take(&mut self.op),
                declared_src: take(&mut self.src),
                actual: take(&mut self.actual),
            },
            Diagnostic::Width => ValidationError::CastWidthDirectionInvalid {
                block,
                op: take(&mut self.op),
                src: take(&mut self.src),
                dst: take(&mut self.dst),
                reason: take(&mut self.reason),
            },
        };
        self.errors.push(error);
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.op));
        work.flat(take(&mut self.src));
        work.flat(take(&mut self.dst));
        work.flat(take(&mut self.actual));
        work.flat(take(&mut self.reason));
    }
}
