// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual arithmetic/comparison type checks, without vector surface checks.
use super::*;
use core::mem::{size_of, take};
use trust_ir::inst::OverflowOp;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod binary;
mod comparisons;
mod diagnostics;
mod dispatch;
mod storage;
#[cfg(test)]
mod tests;
mod tokens;
mod unary;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    op: String,
    role: String,
    expected: String,
    actual: String,
    errors: Vec<ValidationError>,
}
enum Diagnostic {
    Operands(u32),
    Operand(u32),
    Integer(u32),
    Float(u32),
    Bool(u32),
    OverflowInteger(u32),
    ICmp(u32),
    FCmp(u32),
    ScalarBoolNot(u32),
}
#[derive(Clone, Copy)]
enum Category {
    Integer,
    Bool,
    IntegerOrBool,
    Float,
}

/// Exact original BinOp/UnOp/ICmp/FCmp/Overflow operand and category rules,
/// borrowing the complete original inferred map. Vector well-formedness and
/// all other type-pass constituents remain the full caller's responsibility.
/// In particular standalone Refine suppression here presupposes the original
/// standalone refinement-surface refusal; this is never a complete validator.
///
/// Same original session/site owns actual lookups, one-hop Refine base
/// selection, structural equality, text/storage and failed output retirement.
/// Missing type/base exemptions remain semantic original behavior, not an
/// operational fallback. No partial accepting diagnostics escape a stop.
pub fn validate_instruction_numeric_type_operands_observed<O: ExecutionObserver>(
    block: u32,
    instruction: &Inst,
    values: &ObservedValueTypes,
    module: Option<&Module>,
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
    let result = state.check(block, instruction, values, module, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            state.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}
