// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact basic operand checks, one constituent of the original type pass.
use super::*;
use core::mem::{size_of, take};
use trust_ir::inst::Ordering;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod checks;
mod dispatch;
mod storage;
#[cfg(test)]
mod tests;
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
    Operand(u32),
    Pointer(u32),
    Index(u32),
    Condition(u32),
    Predicate(u32),
    Atomic {
        block: u32,
        op: &'static str,
        role: &'static str,
        legal: &'static str,
    },
}
#[derive(Clone, Copy)]
enum Refinement {
    Exact,
    Consumption,
}
#[derive(Clone, Copy)]
enum AtomicRole {
    Load,
    Store,
}

/// Run exactly the original basic checks for load/store, boolean control,
/// assert-message operands, bulk memory, GEP, atomics, Copy, borrow/ARC and
/// coroutine frame operands. The complete original inferred map is borrowed.
/// This excludes vector well-formedness, result inference, numeric/cast/fat-
/// pointer/select/element checks and borrow-structure claims; their original
/// ordering remains the complete type-pass caller's obligation. Other variants
/// produce no diagnostics in THIS constituent, never a full validation result.
///
/// Actual lookups, equality, bounded text/storage and refusal cleanup use the
/// supplied original session/site. Unknown types and only the original checked
/// consumption positions retain their original exemption. No partial result
/// escapes refusal; successful output/input disposal remains caller-owned.
pub fn validate_instruction_basic_type_operands_observed<O: ExecutionObserver>(
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

impl State {
    fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(4, 0)?;
        if self.op.capacity() != 0
            || self.role.capacity() != 0
            || self.expected.capacity() != 0
            || self.actual.capacity() != 0
        {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn commit<O: ExecutionObserver>(&mut self, kind: Diagnostic, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        // Every fallible action precedes the retained owned moves below.
        let error = match kind {
            Diagnostic::Operand(block) => ValidationError::OperandTypeMismatch {
                block,
                op: take(&mut self.op),
                role: take(&mut self.role),
                expected: take(&mut self.expected),
                actual: take(&mut self.actual),
            },
            Diagnostic::Pointer(block) => ValidationError::OperandNotPointer {
                block,
                op: take(&mut self.op),
                ty: take(&mut self.actual),
            },
            Diagnostic::Index(block) => ValidationError::GepIndexNotInteger {
                block,
                ty: take(&mut self.actual),
            },
            Diagnostic::Condition(block) => ValidationError::CondBrRequiresBool {
                block,
                cond_ty: take(&mut self.actual),
            },
            Diagnostic::Predicate(block) => ValidationError::PredicateRequiresBool {
                block,
                op: take(&mut self.op),
                cond_ty: take(&mut self.actual),
            },
            Diagnostic::Atomic {
                block,
                op,
                role,
                legal,
            } => ValidationError::IllegalAtomicOrdering {
                block,
                op,
                role,
                ordering: take(&mut self.actual),
                legal,
            },
        };
        self.errors.push(error);
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.op));
        work.flat(take(&mut self.role));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
    }
    fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(error) = self.errors.pop() {
                match error {
                    ValidationError::OperandTypeMismatch {
                        op,
                        role,
                        expected,
                        actual,
                        ..
                    } => {
                        work.flat(op);
                        work.flat(role);
                        work.flat(expected);
                        work.flat(actual);
                    }
                    ValidationError::OperandNotPointer { op, ty, .. } => {
                        work.flat(op);
                        work.flat(ty);
                    }
                    ValidationError::PredicateRequiresBool { op, cond_ty, .. } => {
                        work.flat(op);
                        work.flat(cond_ty);
                    }
                    ValidationError::GepIndexNotInteger { ty, .. } => work.flat(ty),
                    ValidationError::CondBrRequiresBool { cond_ty, .. } => work.flat(cond_ty),
                    ValidationError::IllegalAtomicOrdering { ordering, .. } => work.flat(ordering),
                    // These are the only constructors in this private State.
                    other => work.flat(other),
                }
            }
        }
        work.flat(take(&mut self.errors));
    }
}
