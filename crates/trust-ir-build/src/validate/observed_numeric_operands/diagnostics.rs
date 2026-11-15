// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
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
    pub(super) fn commit<O: ExecutionObserver>(
        &mut self,
        kind: Diagnostic,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        let error = match kind {
            Diagnostic::Operands(block) => ValidationError::BinOpTypeMismatch {
                block,
                op: take(&mut self.op),
                lhs_ty: take(&mut self.expected),
                rhs_ty: take(&mut self.actual),
            },
            Diagnostic::Operand(block) => ValidationError::OperandTypeMismatch {
                block,
                op: take(&mut self.op),
                role: take(&mut self.role),
                expected: take(&mut self.expected),
                actual: take(&mut self.actual),
            },
            Diagnostic::Integer(block) => ValidationError::BinOpRequiresInteger {
                block,
                op: take(&mut self.op),
                ty: take(&mut self.actual),
            },
            Diagnostic::Float(block) => ValidationError::BinOpRequiresFloat {
                block,
                op: take(&mut self.op),
                ty: take(&mut self.actual),
            },
            Diagnostic::Bool(block) => ValidationError::BinOpRequiresBool {
                block,
                op: take(&mut self.op),
                ty: take(&mut self.actual),
            },
            Diagnostic::OverflowInteger(block) => ValidationError::OperandNotInteger {
                block,
                op: take(&mut self.op),
                ty: take(&mut self.actual),
            },
            Diagnostic::ICmp(block) => ValidationError::ICmpRequiresIntegerOrPtr {
                block,
                ty: take(&mut self.actual),
            },
            Diagnostic::FCmp(block) => ValidationError::FCmpRequiresFloat {
                block,
                ty: take(&mut self.actual),
            },
            Diagnostic::ScalarBoolNot(block) => ValidationError::UnOpNotOnScalarBool { block },
        };
        self.errors.push(error);
        Ok(())
    }
    pub(super) fn mismatch<O: ExecutionObserver>(
        &mut self,
        kind: Diagnostic,
        op: &'static str,
        role: Option<&'static str>,
        expected: &Ty,
        actual: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text(op, &mut self.op)?;
        if let Some(role) = role {
            work.text(role, &mut self.role)?;
        }
        work.spelling(expected, &mut self.expected)?;
        work.spelling(actual, &mut self.actual)?;
        self.commit(kind, work)
    }
    pub(super) fn category_error<O: ExecutionObserver>(
        &mut self,
        kind: Diagnostic,
        op: Option<&'static str>,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        if let Some(op) = op {
            work.text(op, &mut self.op)?;
        }
        work.spelling(ty, &mut self.actual)?;
        self.commit(kind, work)
    }
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.op));
        work.flat(take(&mut self.role));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
    }
    pub(super) fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(error) = self.errors.pop() {
                match error {
                    ValidationError::BinOpTypeMismatch {
                        op, lhs_ty, rhs_ty, ..
                    } => {
                        work.flat(op);
                        work.flat(lhs_ty);
                        work.flat(rhs_ty);
                    }
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
                    ValidationError::BinOpRequiresInteger { op, ty, .. }
                    | ValidationError::BinOpRequiresFloat { op, ty, .. }
                    | ValidationError::BinOpRequiresBool { op, ty, .. }
                    | ValidationError::OperandNotInteger { op, ty, .. } => {
                        work.flat(op);
                        work.flat(ty);
                    }
                    ValidationError::ICmpRequiresIntegerOrPtr { ty, .. }
                    | ValidationError::FCmpRequiresFloat { ty, .. } => work.flat(ty),
                    // Only these nine private constructors are admitted here.
                    fixed => work.flat(fixed),
                }
            }
        }
        work.flat(take(&mut self.errors));
    }
}
