// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    clippy::while_let_loop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Clone, Copy)]
enum Values<'a> {
    Many(&'a [ValueId]),
    One(ValueId),
}
impl Values<'_> {
    fn len(self) -> usize {
        match self {
            Self::Many(values) => values.len(),
            Self::One(_) => 1,
        }
    }
    fn at<O: ExecutionObserver>(self, at: usize, work: &mut Work<'_, '_, O>) -> R<Option<ValueId>> {
        work.admit(1, size_of::<Option<ValueId>>())?;
        Ok(match self {
            Self::Many(values) => values.get(at).copied(),
            Self::One(value) => (at == 0).then_some(value),
        })
    }
}
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        inst: &Inst,
        signature: &FuncTy,
        types: &ObservedValueTypes,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Values<'_>>())?;
        let values = match inst {
            Inst::Return { values } => Values::Many(values),
            Inst::CoroSuspend { value, .. } => Values::One(*value),
            _ => return Ok(()),
        };
        work.admit(2, 2 * size_of::<usize>() + size_of::<bool>())?;
        if values.len() != signature.returns.len() {
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::ReturnArityMismatch {
                block: block.index(),
                expected: signature.returns.len(),
                actual: values.len(),
            });
        }
        let mut at = 0;
        loop {
            let Some(value) = values.at(at, work)? else {
                break;
            };
            let Some(expected) = work.at(&signature.returns, at)? else {
                break;
            };
            if let Some(actual) = types.get_observed(value, work.session, work.site)?
                && !actual.structural_eq_observed(expected, work.session, work.site)?
            {
                work.admit(2, 2 * size_of::<bool>())?;
                if !(actual.is_refine() || expected.is_refine()) {
                    self.expected = expected.display_observed(work.session, work.site)?;
                    self.actual = actual.display_observed(work.session, work.site)?;
                    work.reserve(&mut self.errors)?;
                    work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
                    self.errors.push(ValidationError::ReturnTypeMismatch {
                        block: block.index(),
                        expected: take(&mut self.expected),
                        actual: take(&mut self.actual),
                    });
                }
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
}
