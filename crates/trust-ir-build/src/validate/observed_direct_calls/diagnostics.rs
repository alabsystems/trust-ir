// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    fn fields_ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, 0)?;
        if self.name.capacity() != 0
            || self.expected.capacity() != 0
            || self.actual.capacity() != 0
            || self.caller.is_some()
            || self.callee.is_some()
        {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    pub(super) fn count<O: ExecutionObserver>(
        &mut self,
        caller: &Function,
        callee: &Function,
        block: BlockId,
        expected: usize,
        actual: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.fields_ready(work)?;
        work.text(&callee.name, &mut self.name)?;
        producer::render(&caller.producer, &mut self.caller, work)?;
        producer::render(&callee.producer, &mut self.callee, work)?;
        work.reserve(&mut self.errors)?;
        work.admit(
            1,
            size_of::<ValidationError>() + size_of::<String>() + 2 * size_of::<Option<String>>(),
        )?;
        self.errors.push(ValidationError::CallArgCountMismatch {
            block: block.index(),
            callee: take(&mut self.name),
            expected,
            actual,
            caller_producer: self.caller.take(),
            callee_producer: self.callee.take(),
        });
        Ok(())
    }
    pub(super) fn types<O: ExecutionObserver>(
        &mut self,
        caller: &Function,
        callee: &Function,
        block: BlockId,
        index: usize,
        expected: &Ty,
        actual: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.fields_ready(work)?;
        work.text(&callee.name, &mut self.name)?;
        self.expected = expected.display_observed(work.session, work.site)?;
        self.actual = actual.display_observed(work.session, work.site)?;
        producer::render(&caller.producer, &mut self.caller, work)?;
        producer::render(&callee.producer, &mut self.callee, work)?;
        work.reserve(&mut self.errors)?;
        work.admit(
            1,
            size_of::<ValidationError>()
                + 3 * size_of::<String>()
                + 2 * size_of::<Option<String>>(),
        )?;
        self.errors.push(ValidationError::CallArgTypeMismatch {
            block: block.index(),
            callee: take(&mut self.name),
            arg_index: index,
            expected: take(&mut self.expected),
            actual: take(&mut self.actual),
            caller_producer: self.caller.take(),
            callee_producer: self.callee.take(),
        });
        Ok(())
    }
}
