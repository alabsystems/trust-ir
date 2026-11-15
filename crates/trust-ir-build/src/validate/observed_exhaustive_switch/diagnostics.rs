// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(4, 0)?;
        if self.first.capacity() != 0
            || self.second.capacity() != 0
            || self.ty.capacity() != 0
            || self.reason.capacity() != 0
        {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    pub(super) fn commit<O: ExecutionObserver>(
        &mut self,
        block: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors
            .push(ValidationError::ExhaustiveSwitchDefaultReachable {
                block,
                reason: take(&mut self.reason),
            });
        Ok(())
    }
    pub(super) fn default_arguments<O: ExecutionObserver>(
        &mut self,
        block: u32,
        target: u32,
        count: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("the default edge to bb", &mut self.reason)?;
        work.number(u128::from(target), &mut self.reason)?;
        work.text(" passes ", &mut self.reason)?;
        work.number(count as u128, &mut self.reason)?;
        work.text(
            " argument(s); a dead default carries none",
            &mut self.reason,
        )?;
        self.commit(block, work)
    }
    pub(super) fn default_parameters<O: ExecutionObserver>(
        &mut self,
        block: u32,
        target: u32,
        count: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("the default block bb", &mut self.reason)?;
        work.number(u128::from(target), &mut self.reason)?;
        work.text(" has ", &mut self.reason)?;
        work.number(count as u128, &mut self.reason)?;
        work.text(" parameter(s); a dead default has none", &mut self.reason)?;
        self.commit(block, work)
    }
    pub(super) fn default_body<O: ExecutionObserver>(
        &mut self,
        block: u32,
        target: u32,
        count: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("the default block bb", &mut self.reason)?;
        work.number(u128::from(target), &mut self.reason)?;
        work.text(" is not exactly [unreachable] (", &mut self.reason)?;
        work.number(count as u128, &mut self.reason)?;
        work.text(" instruction(s))", &mut self.reason)?;
        self.commit(block, work)
    }
}
