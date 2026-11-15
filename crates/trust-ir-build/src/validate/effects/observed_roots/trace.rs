// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Trace {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        body: &ObservedBody<'_>,
        address: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Step>())?;
        work.push(&mut self.stack, Step::Enter(address))?;
        loop {
            work.admit(1, size_of::<Option<Step>>())?;
            let Some(step) = self.stack.pop() else {
                return Ok(());
            };
            work.admit(2, size_of::<Step>() + size_of::<Root>())?;
            let current = match step {
                Step::Exit(value) => {
                    self.mark(value, Mark::Done, work)?;
                    continue;
                }
                Step::Enter(value) => value,
            };
            match self.mark_of(current, work)? {
                Some(Mark::OnPath) => {
                    self.root(Root::Untraceable, work)?;
                    continue;
                }
                Some(Mark::Done) => continue,
                None => {}
            }
            self.mark(current, Mark::OnPath, work)?;
            work.admit(1, size_of::<Step>())?;
            work.push(&mut self.stack, Step::Exit(current))?;
            self.definitions(body, current, work)?;
        }
    }
    fn mark_of<O: ExecutionObserver>(
        &self,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<Mark>> {
        let mut at = 0;
        while let Some((id, mark)) = work.at(&self.marks, at)? {
            work.admit(1, 2 * size_of::<ValueId>() + size_of::<Option<Mark>>())?;
            if *id == value {
                return Ok(Some(*mark));
            }
            work.next(&mut at)?;
        }
        Ok(None)
    }
    fn mark<O: ExecutionObserver>(
        &mut self,
        value: ValueId,
        mark: Mark,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some((id, _)) = work.at(&self.marks, at)? {
            work.admit(1, 2 * size_of::<ValueId>())?;
            if *id == value {
                work.admit(1, size_of::<Mark>())?;
                self.marks[at].1 = mark;
                return Ok(());
            }
            work.next(&mut at)?;
        }
        work.admit(1, size_of::<(ValueId, Mark)>())?;
        work.push(&mut self.marks, (value, mark))
    }
}
