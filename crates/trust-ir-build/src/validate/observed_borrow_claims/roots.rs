// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl State<'_> {
    pub(super) fn shared_root<O: ExecutionObserver>(
        &mut self,
        address: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let result = self.trace(address, work);
        self.retire_walk(work);
        result.and_then(|answer| {
            work.admit(1, size_of::<bool>())?;
            Ok(answer)
        })
    }
    pub(super) fn trace<O: ExecutionObserver>(
        &mut self,
        address: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.push(&mut self.stack, address)?;
        loop {
            work.admit(1, size_of::<ValueId>())?;
            let Some(current) = self.stack.pop() else {
                return Ok(false);
            };
            if self.visited(current, work)? {
                continue;
            }
            let mut index = 0usize;
            loop {
                work.admit(1, size_of::<DefRow<'_>>())?;
                let Some((candidate, definition)) = self
                    .definitions
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?
                    .get(index)
                    .copied()
                else {
                    break;
                };
                if candidate == current && self.follow(definition, work)? {
                    return Ok(true);
                }
                work.next(&mut index)?;
            }
        }
    }
    fn visited<O: ExecutionObserver>(
        &mut self,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<ValueId>())?;
            let Some(candidate) = self.seen.get(index) else {
                break;
            };
            if *candidate == value {
                return Ok(true);
            }
            work.next(&mut index)?;
        }
        work.push(&mut self.seen, value)?;
        Ok(false)
    }
    fn follow<O: ExecutionObserver>(
        &mut self,
        definition: Definition<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(67, 2 * size_of::<ValueId>())?;
        match definition {
            Definition::Node(Inst::Borrow { .. }) => return Ok(true),
            Definition::Node(Inst::GEP { base, .. }) => work.push(&mut self.stack, *base)?,
            Definition::Node(Inst::Copy { operand, .. })
            | Definition::Node(Inst::Cast {
                op: CastOp::PtrToPtr,
                operand,
                ..
            }) => work.push(&mut self.stack, *operand)?,
            Definition::Node(Inst::Select {
                then_val, else_val, ..
            }) => {
                work.push(&mut self.stack, *then_val)?;
                work.push(&mut self.stack, *else_val)?;
            }
            Definition::Parameter { block, index } => self.parameter_roots(block, index, work)?,
            Definition::Node(_) => {}
        }
        Ok(false)
    }
    fn parameter_roots<O: ExecutionObserver>(
        &mut self,
        block: u32,
        parameter: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        loop {
            work.admit(2, size_of::<Incoming>())?;
            let Some(&(target, ordinal, value)) = self
                .incoming
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?
                .get(index)
            else {
                return Ok(());
            };
            if target == block && ordinal == parameter {
                work.push(&mut self.stack, value)?;
            }
            work.next(&mut index)?;
        }
    }
}
