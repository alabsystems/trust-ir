// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_, '_> {
    pub(super) fn roots_at_local_alloca<O: ExecutionObserver>(
        &mut self,
        address: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(3, 0)?;
        if self.stack.capacity() != 0 || self.seen.capacity() != 0 || self.roots.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        let result = self.trace(address, work);
        self.retire_trace(work);
        result.and_then(|answer| {
            // A refusal during retirement must not escape as a semantic bool.
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
                break;
            };
            if self.was_seen(current, work)? {
                // Preserve the original global seen set, even for converging
                // transparent paths: a repeat contributes an UNKNOWN root.
                work.push(&mut self.roots, None)?;
                continue;
            }
            work.push(&mut self.seen, current)?;
            let mut found = false;
            let mut index = 0usize;
            loop {
                work.admit(4, size_of::<DefRow<'_>>())?;
                let Some(&(candidate, definition)) = self.definitions.get(index) else {
                    break;
                };
                if candidate == current {
                    found = true;
                    match definition {
                        Definition::Node(Inst::GEP { base, .. }) => {
                            work.push(&mut self.stack, *base)?;
                        }
                        Definition::Node(Inst::Copy { operand, .. })
                        | Definition::Node(Inst::Cast {
                            op: CastOp::PtrToPtr,
                            operand,
                            ..
                        }) => {
                            work.push(&mut self.stack, *operand)?;
                        }
                        Definition::Parameter { block, index } => {
                            work.push(
                                &mut self.roots,
                                Some(Definition::Parameter { block, index }),
                            )?;
                        }
                        other => work.push(&mut self.roots, Some(other))?,
                    }
                }
                work.next(&mut index)?;
            }
            if !found {
                work.push(&mut self.roots, None)?;
            }
        }
        let mut index = 0usize;
        loop {
            work.admit(2, size_of::<Option<Definition<'_>>>())?;
            let Some(root) = self.roots.get(index) else {
                return Ok(index != 0);
            };
            if !matches!(root, Some(Definition::Node(Inst::Alloca { .. }))) {
                return Ok(false);
            }
            work.next(&mut index)?;
        }
    }
    fn was_seen<O: ExecutionObserver>(
        &self,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut index = 0usize;
        loop {
            work.admit(2, size_of::<ValueId>())?;
            let Some(candidate) = self.seen.get(index) else {
                return Ok(false);
            };
            if *candidate == value {
                return Ok(true);
            }
            work.next(&mut index)?;
        }
    }
}
