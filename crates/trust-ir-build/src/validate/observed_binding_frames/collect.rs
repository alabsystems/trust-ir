// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

impl<'a> State<'a> {
    pub(super) fn collect<O: ExecutionObserver>(
        &mut self,
        function: &'a Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut bi = 0;
        loop {
            work.admit(1, 0)?;
            let Some(block) = function.blocks.get(bi) else {
                return Ok(());
            };
            let mut ni = 0;
            loop {
                work.admit(1, 0)?;
                let Some(node) = block.body.get(ni) else {
                    break;
                };
                if let Inst::OpenFrame { def } = &node.inst {
                    work.admit(1, size_of::<u32>() + size_of::<&[BindingSlot]>())?;
                    let frame = def.id.index();
                    let _arity = u32::try_from(def.slots.len())
                        .map_err(|_| ObservedValueError::CapacityOverflow)?;
                    if work.get(&self.declarations, frame)?.is_some() {
                        self.fixed(
                            || ValidationError::BindingFrameIdReused {
                                block: block.id.index(),
                                frame_id: frame,
                            },
                            work,
                        )?;
                    } else {
                        // Original first declaration wins. The old slot clones
                        // carried no checks; retain their exact borrowed types.
                        work.set(&mut self.declarations, frame, def.slots.as_slice())?;
                    }
                }
                ni = ni
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            bi = bi
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }

    pub(super) fn propagate<O: ExecutionObserver>(
        &mut self,
        function: &'a Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.flow.initialize(function, &self.declarations, work)?;
        self.flow.solve(function, &self.declarations, work)
    }

    pub(super) fn count_opens<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut bi = 0;
        loop {
            work.admit(1, 0)?;
            let Some(block) = function.blocks.get(bi) else {
                return Ok(());
            };
            let mut ni = 0;
            loop {
                work.admit(1, 0)?;
                let Some(node) = block.body.get(ni) else {
                    break;
                };
                if let Inst::OpenFrame { def } = &node.inst {
                    work.increment(&mut self.opens, def.id.index())?;
                }
                ni = ni
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            bi = bi
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
}
