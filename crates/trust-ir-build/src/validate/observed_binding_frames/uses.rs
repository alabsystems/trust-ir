// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) enum Access {
    Write,
    Read,
}
impl<'a> State<'a> {
    pub(super) fn uses<O: ExecutionObserver>(
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
            self.flow.prepare_block(bi, work)?;
            work.admit(1, 0)?;
            let mut ni = 0;
            loop {
                work.admit(67, 0)?;
                let Some(node) = block.body.get(ni) else {
                    break;
                };
                match &node.inst {
                    Inst::BindSlot { frame, slot, value } => {
                        self.bind(function, block.id.index(), *frame, *slot, *value, work)?
                    }
                    Inst::LoadSlot { frame, slot, ty } => {
                        self.load(block.id.index(), *frame, *slot, ty, work)?
                    }
                    Inst::CloseFrame { frame } => self.close(block.id.index(), *frame, work)?,
                    // The original rule observes only binding operations. In
                    // particular Borrow and ordinary pointer copies do not
                    // gain frame-handle propagation or lifetime semantics.
                    Inst::OpenFrame { .. }
                    | Inst::BinOp { .. }
                    | Inst::SeqMapAddK { .. }
                    | Inst::SeqMapNot { .. }
                    | Inst::SeqMap { .. }
                    | Inst::UnOp { .. }
                    | Inst::Overflow { .. }
                    | Inst::ICmp { .. }
                    | Inst::FCmp { .. }
                    | Inst::Cast { .. }
                    | Inst::Load { .. }
                    | Inst::Store { .. }
                    | Inst::Alloca { .. }
                    | Inst::HeapAlloc { .. }
                    | Inst::GEP { .. }
                    | Inst::PtrData { .. }
                    | Inst::PtrMetadata { .. }
                    | Inst::PtrFromParts { .. }
                    | Inst::AtomicLoad { .. }
                    | Inst::AtomicStore { .. }
                    | Inst::AtomicRMW { .. }
                    | Inst::CmpXchg { .. }
                    | Inst::Fence { .. }
                    | Inst::Br { .. }
                    | Inst::CondBr { .. }
                    | Inst::Switch { .. }
                    | Inst::Call { .. }
                    | Inst::CallIndirect { .. }
                    | Inst::CallCannotUnwind { .. }
                    | Inst::CallIndirectCannotUnwind { .. }
                    | Inst::Return { .. }
                    | Inst::Drop { .. }
                    | Inst::DropInvoke { .. }
                    | Inst::MakeAggregate { .. }
                    | Inst::MakeClosure { .. }
                    | Inst::BoxDeref { .. }
                    | Inst::ArraySplat { .. }
                    | Inst::TensorContract { .. }
                    | Inst::TensorMap { .. }
                    | Inst::TensorReduce { .. }
                    | Inst::TensorView { .. }
                    | Inst::TensorGather { .. }
                    | Inst::TensorScatter { .. }
                    | Inst::ExtractField { .. }
                    | Inst::InsertField { .. }
                    | Inst::ExtractElement { .. }
                    | Inst::InsertElement { .. }
                    | Inst::Const { .. }
                    | Inst::NullPtr
                    | Inst::GlobalAddr { .. }
                    | Inst::Undef { .. }
                    | Inst::Copy { .. }
                    | Inst::Select { .. }
                    | Inst::Assume { .. }
                    | Inst::Assert { .. }
                    | Inst::AssertInvoke { .. }
                    | Inst::Unreachable
                    | Inst::Borrow { .. }
                    | Inst::BorrowMut { .. }
                    | Inst::EndBorrow { .. }
                    | Inst::Retain { .. }
                    | Inst::Release { .. }
                    | Inst::IsUnique { .. }
                    | Inst::Dealloc { .. }
                    | Inst::MemCopy { .. }
                    | Inst::MemSet { .. }
                    | Inst::CoroSuspend { .. }
                    | Inst::Invoke { .. }
                    | Inst::InvokeIndirect { .. }
                    | Inst::LandingPad { .. }
                    | Inst::Resume { .. }
                    | Inst::DialectOp(_) => {}
                }
                self.flow.step(node, &self.declarations, work)?;
                ni = ni
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            bi = bi
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }

    fn before_use<O: ExecutionObserver>(
        &mut self,
        block: u32,
        value: ValueId,
        closing: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<usize>> {
        let index = self.flow.index(value, work)?;
        let flags = match index {
            Some(index) => self.flow.flags(index, work)?,
            None => flow::NON_FRAME,
        };
        if flags & flow::DEAD != 0 {
            self.fixed(
                || ValidationError::BindingUseAfterClose {
                    block,
                    frame_value: value.index(),
                },
                work,
            )?;
        }
        if flags & flow::NON_FRAME != 0 || flags & (flow::LIVE | flow::DEAD) == 0 {
            self.fixed(
                || {
                    if closing {
                        ValidationError::BindingFrameUnopened {
                            block,
                            frame_value: value.index(),
                        }
                    } else {
                        ValidationError::BindingFrameNotOpen {
                            block,
                            frame_value: value.index(),
                        }
                    }
                },
                work,
            )?;
        }
        Ok(index)
    }

    fn bind<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: u32,
        frame: ValueId,
        slot: u32,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(index) = self.before_use(block, frame, false, work)? else {
            return Ok(());
        };
        for di in 0..self.declarations.len() {
            if !self.flow.origin(index, di, work)? {
                continue;
            }
            work.admit(1, size_of::<(u32, &[BindingSlot])>())?;
            let (frame_id, slots) = self.declarations[di];
            let arity =
                u32::try_from(slots.len()).map_err(|_| ObservedValueError::CapacityOverflow)?;
            if slot >= arity {
                self.fixed(
                    || ValidationError::BindingSlotOutOfRange {
                        block,
                        frame_id,
                        slot,
                        arity,
                    },
                    work,
                )?;
                continue;
            }
            work.admit(1, size_of::<&Ty>())?;
            let expected = &slots[slot as usize].ty;
            work.admit(1, size_of::<Option<Ty>>())?;
            if self.actual_type.is_some() {
                return Err(ObservedValueError::InvalidRange);
            }
            self.actual_type =
                function_value_type_observed(function, value, work.session, work.site)?;
            if let Some(actual) = &self.actual_type {
                let equal = actual.structural_eq_observed(expected, work.session, work.site)?;
                work.admit(2, 0)?;
                if !equal
                    && !(matches!(actual, Ty::Refine(..)) || matches!(expected, Ty::Refine(..)))
                {
                    Self::text_ready(&self.expected, &self.actual, work)?;
                    work.admit(1, size_of::<String>())?;
                    self.expected = expected.display_observed(work.session, work.site)?;
                    work.admit(1, size_of::<String>())?;
                    self.actual = actual.display_observed(work.session, work.site)?;
                    self.type_error(Access::Write, block, frame_id, slot, work)?;
                }
            }
            work.retire_type(&mut self.actual_type);
            work.admit(1, 0)?;
        }
        Ok(())
    }

    fn load<O: ExecutionObserver>(
        &mut self,
        block: u32,
        frame: ValueId,
        slot: u32,
        actual: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(index) = self.before_use(block, frame, false, work)? else {
            return Ok(());
        };
        for di in 0..self.declarations.len() {
            if !self.flow.origin(index, di, work)? {
                continue;
            }
            work.admit(1, size_of::<(u32, &[BindingSlot])>())?;
            let (frame_id, slots) = self.declarations[di];
            let arity =
                u32::try_from(slots.len()).map_err(|_| ObservedValueError::CapacityOverflow)?;
            if slot >= arity {
                self.fixed(
                    || ValidationError::BindingSlotOutOfRange {
                        block,
                        frame_id,
                        slot,
                        arity,
                    },
                    work,
                )?;
                continue;
            }
            work.admit(1, size_of::<&Ty>())?;
            let expected = &slots[slot as usize].ty;
            let equal = actual.structural_eq_observed(expected, work.session, work.site)?;
            work.admit(2, 0)?;
            if !equal && !(matches!(expected, Ty::Refine(..)) || matches!(actual, Ty::Refine(..))) {
                Self::text_ready(&self.expected, &self.actual, work)?;
                work.admit(1, size_of::<String>())?;
                self.expected = expected.display_observed(work.session, work.site)?;
                work.admit(1, size_of::<String>())?;
                self.actual = actual.display_observed(work.session, work.site)?;
                self.type_error(Access::Read, block, frame_id, slot, work)?;
            }
        }
        Ok(())
    }

    pub(super) fn text_ready<O: ExecutionObserver>(
        expected: &String,
        actual: &String,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, 0)?;
        if expected.capacity() != 0 || actual.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }

    pub(super) fn type_error<O: ExecutionObserver>(
        &mut self,
        access: Access,
        block: u32,
        frame_id: u32,
        slot: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(2, size_of::<ValidationError>())?;
        let expected = take(&mut self.expected);
        let actual = take(&mut self.actual);
        let error = match access {
            Access::Write => ValidationError::BindingBindTypeMismatch {
                block,
                frame_id,
                slot,
                expected,
                actual,
            },
            Access::Read => ValidationError::BindingSlotTypeMismatch {
                block,
                frame_id,
                slot,
                expected,
                actual,
            },
        };
        self.errors.push(error);
        Ok(())
    }

    fn close<O: ExecutionObserver>(
        &mut self,
        block: u32,
        frame: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(index) = self.before_use(block, frame, true, work)? else {
            return Ok(());
        };
        // A may-origin is enough to check its slot type, but not enough to
        // credit a syntactic close for every alternative declaration.
        let mut only_origin = None;
        let mut ambiguous = false;
        for di in 0..self.declarations.len() {
            if self.flow.origin(index, di, work)? {
                work.admit(1, size_of::<usize>())?;
                if only_origin.is_some() {
                    ambiguous = true;
                } else {
                    only_origin = Some(di);
                }
            }
        }
        if let Some(di) = only_origin.filter(|_| !ambiguous) {
            work.admit(1, size_of::<u32>())?;
            work.increment(&mut self.closes, self.declarations[di].0)?;
        }
        Ok(())
    }

    pub(super) fn unclosed<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        loop {
            work.admit(1, size_of::<(u32, u32)>())?;
            let Some(&(frame_id, _)) = self.opens.get(index) else {
                return Ok(());
            };
            if work.get(&self.closes, frame_id)?.unwrap_or(0) == 0 {
                let block = first_opening_block(function, frame_id, work)?;
                self.fixed(
                    || ValidationError::BindingFrameUnclosed { block, frame_id },
                    work,
                )?;
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
}

fn first_opening_block<O: ExecutionObserver>(
    function: &Function,
    frame: u32,
    work: &mut Work<'_, '_, O>,
) -> R<u32> {
    let mut bi = 0;
    loop {
        work.admit(1, 0)?;
        let Some(block) = function.blocks.get(bi) else {
            return Ok(0);
        };
        let mut ni = 0;
        loop {
            work.admit(1, 0)?;
            let Some(node) = block.body.get(ni) else {
                break;
            };
            if let Inst::OpenFrame { def } = &node.inst
                && def.id.index() == frame
            {
                return Ok(block.id.index());
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
