// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use trust_ir::InstrNode;

#[derive(Clone, Copy)]
pub(super) enum Definition<'a> {
    Value(Inferred<'a>),
    Borrow(ValueId),
}

fn has_result<O: ExecutionObserver>(
    node: &InstrNode,
    value: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, size_of::<usize>())?;
    let mut index = 0usize;
    loop {
        work.admit(1, size_of::<ValueId>())?;
        let Some(candidate) = node.results.get(index) else {
            return Ok(false);
        };
        if *candidate == value {
            return Ok(true);
        }
        work.admit(1, size_of::<usize>())?;
        index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
}

fn parameters<'a, O: ExecutionObserver>(
    block: &'a trust_ir::Block,
    value: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<Definition<'a>>> {
    work.admit(1, size_of::<usize>())?;
    let mut index = 0usize;
    loop {
        work.admit(1, size_of::<ValueId>() + size_of::<&Ty>())?;
        let Some((candidate, ty)) = block.params.get(index) else {
            return Ok(None);
        };
        if *candidate == value {
            return Ok(Some(Definition::Value(Inferred::Borrowed(ty))));
        }
        work.admit(1, size_of::<usize>())?;
        index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
}

fn body<'a, O: ExecutionObserver>(
    block: &'a trust_ir::Block,
    value: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<Definition<'a>>> {
    work.admit(1, size_of::<usize>())?;
    let mut index = 0usize;
    loop {
        work.admit(1, size_of::<&InstrNode>())?;
        let Some(node) = block.body.get(index) else {
            return Ok(None);
        };
        if has_result(node, value, work)? {
            work.admit(2, size_of::<Option<Definition<'_>>>())?;
            if let Inst::Borrow { ptr } | Inst::BorrowMut { ptr } = &node.inst {
                return Ok(Some(Definition::Borrow(*ptr)));
            }
            if let Some(inferred) = inference::for_instruction(&node.inst, work)? {
                return Ok(Some(Definition::Value(inferred)));
            }
        }
        work.admit(1, size_of::<usize>())?;
        index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
}

pub(super) fn definition<'a, O: ExecutionObserver>(
    function: &'a Function,
    value: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<Definition<'a>>> {
    work.admit(1, size_of::<usize>())?;
    let mut index = 0usize;
    loop {
        work.admit(1, size_of::<&trust_ir::Block>())?;
        let Some(block) = function.blocks.get(index) else {
            return Ok(None);
        };
        if let Some(found) = parameters(block, value, work)? {
            return Ok(Some(found));
        }
        if let Some(found) = body(block, value, work)? {
            return Ok(Some(found));
        }
        work.admit(1, size_of::<usize>())?;
        index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
}

pub(super) fn borrow_operand<O: ExecutionObserver>(
    function: &Function,
    value: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<ValueId>> {
    work.admit(1, size_of::<Option<ValueId>>())?;
    Ok(match definition(function, value, work)? {
        Some(Definition::Borrow(operand)) => Some(operand),
        _ => None,
    })
}

pub(super) fn borrow_count<O: ExecutionObserver>(
    function: &Function,
    work: &mut Work<'_, '_, O>,
) -> R<usize> {
    work.admit(1, 3 * size_of::<usize>())?;
    let (mut count, mut block_index) = (0usize, 0usize);
    loop {
        work.admit(1, size_of::<&trust_ir::Block>())?;
        let Some(block) = function.blocks.get(block_index) else {
            return Ok(count);
        };
        let mut node_index = 0usize;
        loop {
            work.admit(2, size_of::<&InstrNode>() + size_of::<usize>())?;
            let Some(node) = block.body.get(node_index) else {
                break;
            };
            if matches!(node.inst, Inst::Borrow { .. } | Inst::BorrowMut { .. }) {
                count = count
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            node_index = node_index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        work.admit(1, size_of::<usize>())?;
        block_index = block_index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
}
