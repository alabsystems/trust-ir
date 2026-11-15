// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl<'f> State<'f> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        module: Option<&Module>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<ObservedValueTypes>>())?;
        self.values = Some(match module {
            Some(module) => {
                build_module_value_types_observed(function, module, work.session, work.site)?
            }
            None => build_function_value_types_observed(function, work.session, work.site)?,
        });
        work.admit(1, size_of::<usize>())?;
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<&trust_ir::Block>())?;
            let Some(block) = function.blocks.get(index) else {
                return Ok(());
            };
            work.admit(1, size_of::<Option<&trust_ir::InstrNode>>())?;
            if let Some(term) = block.terminator() {
                work.admit(1, size_of::<Vec<Edge<'_>>>())?;
                self.edges = term
                    .inst
                    .successor_edges_observed(work.session, work.site)?;
                self.check_edges(
                    function,
                    block.id.index(),
                    matches!(term.inst, Inst::Switch { .. }),
                    work,
                )?;
                self.retire_edges(work);
            }
            work.admit(1, size_of::<usize>())?;
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
    fn check_edges<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: u32,
        default_first: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        let mut position = 0usize;
        loop {
            work.admit(1, size_of::<Edge<'_>>() + size_of::<usize>())?;
            if position >= self.edges.len() {
                return Ok(());
            }
            let index = if default_first {
                if position == 0 {
                    self.edges.len() - 1
                } else {
                    position - 1
                }
            } else {
                position
            };
            let edge = self
                .edges
                .get(index)
                .copied()
                .ok_or(ObservedValueError::InvalidRange)?;
            self.check_edge(function, block, edge, work)?;
            work.admit(1, size_of::<usize>())?;
            position = position
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
    fn check_edge<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: u32,
        edge: Edge<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let target = edge.target.index();
        let Some(params) = target_params(function, target, work)? else {
            return Ok(());
        };
        let count = match edge.kind {
            EdgeKind::Normal => edge.args.len(),
            EdgeKind::Unwind => 0,
        };
        self.diagnostics
            .count(block, target, params.len(), count, work)?;
        if edge.kind == EdgeKind::Unwind {
            return Ok(());
        }
        work.admit(1, size_of::<usize>())?;
        let mut arg_index = 0usize;
        loop {
            work.admit(1, size_of::<ValueId>() + 2 * size_of::<&Ty>())?;
            let (Some(arg), Some((_, expected))) =
                (edge.args.get(arg_index), params.get(arg_index))
            else {
                return Ok(());
            };
            let values = self
                .values
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?;
            if let Some(actual) = values.get_observed(*arg, work.session, work.site)? {
                let equal = actual.structural_eq_observed(expected, work.session, work.site)?;
                work.admit(1, 0)?;
                if !equal
                    && !(matches!(actual, Ty::Refine(..)) || matches!(expected, Ty::Refine(..)))
                {
                    self.diagnostics
                        .mismatch(block, target, arg_index, expected, actual, work)?;
                }
            }
            work.admit(1, size_of::<usize>())?;
            arg_index = arg_index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
}
pub(super) fn target_params<'a, O: ExecutionObserver>(
    function: &'a Function,
    target: u32,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'a [(ValueId, Ty)]>> {
    work.admit(1, size_of::<usize>())?;
    let mut index = function.blocks.len();
    loop {
        work.admit(1, size_of::<usize>())?;
        if index == 0 {
            return Ok(None);
        }
        index -= 1;
        work.admit(1, size_of::<u32>() + size_of::<&[(ValueId, Ty)]>())?;
        let block = function
            .blocks
            .get(index)
            .ok_or(ObservedValueError::InvalidRange)?;
        if block.id.index() == target {
            return Ok(Some(&block.params));
        }
    }
}
