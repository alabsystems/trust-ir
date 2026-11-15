// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn build<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.constants(function, work)?;
        loop {
            work.admit(1, size_of::<bool>())?;
            let mut changed = false;
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                work.admit(1, size_of::<bool>())?;
                if block.id != function.entry {
                    let mut p = 0;
                    while let Some((parameter, ty)) = work.at(&block.params, p)? {
                        work.admit(1, size_of::<&Ty>())?;
                        if matches!(ty, Ty::Closure(_))
                            && work.read(&self.targets, parameter.index())?.is_none()
                            && let Some(target) = self.block_parameter(function, block, p, work)?
                        {
                            work.insert(&mut self.targets, parameter.index(), target)?;
                            work.admit(1, size_of::<bool>())?;
                            changed = true;
                        }
                        work.next(&mut p)?;
                    }
                }
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    work.admit(
                        2,
                        size_of::<&Inst>() + size_of::<Option<ClosureTargetSources>>(),
                    )?;
                    if let Some(sources) = super::super::closure_target_sources(&node.inst)
                        && let Some(result) = work.at(&node.results, 0)?
                        && work.read(&self.targets, result.index())?.is_none()
                    {
                        let target = match sources {
                            ClosureTargetSources::Single(operand) => {
                                work.read(&self.targets, operand.index())?
                            }
                            ClosureTargetSources::Agree(left, right) => {
                                let left = work.read(&self.targets, left.index())?;
                                let right = work.read(&self.targets, right.index())?;
                                work.admit(2, size_of::<Option<FuncId>>())?;
                                left.filter(|target| right == Some(*target))
                            }
                        };
                        if let Some(target) = target {
                            work.insert(&mut self.targets, result.index(), target)?;
                            work.admit(1, size_of::<bool>())?;
                            changed = true;
                        }
                    }
                    work.next(&mut n)?;
                }
                work.next(&mut b)?;
            }
            work.admit(1, size_of::<bool>())?;
            if !changed {
                return Ok(());
            }
        }
    }

    fn block_parameter<O: ExecutionObserver>(
        &self,
        function: &Function,
        block: &trust_ir::Block,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<FuncId>> {
        work.admit(1, size_of::<Option<FuncId>>())?;
        let mut agreed = None;
        let mut p = 0;
        while let Some(predecessor) = work.at(&function.blocks, p)? {
            work.admit(1, size_of::<Option<&trust_ir::InstrNode>>())?;
            if let Some(terminator) = predecessor.terminator() {
                let mut edges = terminator
                    .inst
                    .successor_edges_observed(work.session, work.site)?;
                // Retire the actual borrowed-header buffer even when an edge
                // read refuses. No caller stop can leak a partial result.
                let result: R<bool> = (|| {
                    let mut e = 0;
                    while let Some(edge) = work.at(&edges, e)? {
                        work.admit(1, size_of::<bool>())?;
                        if edge.target == block.id {
                            work.admit(1, size_of::<bool>())?;
                            if edge.args.len() != block.params.len() {
                                return Ok(false);
                            }
                            let Some(argument) = work.at(edge.args, index)? else {
                                return Ok(false);
                            };
                            let Some(target) = work.read(&self.targets, argument.index())? else {
                                return Ok(false);
                            };
                            work.admit(2, size_of::<Option<FuncId>>())?;
                            if agreed.is_some_and(|previous| previous != target) {
                                return Ok(false);
                            }
                            agreed = Some(target);
                        }
                        work.next(&mut e)?;
                    }
                    Ok(true)
                })();
                while !edges.is_empty() {
                    work.step(1);
                    edges.pop();
                }
                work.poll();
                drop(edges);
                work.poll();
                if !result? {
                    return Ok(None);
                }
            }
            work.next(&mut p)?;
        }
        Ok(agreed)
    }
    fn constants<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut b = 0;
        while let Some(block) = work.at(&function.blocks, b)? {
            let mut n = 0;
            while let Some(node) = work.at(&block.body, n)? {
                work.admit(1, size_of::<&Inst>())?;
                if let Inst::Const {
                    ty: Ty::Closure(_),
                    value: Constant::Closure { func: target, .. },
                }
                | Inst::MakeClosure { func: target, .. } = &node.inst
                    && let Some(result) = work.at(&node.results, 0)?
                {
                    work.insert(&mut self.targets, result.index(), *target)?;
                }
                work.next(&mut n)?;
            }
            work.next(&mut b)?;
        }
        Ok(())
    }
}
