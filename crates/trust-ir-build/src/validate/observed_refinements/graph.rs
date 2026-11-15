// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::inst::BindingFrameDef;
use trust_ir::{Block, Edge};
#[derive(Default)]
pub(super) struct Flow<'a> {
    pub(super) values: Option<ObservedValueTypes>,
    pub(super) facts: Facts,
    pub(super) derived: Vec<(u32, Fact)>,
    pub(super) available: Vec<u32>,
    pub(super) visited_blocks: Vec<u32>,
    pub(super) incoming: Vec<(u32, &'a [ValueId])>,
    pub(super) reached: Vec<u32>,
    pub(super) order: Vec<u32>,
    pub(super) stack: Vec<(u32, bool)>,
    pub(super) edges: Vec<Edge<'a>>,
    pub(super) frames: Vec<(u32, &'a BindingFrameDef)>,
}
pub(super) fn contains<O: ExecutionObserver>(
    rows: &[u32],
    id: u32,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    for row in rows {
        work.admit(1, 0)?;
        if *row == id {
            return Ok(true);
        }
    }
    Ok(false)
}
pub(super) fn insert<O: ExecutionObserver>(
    rows: &mut Vec<u32>,
    id: u32,
    work: &mut Work<'_, '_, O>,
) -> R {
    if !contains(rows, id, work)? {
        work.push(rows, id)?
    }
    Ok(())
}
pub(super) fn find<T, O: ExecutionObserver>(
    rows: &[(u32, T)],
    id: u32,
    work: &mut Work<'_, '_, O>,
) -> R<Option<usize>> {
    for (i, (key, _)) in rows.iter().enumerate() {
        work.admit(1, 0)?;
        if *key == id {
            return Ok(Some(i));
        }
    }
    Ok(None)
}
pub(super) fn block<'a, O: ExecutionObserver>(
    function: &'a Function,
    id: u32,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'a Block>> {
    for block in function.blocks.iter().rev() {
        work.admit(1, 0)?;
        if block.id.index() == id {
            return Ok(Some(block));
        }
    }
    Ok(None)
}
impl<'a> Flow<'a> {
    pub(super) fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_vec(&mut self.frames);
        work.retire_vec(&mut self.edges);
        work.retire_vec(&mut self.stack);
        work.retire_vec(&mut self.order);
        work.retire_vec(&mut self.reached);
        work.retire_vec(&mut self.incoming);
        work.retire_vec(&mut self.available);
        work.retire_vec(&mut self.visited_blocks);
        while !self.derived.is_empty() {
            work.step(1);
            let _ = self.derived.pop();
        }
        work.retire_vec(&mut self.derived);
        self.facts.retire(work);
        work.step(1);
        if let Some(values) = self.values.take() {
            let _ = values.retire_observed(work.session, work.site);
        }
        work.session.retirement_poll(work.site);
    }
    pub(super) fn edges<O: ExecutionObserver>(
        &mut self,
        inst: &'a Inst,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if !self.edges.is_empty() {
            return Err(ObservedValueError::InvalidRange);
        }
        work.admit(1, size_of::<Vec<Edge<'a>>>())?;
        self.edges = inst.successor_edges_observed(work.session, work.site)?;
        if matches!(inst, Inst::Switch { .. }) && !self.edges.is_empty() {
            let mut i = self.edges.len() - 1;
            while i > 0 {
                work.admit(1, 2 * size_of::<Edge<'a>>())?;
                self.edges.swap(i, i - 1);
                i -= 1;
            }
        }
        Ok(())
    }
    pub(super) fn incoming<O: ExecutionObserver>(
        &mut self,
        function: &'a Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            for node in &block.body {
                work.admit(1, 0)?;
                self.edges(&node.inst, work)?;
                for edge in &self.edges {
                    work.admit(1, size_of::<Edge<'a>>())?;
                    if edge.kind == EdgeKind::Normal {
                        work.push(&mut self.incoming, (edge.target.index(), edge.args))?
                    }
                }
                work.retire_vec(&mut self.edges);
            }
        }
        Ok(())
    }
    pub(super) fn order<O: ExecutionObserver>(
        &mut self,
        function: &'a Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.push(&mut self.stack, (function.entry.index(), false))?;
        while let Some((id, emit)) = self.stack.last().copied() {
            work.admit(1, size_of::<(u32, bool)>())?;
            self.stack.pop();
            if emit {
                work.push(&mut self.order, id)?;
                continue;
            }
            if contains(&self.reached, id, work)? {
                continue;
            }
            insert(&mut self.reached, id, work)?;
            work.push(&mut self.stack, (id, true))?;
            let Some(block) = block(function, id, work)? else {
                continue;
            };
            for node in &block.body {
                work.admit(1, 0)?;
                self.edges(&node.inst, work)?;
                for edge in &self.edges {
                    work.admit(1, 0)?;
                    if !contains(&self.reached, edge.target.index(), work)? {
                        work.push(&mut self.stack, (edge.target.index(), false))?
                    }
                }
                work.retire_vec(&mut self.edges);
            }
        }
        let mut i = 0;
        while i < self.order.len() / 2 {
            work.admit(1, 2 * size_of::<u32>())?;
            let end = self.order.len() - 1 - i;
            self.order.swap(i, end);
            i += 1;
        }
        for block in &function.blocks {
            work.admit(1, 0)?;
            if !contains(&self.reached, block.id.index(), work)? {
                work.push(&mut self.order, block.id.index())?
            }
        }
        Ok(())
    }
    pub(super) fn frames<O: ExecutionObserver>(
        &mut self,
        function: &'a Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            for node in &block.body {
                work.admit(1, 0)?;
                if let Inst::OpenFrame { def } = &node.inst
                    && let Some(result) = work.at(&node.results, 0)?
                {
                    let id = result.index();
                    if let Some(i) = find(&self.frames, id, work)? {
                        work.admit(1, size_of::<(u32, &BindingFrameDef)>())?;
                        let old = replace(&mut self.frames[i].1, def);
                        work.step(size_of::<&BindingFrameDef>());
                        let _ = old;
                    } else {
                        work.push(&mut self.frames, (id, def))?;
                    }
                }
            }
        }
        loop {
            let mut changed = false;
            work.admit(1, size_of::<bool>())?;
            for block in &function.blocks {
                work.admit(1, 0)?;
                for node in &block.body {
                    work.admit(1, 0)?;
                    if let Inst::BindSlot { frame, .. } = &node.inst
                        && let Some(result) = work.at(&node.results, 0)?
                        && find(&self.frames, result.index(), work)?.is_none()
                        && let Some(i) = find(&self.frames, frame.index(), work)?
                    {
                        let def = self.frames[i].1;
                        work.push(&mut self.frames, (result.index(), def))?;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        Ok(())
    }
    pub(super) fn value<O: ExecutionObserver>(
        &self,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&Ty>> {
        self.values
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?
            .get_observed(value, work.session, work.site)
    }
    pub(super) fn fact<O: ExecutionObserver>(
        &self,
        id: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R<Fact> {
        Ok(find(&self.derived, id, work)?
            .map(|i| self.derived[i].1)
            .unwrap_or(Fact::Top))
    }
    pub(super) fn set<O: ExecutionObserver>(
        &mut self,
        id: u32,
        fact: Fact,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if let Some(i) = find(&self.derived, id, work)? {
            work.admit(1, size_of::<Fact>())?;
            let old = replace(&mut self.derived[i].1, fact);
            work.step(size_of::<Fact>());
            let _ = old;
        } else {
            work.push(&mut self.derived, (id, fact))?
        }
        Ok(())
    }
    pub(super) fn assumed<O: ExecutionObserver>(
        &self,
        module: &Module,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<Fact> {
        if !contains(&self.available, value.index(), work)? {
            return Ok(Fact::Top);
        }
        let d = facts::declared(module, self.value(value, work)?, work)?;
        self.facts
            .assumed(module, d, self.fact(value.index(), work)?, work)
    }
}
