// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Finite, generation-sensitive may-alias dataflow over frame-relevant SSA values.
//! Origins describe slot signatures; they are deliberately NOT alias identities.
use super::*;

pub(super) const NON_FRAME: u8 = 1;
pub(super) const LIVE: u8 = 2;
pub(super) const DEAD: u8 = 4;

#[derive(Default)]
pub(super) struct Flow<'a> {
    handles: Vec<(u32, ())>,
    global: Vec<u8>,
    entries: Vec<u8>,
    reachable: Vec<u8>,
    current: Vec<u8>,
    snapshot: Vec<u8>,
    edge: Vec<u8>,
    mapping: Vec<usize>,
    edges: Vec<Edge<'a>>,
    handles_len: usize,
    declarations_len: usize,
    origins_offset: usize,
    aliases_offset: usize,
    stride: usize,
}

impl<'a> Flow<'a> {
    pub(super) fn initialize<O: ExecutionObserver>(
        &mut self,
        function: &'a Function,
        declarations: &[(u32, &'a [BindingSlot])],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Include both directions of normal parameter transport. Other pointer
        // operations do not gain frame provenance merely from their type.
        for block in &function.blocks {
            work.admit(1, 0)?;
            for node in &block.body {
                work.admit(1, 0)?;
                match &node.inst {
                    Inst::OpenFrame { .. } | Inst::BindSlot { .. } => {
                        for value in &node.results {
                            work.set(&mut self.handles, value.index(), ())?;
                        }
                    }
                    _ => {}
                }
                match &node.inst {
                    Inst::BindSlot { frame, .. }
                    | Inst::LoadSlot { frame, .. }
                    | Inst::CloseFrame { frame } => {
                        work.set(&mut self.handles, frame.index(), ())?;
                    }
                    _ => {}
                }
            }
        }
        if self.handles.is_empty() {
            work.resize(&mut self.reachable, function.blocks.len(), 0)?;
            return Ok(());
        }
        loop {
            work.admit(1, 0)?;
            let mut changed = false;
            for block in &function.blocks {
                work.admit(1, 0)?;
                let Some(last) = block.body.last() else {
                    continue;
                };
                self.edges = last
                    .inst
                    .successor_edges_observed(work.session, work.site)?;
                for ei in 0..self.edges.len() {
                    work.admit(1, size_of::<Edge<'_>>())?;
                    let edge = self.edges[ei];
                    let Some(target) = block_index(function, edge.target, work)? else {
                        continue;
                    };
                    for (argument, (parameter, _)) in
                        edge.args.iter().zip(&function.blocks[target].params)
                    {
                        work.admit(1, 2 * size_of::<ValueId>())?;
                        if work.get(&self.handles, argument.index())?.is_some()
                            || work.get(&self.handles, parameter.index())?.is_some()
                        {
                            changed |= work.set(&mut self.handles, argument.index(), ())?;
                            changed |= work.set(&mut self.handles, parameter.index(), ())?;
                        }
                    }
                }
                work.drain(&mut self.edges);
            }
            if !changed {
                break;
            }
        }
        self.handles_len = self.handles.len();
        self.declarations_len = declarations.len();
        self.origins_offset = self.handles_len;
        self.aliases_offset = self
            .origins_offset
            .checked_add(
                self.handles_len
                    .checked_mul(self.declarations_len)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )
            .ok_or(ObservedValueError::CapacityOverflow)?;
        self.stride = self
            .aliases_offset
            .checked_add(
                self.handles_len
                    .checked_mul(self.handles_len)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let entries_len = self
            .stride
            .checked_mul(function.blocks.len())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        work.resize(&mut self.global, self.stride, 0)?;
        work.resize(&mut self.entries, entries_len, 0)?;
        work.resize(&mut self.reachable, function.blocks.len(), 0)?;
        work.resize(&mut self.current, self.stride, 0)?;
        work.resize(&mut self.snapshot, self.stride, 0)?;
        work.resize(&mut self.edge, self.stride, 0)?;
        work.resize(&mut self.mapping, self.handles_len, self.handles_len)?;
        self.global_origins(function, declarations, work)?;
        Ok(())
    }

    pub(super) fn index<O: ExecutionObserver>(
        &self,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<usize>> {
        work.admit(1, size_of::<ValueId>())?;
        for (index, (candidate, _)) in self.handles.iter().enumerate() {
            work.admit(1, size_of::<u32>())?;
            if *candidate == value.index() {
                return Ok(Some(index));
            }
        }
        Ok(None)
    }

    fn origin_offset(&self, value: usize, declaration: usize) -> usize {
        // All products and sums were checked before allocating the flat state.
        self.origins_offset + value * self.declarations_len + declaration
    }

    fn alias_offset(&self, left: usize, right: usize) -> usize {
        self.aliases_offset + left * self.handles_len + right
    }

    fn global_copy<O: ExecutionObserver>(
        &mut self,
        source: usize,
        destination: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, 1)?;
        let bits = self.global[source];
        let mut changed = union(&mut self.global, destination, bits, work)?;
        for declaration in 0..self.declarations_len {
            let from = self.origin_offset(source, declaration);
            let to = self.origin_offset(destination, declaration);
            work.admit(1, 1)?;
            let bit = self.global[from];
            changed |= union(&mut self.global, to, bit, work)?;
        }
        Ok(changed)
    }

    fn global_origins<O: ExecutionObserver>(
        &mut self,
        function: &'a Function,
        declarations: &[(u32, &'a [BindingSlot])],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // This reachability-independent union is used only for structural
        // diagnostics in unreachable blocks. It never supplies live CFG facts.
        for block in &function.blocks {
            work.admit(1, 0)?;
            if block.id == function.entry {
                for (parameter, _) in &block.params {
                    if let Some(i) = self.index(*parameter, work)? {
                        union(&mut self.global, i, NON_FRAME, work)?;
                    }
                }
            }
            for node in &block.body {
                work.admit(1, 0)?;
                for result in &node.results {
                    let Some(i) = self.index(*result, work)? else {
                        continue;
                    };
                    match &node.inst {
                        Inst::OpenFrame { def } => {
                            union(&mut self.global, i, LIVE, work)?;
                            let di = declaration_index(declarations, def.id.index(), work)?;
                            let at = self.origin_offset(i, di);
                            union(&mut self.global, at, 1, work)?;
                        }
                        Inst::BindSlot { .. } => {}
                        _ => {
                            union(&mut self.global, i, NON_FRAME, work)?;
                        }
                    }
                }
            }
        }
        loop {
            work.admit(1, 0)?;
            let mut changed = false;
            for block in &function.blocks {
                work.admit(1, 0)?;
                for node in &block.body {
                    work.admit(1, 0)?;
                    if let Inst::BindSlot { frame, .. } = &node.inst
                        && let Some(from) = self.index(*frame, work)?
                    {
                        for result in &node.results {
                            if let Some(to) = self.index(*result, work)? {
                                changed |= self.global_copy(from, to, work)?;
                            }
                        }
                    }
                }
                let Some(last) = block.body.last() else {
                    continue;
                };
                self.edges = last
                    .inst
                    .successor_edges_observed(work.session, work.site)?;
                for ei in 0..self.edges.len() {
                    work.admit(1, size_of::<Edge<'_>>())?;
                    let edge = self.edges[ei];
                    let Some(target) = block_index(function, edge.target, work)? else {
                        continue;
                    };
                    for (argument, (parameter, _)) in
                        edge.args.iter().zip(&function.blocks[target].params)
                    {
                        if let (Some(from), Some(to)) =
                            (self.index(*argument, work)?, self.index(*parameter, work)?)
                        {
                            changed |= self.global_copy(from, to, work)?;
                        }
                    }
                }
                work.drain(&mut self.edges);
            }
            if !changed {
                break;
            }
        }
        for i in 0..self.handles_len {
            work.admit(1, 1)?;
            if self.global[i] == 0 {
                union(&mut self.global, i, NON_FRAME, work)?;
            }
            for j in 0..self.handles_len {
                let mut aliases = false;
                work.admit(
                    self.declarations_len,
                    self.declarations_len
                        .checked_mul(2)
                        .ok_or(ObservedValueError::CapacityOverflow)?,
                )?;
                for di in 0..self.declarations_len {
                    aliases |= self.global[self.origin_offset(i, di)] != 0
                        && self.global[self.origin_offset(j, di)] != 0;
                }
                let at = self.alias_offset(i, j);
                union(&mut self.global, at, u8::from(aliases), work)?;
            }
        }
        Ok(())
    }

    pub(super) fn solve<O: ExecutionObserver>(
        &mut self,
        function: &'a Function,
        declarations: &[(u32, &'a [BindingSlot])],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if self.handles_len == 0 {
            return Ok(());
        }
        let entry =
            block_index(function, function.entry, work)?.ok_or(ObservedValueError::InvalidRange)?;
        work.admit(1, 1)?;
        self.reachable[entry] = 1;
        for i in 0..self.handles_len {
            let at = entry * self.stride + i;
            union(&mut self.entries, at, NON_FRAME, work)?;
        }
        loop {
            work.admit(1, 0)?;
            let mut changed = false;
            for bi in 0..function.blocks.len() {
                work.admit(1, 1)?;
                if self.reachable[bi] == 0 {
                    continue;
                }
                self.prepare_block(bi, work)?;
                for node in &function.blocks[bi].body {
                    self.step(node, declarations, work)?;
                }
                let Some(last) = function.blocks[bi].body.last() else {
                    continue;
                };
                self.edges = last
                    .inst
                    .successor_edges_observed(work.session, work.site)?;
                for ei in 0..self.edges.len() {
                    work.admit(1, size_of::<Edge<'_>>())?;
                    let edge = self.edges[ei];
                    let Some(target) = block_index(function, edge.target, work)? else {
                        continue;
                    };
                    self.identity_mapping(work)?;
                    // Empty unwind argument lists are preserved: each target
                    // parameter without an explicit value becomes non-frame.
                    for (pi, (parameter, _)) in function.blocks[target].params.iter().enumerate() {
                        if let Some(to) = self.index(*parameter, work)? {
                            let from = match edge.args.get(pi) {
                                Some(argument) => {
                                    self.index(*argument, work)?.unwrap_or(self.handles_len)
                                }
                                None => self.handles_len,
                            };
                            work.admit(1, size_of::<usize>())?;
                            self.mapping[to] = from;
                        }
                    }
                    copy(&self.current, &mut self.snapshot, work)?;
                    self.mapped(true, work)?;
                    work.admit(1, 1)?;
                    changed |= self.reachable[target] == 0;
                    self.reachable[target] = 1;
                    for si in 0..self.stride {
                        changed |= union(
                            &mut self.entries,
                            target * self.stride + si,
                            self.edge[si],
                            work,
                        )?;
                    }
                }
                work.drain(&mut self.edges);
            }
            if !changed {
                return Ok(());
            }
        }
    }

    pub(super) fn prepare_block<O: ExecutionObserver>(
        &mut self,
        block: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 1)?;
        if self.reachable[block] == 0 {
            copy(&self.global, &mut self.current, work)
        } else {
            let start = block * self.stride;
            copy(
                &self.entries[start..start + self.stride],
                &mut self.current,
                work,
            )
        }
    }

    pub(super) fn flags<O: ExecutionObserver>(
        &self,
        value: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<u8> {
        work.admit(1, 1)?;
        self.current
            .get(value)
            .copied()
            .ok_or(ObservedValueError::InvalidRange)
    }

    pub(super) fn origin<O: ExecutionObserver>(
        &self,
        value: usize,
        declaration: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, 1)?;
        Ok(self.current[self.origin_offset(value, declaration)] != 0)
    }

    fn identity_mapping<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        for i in 0..self.handles_len {
            work.admit(1, size_of::<usize>())?;
            self.mapping[i] = i;
        }
        Ok(())
    }

    fn mapped<O: ExecutionObserver>(&mut self, to_edge: bool, work: &mut Work<'_, '_, O>) -> R {
        // Every read is from the frozen pre-assignment snapshot. In particular
        // block-parameter swaps cannot observe a previous parameter assignment.
        for i in 0..self.handles_len {
            work.admit(1, 1 + size_of::<usize>())?;
            let from = self.mapping[i];
            let flag = if from < self.handles_len {
                self.snapshot[from]
            } else {
                NON_FRAME
            };
            if to_edge {
                self.edge[i] = flag
            } else {
                self.current[i] = flag
            }
            work.admit(self.declarations_len, self.declarations_len)?;
            for di in 0..self.declarations_len {
                let bit = if from < self.handles_len {
                    self.snapshot[self.origin_offset(from, di)]
                } else {
                    0
                };
                let at = self.origin_offset(i, di);
                if to_edge {
                    self.edge[at] = bit
                } else {
                    self.current[at] = bit
                }
            }
            work.admit(
                self.handles_len,
                self.handles_len
                    .checked_mul(1 + size_of::<usize>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            for j in 0..self.handles_len {
                let other = self.mapping[j];
                let bit = if from < self.handles_len && other < self.handles_len {
                    self.snapshot[self.alias_offset(from, other)]
                } else {
                    0
                };
                let at = self.alias_offset(i, j);
                if to_edge {
                    self.edge[at] = bit
                } else {
                    self.current[at] = bit
                }
            }
        }
        Ok(())
    }

    pub(super) fn step<O: ExecutionObserver>(
        &mut self,
        node: &trust_ir::InstrNode,
        declarations: &[(u32, &'a [BindingSlot])],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.handles_len == 0 {
            return Ok(());
        }
        if let Inst::CloseFrame { frame } = &node.inst
            && let Some(i) = self.index(*frame, work)?
        {
            for j in 0..self.handles_len {
                work.admit(1, 1)?;
                if self.current[self.alias_offset(i, j)] != 0 {
                    union(&mut self.current, j, DEAD, work)?;
                }
            }
        }
        if node.results.is_empty() {
            return Ok(());
        }
        self.identity_mapping(work)?;
        let source = match &node.inst {
            Inst::BindSlot { frame, .. } => self.index(*frame, work)?.unwrap_or(self.handles_len),
            _ => self.handles_len,
        };
        let mut tracked = false;
        for result in &node.results {
            if let Some(i) = self.index(*result, work)? {
                work.admit(1, size_of::<usize>())?;
                self.mapping[i] = source;
                tracked = true;
            }
        }
        if !tracked {
            return Ok(());
        }
        copy(&self.current, &mut self.snapshot, work)?;
        self.mapped(false, work)?;
        if let Inst::OpenFrame { def } = &node.inst {
            let di = declaration_index(declarations, def.id.index(), work)?;
            for result in &node.results {
                if let Some(i) = self.index(*result, work)? {
                    work.admit(2, 2)?;
                    self.current[i] = LIVE;
                    let at = self.origin_offset(i, di);
                    self.current[at] = 1;
                    for other in &node.results {
                        if let Some(j) = self.index(*other, work)? {
                            work.admit(1, 1)?;
                            let at = self.alias_offset(i, j);
                            self.current[at] = 1;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn storage_empty(&self) -> bool {
        self.handles.capacity() == 0
            && self.global.capacity() == 0
            && self.entries.capacity() == 0
            && self.reachable.capacity() == 0
            && self.current.capacity() == 0
            && self.snapshot.capacity() == 0
            && self.edge.capacity() == 0
            && self.mapping.capacity() == 0
            && self.edges.capacity() == 0
    }

    #[cfg(test)]
    pub(super) fn has_rows(&self) -> bool {
        !self.handles.is_empty()
    }

    #[cfg(test)]
    pub(super) fn has_analysis(&self) -> bool {
        !self.entries.is_empty()
            && !self.current.is_empty()
            && !self.snapshot.is_empty()
            && !self.mapping.is_empty()
    }

    #[cfg(test)]
    pub(super) fn has_edges(&self) -> bool {
        !self.edges.is_empty()
    }

    pub(super) fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.drain(&mut self.handles);
        work.drain(&mut self.global);
        work.drain(&mut self.entries);
        work.drain(&mut self.reachable);
        work.drain(&mut self.current);
        work.drain(&mut self.snapshot);
        work.drain(&mut self.edge);
        work.drain(&mut self.mapping);
        work.drain(&mut self.edges);
    }
}

fn union<O: ExecutionObserver>(
    rows: &mut [u8],
    index: usize,
    bits: u8,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, 2)?;
    let value = rows
        .get_mut(index)
        .ok_or(ObservedValueError::InvalidRange)?;
    let next = *value | bits;
    let changed = next != *value;
    *value = next;
    Ok(changed)
}

fn copy<O: ExecutionObserver>(
    source: &[u8],
    destination: &mut [u8],
    work: &mut Work<'_, '_, O>,
) -> R {
    if source.len() != destination.len() {
        return Err(ObservedValueError::InvalidRange);
    }
    // Admit the complete bounded copy before touching either payload. One
    // batch avoids an observer allocation per byte while charging every byte.
    work.admit(source.len(), source.len())?;
    destination.copy_from_slice(source);
    Ok(())
}

fn block_index<O: ExecutionObserver>(
    function: &Function,
    id: BlockId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<usize>> {
    for (index, block) in function.blocks.iter().enumerate().rev() {
        work.admit(1, size_of::<BlockId>())?;
        if block.id == id {
            return Ok(Some(index));
        }
    }
    Ok(None)
}

fn declaration_index<O: ExecutionObserver>(
    declarations: &[(u32, &[BindingSlot])],
    id: u32,
    work: &mut Work<'_, '_, O>,
) -> R<usize> {
    for (index, (candidate, _)) in declarations.iter().enumerate() {
        work.admit(1, size_of::<u32>())?;
        if *candidate == id {
            return Ok(index);
        }
    }
    Err(ObservedValueError::InvalidRange)
}
