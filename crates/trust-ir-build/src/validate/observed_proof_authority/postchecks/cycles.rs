// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Post {
    pub(super) fn cycles<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        rows: &[TvRechecked],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut start = 0;
        while let Some(entry) = w.at(rows, start)? {
            self.cycle(catalog, rows, start, entry, w)?;
            w.rows(take(&mut self.scratch.parents));
            w.rows(take(&mut self.scratch.queue));
            w.rows(take(&mut self.scratch.path));
            w.next(&mut start)?;
        }
        Ok(())
    }
    fn cycle<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        rows: &[TvRechecked],
        start: usize,
        entry: &TvRechecked,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut closing = self.expand(start, start, w)?;
        let mut head = 0;
        while closing.is_none() {
            let Some(node) = w.at(&self.scratch.queue, head)?.copied() else {
                break;
            };
            w.next(&mut head)?;
            closing = self.expand(node, start, w)?;
        }
        let Some(mut cursor) = closing else {
            return Ok(());
        };
        w.push(&mut self.scratch.path, cursor)?;
        loop {
            w.admit(1, size_of::<bool>())?;
            if cursor == start {
                break;
            }
            cursor = self
                .parent(cursor, w)?
                .ok_or(ObservedValueError::InvalidRange)?;
            w.push(&mut self.scratch.path, cursor)?;
        }
        w.admit(1, size_of::<usize>())?;
        let mut at = 0;
        while at < self.scratch.path.len() / 2 {
            w.admit(4, 2 * size_of::<usize>())?;
            let other = self.scratch.path.len() - 1 - at;
            self.scratch.path.swap(at, other);
            w.next(&mut at)?;
        }
        w.push(&mut self.scratch.path, start)?;
        self.text("clean_backend_tv composition cycle: ", w)?;
        let mut at = 0;
        while let Some(index) = w.at(&self.scratch.path, at)?.copied() {
            if at != 0 {
                self.text(" → ", w)?;
            }
            let row = w.at(rows, index)?.ok_or(ObservedValueError::InvalidRange)?;
            self.name(catalog, row.function, w)?;
            w.next(&mut at)?;
        }
        self.text("; recursive composition is not grounded (the parametric equation of a recursive body says nothing about divergence) — REJECTED", w)?;
        self.failure(entry.obligation, w)
    }
    fn expand<O: ExecutionObserver>(
        &mut self,
        node: usize,
        start: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<usize>> {
        let mut at = 0;
        while let Some((from, next)) = w.at(&self.scratch.edges, at)?.copied() {
            w.admit(2, size_of::<bool>())?;
            if from == node {
                if next == start {
                    return Ok(Some(node));
                }
                if self.parent(next, w)?.is_none() {
                    w.push(&mut self.scratch.parents, (next, node))?;
                    w.push(&mut self.scratch.queue, next)?;
                }
            }
            w.next(&mut at)?;
        }
        Ok(None)
    }
    fn parent<O: ExecutionObserver>(
        &self,
        node: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<usize>> {
        let mut at = 0;
        while let Some((other, parent)) = w.at(&self.scratch.parents, at)? {
            w.admit(1, size_of::<bool>())?;
            if *other == node {
                return Ok(Some(*parent));
            }
            w.next(&mut at)?;
        }
        Ok(None)
    }
}
