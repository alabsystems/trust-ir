// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn components<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        let mut i = 0;
        while w.at(&self.nodes, i)?.is_some() {
            w.push(&mut self.marks, Mark::default())?;
            w.next(&mut i)?;
        }
        let mut root = 0;
        while let Some(mark) = w.at(&self.marks, root)? {
            w.admit(2, size_of::<bool>())?;
            if mark.index.is_none() {
                self.enter(root, w)?;
                self.dfs(w)?;
            }
            w.next(&mut root)?;
        }
        Ok(())
    }
    fn enter<O: ExecutionObserver>(&mut self, node: usize, w: &mut Work<'_, '_, O>) -> R {
        w.admit(3, size_of::<usize>())?;
        let number = self.number;
        self.number = number
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        w.reserve(&mut self.stack)?;
        w.reserve(&mut self.calls)?;
        w.admit(
            3,
            size_of::<Mark>() + size_of::<usize>() + size_of::<Frame>(),
        )?;
        let mark = self
            .marks
            .get_mut(node)
            .ok_or(ObservedValueError::InvalidRange)?;
        *mark = Mark {
            index: Some(number),
            lowlink: number,
            on_stack: true,
        };
        self.stack.push(node);
        self.calls.push(Frame { node, next: 0 });
        Ok(())
    }
    fn lower<O: ExecutionObserver>(
        &mut self,
        node: usize,
        low: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(2, size_of::<usize>())?;
        let mark = self
            .marks
            .get_mut(node)
            .ok_or(ObservedValueError::InvalidRange)?;
        mark.lowlink = mark.lowlink.min(low);
        Ok(())
    }
    fn dfs<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        loop {
            w.admit(1, size_of::<Option<Frame>>())?;
            let Some(frame) = self.calls.last().copied() else {
                return Ok(());
            };
            let edges = w
                .at(&self.successors, frame.node)?
                .ok_or(ObservedValueError::InvalidRange)?;
            let edge = w.at(edges, frame.next)?.copied();
            if let Some(next) = edge {
                w.admit(2, size_of::<usize>())?;
                let last = self
                    .calls
                    .last_mut()
                    .ok_or(ObservedValueError::InvalidRange)?;
                last.next = frame
                    .next
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let mark = w
                    .at(&self.marks, next)?
                    .copied()
                    .ok_or(ObservedValueError::InvalidRange)?;
                w.admit(3, 0)?;
                match mark {
                    Mark { index: None, .. } => self.enter(next, w)?,
                    Mark {
                        index: Some(index),
                        on_stack: true,
                        ..
                    } => self.lower(frame.node, index, w)?,
                    _ => {}
                }
                continue;
            }
            w.admit(1, size_of::<Option<Frame>>())?;
            self.calls.pop();
            let mark = w
                .at(&self.marks, frame.node)?
                .copied()
                .ok_or(ObservedValueError::InvalidRange)?;
            let index = mark.index.ok_or(ObservedValueError::InvalidRange)?;
            w.admit(1, size_of::<Option<Frame>>())?;
            if let Some(parent) = self.calls.last().copied() {
                self.lower(parent.node, mark.lowlink, w)?;
            }
            w.admit(1, 0)?;
            if mark.lowlink == index {
                self.finish_component(frame.node, w)?;
            }
        }
    }
    fn finish_component<O: ExecutionObserver>(
        &mut self,
        root: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        loop {
            w.admit(1, size_of::<Option<usize>>())?;
            let member = self.stack.pop().ok_or(ObservedValueError::InvalidRange)?;
            w.admit(1, size_of::<bool>())?;
            let mark = self
                .marks
                .get_mut(member)
                .ok_or(ObservedValueError::InvalidRange)?;
            mark.on_stack = false;
            w.insert(&mut self.component, member)?;
            w.admit(1, 0)?;
            if member == root {
                break;
            }
        }
        let mut i = 0;
        let mut self_edge = false;
        let edges = w
            .at(&self.successors, root)?
            .ok_or(ObservedValueError::InvalidRange)?;
        while let Some(&next) = w.at(edges, i)? {
            w.admit(1, 0)?;
            if next == root {
                self_edge = true;
                break;
            }
            w.next(&mut i)?;
        }
        w.admit(2, 0)?;
        if self.component.len() > 1 || self_edge {
            self.store_cycle(w)?;
        } else {
            w.rows(take(&mut self.component));
            w.admit(1, 0)?;
        }
        Ok(())
    }
    fn store_cycle<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        w.reserve(&mut self.cycles)?;
        w.admit(1, 2 * size_of::<Vec<usize>>())?;
        let mut i = self.cycles.len();
        self.cycles.push(take(&mut self.component));
        // Tarjan components are disjoint and nonempty, so their distinct least
        // members decide exactly the ordinary lexicographic component order.
        while i > 0 {
            w.admit(4, 2 * size_of::<usize>())?;
            let left = self
                .cycles
                .get(i - 1)
                .and_then(|c| c.first())
                .copied()
                .ok_or(ObservedValueError::InvalidRange)?;
            let right = self
                .cycles
                .get(i)
                .and_then(|c| c.first())
                .copied()
                .ok_or(ObservedValueError::InvalidRange)?;
            if left < right {
                break;
            }
            w.admit(1, 3 * size_of::<Vec<usize>>())?;
            self.cycles.swap(i - 1, i);
            i -= 1;
        }
        Ok(())
    }
}
