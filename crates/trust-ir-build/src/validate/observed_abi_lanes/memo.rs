// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl ObservedAbiLanes<'_> {
    fn position<O: ExecutionObserver>(
        &self,
        node: Node,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<usize>> {
        let mut i = 0;
        while let Some(&(key, _)) = w.at(&self.nodes, i)? {
            w.admit(4, size_of::<bool>())?;
            if key == node {
                return Ok(Some(i));
            }
            w.next(&mut i)?;
        }
        Ok(None)
    }
    pub(super) fn read<O: ExecutionObserver>(
        &self,
        node: Node,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<Slot>> {
        let at = self.position(node, w)?;
        w.admit(1, size_of::<Option<Slot>>())?;
        Ok(at.map(|i| self.nodes[i].1))
    }
    pub(super) fn write<O: ExecutionObserver>(
        &mut self,
        node: Node,
        slot: Slot,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        if let Some(i) = self.position(node, w)? {
            w.admit(1, size_of::<Slot>())?;
            self.nodes[i].1 = slot;
            Ok(())
        } else {
            w.push(&mut self.nodes, (node, slot))
        }
    }
}
impl<'a> Fields<'a> {
    pub(super) fn at<O: ExecutionObserver>(
        self,
        i: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a Ty>> {
        w.admit(2, size_of::<Option<&Ty>>())?;
        Ok(match self {
            Fields::Types(rows) => rows.get(i),
            Fields::Struct(rows) => rows.get(i).map(|f| &f.ty),
        })
    }
}
