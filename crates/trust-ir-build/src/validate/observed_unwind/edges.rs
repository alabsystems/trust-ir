// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> Checking<'a> {
    pub(super) fn leading<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            let id = block.id.index();
            let leads = block
                .body
                .first()
                .is_some_and(|node| matches!(node.inst, Inst::LandingPad { .. }));
            let mut found = false;
            for (other, all) in &mut self.leading {
                work.admit(1, 0)?;
                if *other == id {
                    *all &= leads;
                    found = true;
                    break;
                }
            }
            if !found {
                work.push(&mut self.leading, (id, leads))?;
            }
        }
        Ok(())
    }
    pub(super) fn edges<O: ExecutionObserver>(
        &mut self,
        function: &'a Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            let Some(term) = block.terminator() else {
                continue;
            };
            self.edges = term
                .inst
                .successor_edges_observed(work.session, work.site)?;
            let mut unwind = None;
            for edge in &self.edges {
                work.admit(1, 0)?;
                if edge.kind == EdgeKind::Normal {
                    // Flattening preserves each target's canonical accessor
                    // source order and duplicates, without a nested map Vec.
                    work.push(&mut self.normal, (edge.target.index(), block.id.index()))?;
                } else if unwind.is_none() && edge.kind == EdgeKind::Unwind {
                    unwind = Some(edge.target.index());
                }
            }
            // Ordinary unwind_dest() builds another unobserved successor Vec.
            // Use the exact first unwind edge from the already observed list.
            if let Some(target) = unwind {
                work.push(&mut self.unwind, target)?;
                let mut pad_less = false;
                for (id, leads) in &self.leading {
                    work.admit(1, 0)?;
                    if *id == target {
                        pad_less = !leads;
                        break;
                    }
                }
                let mut doubles = false;
                for edge in &self.edges {
                    work.admit(1, 0)?;
                    if edge.kind == EdgeKind::Normal && edge.target.index() == target {
                        doubles = true;
                        break;
                    }
                }
                if pad_less || doubles {
                    self.fixed(block.id.index(), target, work)?;
                }
            }
            self.retire_edges(work);
            work.admit(1, 0)?;
        }
        Ok(())
    }
}
