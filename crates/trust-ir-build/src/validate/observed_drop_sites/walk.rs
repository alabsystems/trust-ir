// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        index: &ObservedDropGlueIndex<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut fi = 0usize;
        while let Some(function) = work.at(&module.functions, fi)? {
            let mut bi = 0usize;
            while let Some(block) = work.at(&function.blocks, bi)? {
                let mut ni = 0usize;
                while let Some(node) = work.at(&block.body, ni)? {
                    work.admit(2, size_of::<&Inst>() + size_of::<u32>())?;
                    self.instruction(module, index, function, block.id.index(), &node.inst, work)?;
                    work.next(&mut ni)?;
                }
                work.next(&mut bi)?;
            }
            work.next(&mut fi)?;
        }
        Ok(())
    }
    fn instruction<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        index: &ObservedDropGlueIndex<'_>,
        function: &Function,
        block: u32,
        inst: &Inst,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, size_of::<&Ty>() + size_of::<bool>())?;
        if let Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } = inst {
            work.admit(1, size_of::<bool>())?;
            if matches!(ty, Ty::Refine(..)) {
                self.type_reason(ty, TypeRule::Refined, work)?;
                self.emit(function, block, work)?;
            } else if ty.is_trivially_droppable_observed(&module.types, work.session, work.site)? {
                self.type_reason(ty, TypeRule::Trivial, work)?;
                self.emit(function, block, work)?;
            }
        }
        if index.is_empty(work.session, work.site)? {
            return Ok(());
        }
        work.admit(3, size_of::<Option<(FuncId, &str)>>())?;
        // Same fixed panic_site dispatch as the original method. No operands,
        // signatures, type payloads or source text are traversed for this row.
        let direct = match inst {
            Inst::Call { callee, .. }
            | Inst::CallCannotUnwind { callee, .. }
            | Inst::Invoke { callee, .. } => Some((*callee, "call")),
            Inst::SeqMap { fwd, .. } => Some((*fwd, "seq_map element call")),
            Inst::Assert {
                site: Some(site), ..
            }
            | Inst::AssertInvoke { site, .. } => Some((site.entry, "panic-site entry")),
            _ => None,
        };
        work.admit(1, size_of::<bool>())?;
        if let Some((callee, what)) = direct
            && index.is_glue(callee, work.session, work.site)?
        {
            self.direct_reason(callee, what, work)?;
            self.emit(function, block, work)?;
        }
        Ok(())
    }
}
