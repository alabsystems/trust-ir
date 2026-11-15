// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'m> State<'m> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'m>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let module = catalog.source_module();
        if !queries::exists(module, work)? {
            return Ok(());
        }
        let mut f = 0;
        while let Some(function) = work.at(&module.functions, f)? {
            self.build_definitions(function, work)?;
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    self.node(catalog, function, block.id, n, node, work)?;
                    work.next(&mut n)?;
                }
                work.next(&mut b)?;
            }
            self.retire_definitions(work);
            work.admit(1, 0)?;
            work.next(&mut f)?;
        }
        Ok(())
    }
    fn node<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'m>,
        function: &Function,
        block: BlockId,
        index: usize,
        node: &'m trust_ir::InstrNode,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            67,
            size_of::<Option<FuncId>>() + size_of::<Option<&Function>>(),
        )?;
        match &node.inst {
            Inst::CallIndirect {
                callee,
                sig,
                calling_conv,
                ..
            }
            | Inst::CallIndirectCannotUnwind {
                callee,
                sig,
                calling_conv,
                ..
            }
            | Inst::InvokeIndirect {
                callee,
                sig,
                calling_conv,
                ..
            } => {
                if let Some(decl) = self.origin(catalog.source_module(), *callee, work)? {
                    self.indirect(
                        catalog.source_module(),
                        block.index(),
                        decl,
                        *sig,
                        *calling_conv,
                        work,
                    )?;
                }
                return Ok(());
            }
            Inst::Switch { cases, .. } => {
                let mut at = 0;
                while let Some(case) = work.at(cases, at)? {
                    self.location(function, block, index, Some(at), false, work)?;
                    let result = self.switch_tree(catalog, &case.value, work);
                    self.retire_tree(work);
                    result?;
                    work.admit(1, 0)?;
                    work.flat(take(&mut self.location));
                    work.admit(1, 0)?;
                    work.next(&mut at)?;
                }
                return Ok(());
            }
            _ => {}
        }
        let panic_entry = node.inst.panic_site().map(|s| s.entry);
        let callee = match &node.inst {
            Inst::Call { callee, .. }
            | Inst::CallCannotUnwind { callee, .. }
            | Inst::Invoke { callee, .. }
            | Inst::SeqMap { fwd: callee, .. } => Some((*callee, false)),
            _ => panic_entry.map(|id| (id, true)),
        };
        if let Some((id, panic)) = callee
            && let Some(target) = catalog.unique_observed(id, work.session, work.site)?
        {
            work.admit(8, size_of::<bool>())?;
            if target.is_weak_declaration() {
                self.direct(function, block, index, id, target, panic, work)?;
            }
        }
        Ok(())
    }
}
