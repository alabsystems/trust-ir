// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'m> State<'m> {
    pub(super) fn constants<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        registry: &HandleRegistry,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut global = 0usize;
        while let Some(row) = work.at(&module.globals, global)? {
            work.admit(1, size_of::<Option<&Constant>>())?;
            if let Some(initializer) = &row.initializer {
                work.text("global '", &mut self.location)?;
                work.text(&row.name, &mut self.location)?;
                work.text("'", &mut self.location)?;
                self.tree(initializer, registry, work)?;
                work.flat(take(&mut self.location));
                work.admit(1, 0)?;
            }
            work.next(&mut global)?;
        }
        let mut function = 0usize;
        while let Some(f) = work.at(&module.functions, function)? {
            let mut block = 0usize;
            while let Some(b) = work.at(&f.blocks, block)? {
                let mut node = 0usize;
                while let Some(row) = work.at(&b.body, node)? {
                    work.admit(1, size_of::<&Inst>())?;
                    if let Inst::Const { value, .. } = &row.inst {
                        work.text("function '", &mut self.location)?;
                        work.text(&f.name, &mut self.location)?;
                        work.text("' bb", &mut self.location)?;
                        work.number(b.id.index(), &mut self.location)?;
                        self.tree(value, registry, work)?;
                        work.flat(take(&mut self.location));
                        work.admit(1, 0)?;
                    }
                    work.next(&mut node)?;
                }
                work.next(&mut block)?;
            }
            work.next(&mut function)?;
        }
        Ok(())
    }
    pub(super) fn tree<O: ExecutionObserver>(
        &mut self,
        root: &'m Constant,
        registry: &HandleRegistry,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.stack)?;
        work.admit(1, size_of::<&Constant>())?;
        self.stack.push(root);
        loop {
            work.admit(1, size_of::<Option<&Constant>>())?;
            let Some(node) = self.stack.pop() else {
                break;
            };
            work.admit(1, size_of::<&Constant>())?;
            if let Constant::SymbolAddr { symbol, .. } = node
                && registry
                    .entry_for_symbol_observed(symbol, work.session, work.site)?
                    .is_some()
            {
                work.text(&self.location, &mut self.other)?;
                work.text(symbol, &mut self.symbol)?;
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
                self.errors
                    .push(ValidationError::HandleEntryPointAddressTaken {
                        location: take(&mut self.other),
                        symbol: take(&mut self.symbol),
                    });
            }
            // Read actual Constant::children/next bodies: these are a fixed
            // discriminant match and one slice cursor advance, no opaque walk
            // or allocation. Every actual cursor/append is separately paid.
            work.admit(1, size_of::<trust_ir::constant::ConstantChildren<'_>>())?;
            let mut children = node.children();
            loop {
                work.admit(1, size_of::<Option<&Constant>>())?;
                let Some(child) = children.next() else {
                    break;
                };
                work.reserve(&mut self.stack)?;
                work.admit(1, size_of::<&Constant>())?;
                self.stack.push(child);
            }
        }
        // Preserve original stack.extend(children) then LIFO visit order.
        Ok(())
    }
}
