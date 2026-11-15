// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(16, size_of::<u32>())?;
        let pointer_bits = module.pointer_bits();
        let mut g = 0;
        while let Some(global) = work.at(&module.globals, g)? {
            work.admit(1, size_of::<Option<&Constant>>())?;
            if let Some(initializer) = global.initializer.as_ref() {
                work.text("global '", &mut self.location)?;
                work.text(&global.name, &mut self.location)?;
                work.text("'", &mut self.location)?;
                let result = self.tree(module, initializer, &global.ty, pointer_bits, work);
                self.retire_tree(work);
                result?;
                work.flat(take(&mut self.location));
                work.admit(1, 0)?;
            }
            work.next(&mut g)?;
        }
        let mut f = 0;
        while let Some(function) = work.at(&module.functions, f)? {
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                work.text("function '", &mut self.location)?;
                work.text(&function.name, &mut self.location)?;
                work.text("' bb", &mut self.location)?;
                work.unsigned(u128::from(block.id.index()), &mut self.location)?;
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    work.admit(1, size_of::<Option<(&Ty, &Constant)>>())?;
                    if let Inst::Const { ty, value } = &node.inst {
                        let result = self.tree(module, value, ty, pointer_bits, work);
                        self.retire_tree(work);
                        result?;
                        work.admit(1, 0)?;
                    }
                    work.next(&mut n)?;
                }
                work.flat(take(&mut self.location));
                work.admit(1, 0)?;
                work.next(&mut b)?;
            }
            work.next(&mut f)?;
        }
        Ok(())
    }
}
