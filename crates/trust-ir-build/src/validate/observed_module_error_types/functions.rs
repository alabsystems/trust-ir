// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn functions<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let mut i = 0;
        while i < module.functions.len() {
            work.admit(1, 0)?;
            let function = &module.functions[i];
            let mut j = 0;
            while j < function.blocks.len() {
                work.admit(1, 0)?;
                let block = &function.blocks[j];
                let mut k = 0;
                while k < block.params.len() {
                    work.surface()?;
                    let (id, ty) = &block.params[k];
                    self.surface(
                        Location::Parameter(&function.name, block.id.index(), id.index()),
                        ty,
                        work,
                    )?;
                    k += 1;
                }
                k = 0;
                while k < block.body.len() {
                    work.surface()?;
                    let node = &block.body[k];
                    // This original helper is only an exhaustive fixed enum
                    // discriminant-to-static-text table, with no payload walk.
                    work.admit(67, size_of::<&str>())?;
                    let kind = instruction_kind(&node.inst);
                    self.location(
                        Location::Instruction(&function.name, block.id.index(), k, kind),
                        work,
                    )?;
                    self.instruction(&node.inst, work)?;
                    self.end_location(work)?;
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
        Ok(())
    }

    fn instruction<O: ExecutionObserver>(
        &mut self,
        instruction: &'a Inst,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Vec<&Ty>>())?;
        // Retain successful borrowed header output before any next fallible
        // predicate or attribute operation. The helper owns refused partials.
        self.types = instruction.inline_types_observed(work.session, work.site)?;
        let mut i = 0;
        while i < self.types.len() {
            work.admit(1, size_of::<&Ty>())?;
            self.check(self.types[i], Buffer::Base, work)?;
            i += 1;
        }
        work.retire_refs(&mut self.types);
        work.admit(1, 0)?;
        if let Inst::DialectOp(op) = instruction {
            let mut i = 0;
            while i < op.attrs.len() {
                work.admit(7, size_of::<&trust_ir::dialect::AttrEntry>())?;
                let attr = &op.attrs[i];
                if let trust_ir::dialect::AttrValue::Ty(ty) = &attr.value {
                    work.text(&self.location, &mut self.attribute)?;
                    work.text(" attr '", &mut self.attribute)?;
                    work.text(&attr.name, &mut self.attribute)?;
                    work.text("'", &mut self.attribute)?;
                    self.check(ty, Buffer::Attribute, work)?;
                    work.retire(take(&mut self.attribute));
                    work.admit(1, 0)?;
                }
                i += 1;
            }
        }
        Ok(())
    }
}
