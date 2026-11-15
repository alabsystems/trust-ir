// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    pub(super) fn follow<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        key: Key,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(6, size_of::<Key>() + size_of::<Option<&Ty>>())?;
        match key {
            Key::Ty(index) => {
                if let Some(ty) = work.at(&module.types, index)? {
                    work.push(&mut self.stack, ty)?;
                }
            }
            Key::Func(index) => self.signature(module, index, work)?,
            Key::Struct(id) => {
                let mut at = 0usize;
                while let Some(row) = work.at(&module.structs, at)? {
                    work.admit(1, size_of::<u32>() + size_of::<&[trust_ir::FieldDef]>())?;
                    if row.id.index() == id {
                        self.fields(&row.fields, work)?;
                    }
                    work.next(&mut at)?;
                }
            }
            Key::Enum(id) => {
                let mut at = 0usize;
                while let Some(row) = work.at(&module.enums, at)? {
                    work.admit(1, size_of::<u32>() + size_of::<&[trust_ir::EnumVariant]>())?;
                    if row.id.index() == id {
                        let mut index = 0usize;
                        while let Some(variant) = work.at(&row.variants, index)? {
                            work.admit(1, size_of::<&[Ty]>())?;
                            self.types(&variant.fields, work)?;
                            work.next(&mut index)?;
                        }
                    }
                    work.next(&mut at)?;
                }
            }
            Key::Record(id) => {
                let mut at = 0usize;
                while let Some(row) = work.at(&module.records, at)? {
                    work.admit(1, size_of::<u32>() + size_of::<&[trust_ir::FieldDef]>())?;
                    if row.id.index() == id {
                        self.fields(&row.fields, work)?;
                    }
                    work.next(&mut at)?;
                }
            }
            Key::Closure(index) => {
                if let Some(closure) = work.at(&module.closure_types, index)? {
                    work.admit(2, size_of::<usize>() + size_of::<&[Ty]>())?;
                    let signature = closure.func.as_usize();
                    self.types(&closure.captures, work)?;
                    if self.fresh(Key::Func(signature), work)? {
                        self.signature(module, signature, work)?;
                    }
                }
            }
        }
        Ok(())
    }
    fn signature<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if let Some(signature) = work.at(&module.func_types, index)? {
            work.admit(2, 2 * size_of::<&[Ty]>())?;
            self.types(&signature.params, work)?;
            self.types(&signature.returns, work)?;
        }
        Ok(())
    }
}
