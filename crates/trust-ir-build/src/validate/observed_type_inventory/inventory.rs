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
        registry: &HandleRegistry,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut i = 0usize;
        while let Some(ty) = work.at(&module.types, i)? {
            work.admit(1, size_of::<Location<'_>>())?;
            self.location(Location::Type(i), work)?;
            self.ty(module, registry, ty, work)?;
            work.next(&mut i)?;
        }
        let mut i = 0usize;
        while let Some(def) = work.at(&module.structs, i)? {
            let mut j = 0usize;
            while let Some(field) = work.at(&def.fields, j)? {
                work.admit(1, size_of::<Location<'_>>())?;
                self.location(Location::Struct(&def.name, j), work)?;
                self.ty(module, registry, &field.ty, work)?;
                work.next(&mut j)?;
            }
            work.next(&mut i)?;
        }
        let mut i = 0usize;
        while let Some(def) = work.at(&module.records, i)? {
            let mut j = 0usize;
            while let Some(field) = work.at(&def.fields, j)? {
                work.admit(1, size_of::<Location<'_>>())?;
                self.location(Location::Record(&def.name, j), work)?;
                self.ty(module, registry, &field.ty, work)?;
                work.next(&mut j)?;
            }
            work.next(&mut i)?;
        }
        let mut i = 0usize;
        while let Some(def) = work.at(&module.enums, i)? {
            let mut j = 0usize;
            while let Some(variant) = work.at(&def.variants, j)? {
                let mut k = 0usize;
                while let Some(ty) = work.at(&variant.fields, k)? {
                    work.admit(1, size_of::<Location<'_>>())?;
                    self.location(Location::Enum(&def.name, &variant.name, k), work)?;
                    self.ty(module, registry, ty, work)?;
                    work.next(&mut k)?;
                }
                work.next(&mut j)?;
            }
            work.next(&mut i)?;
        }
        let mut i = 0usize;
        while let Some(closure) = work.at(&module.closure_types, i)? {
            work.admit(
                2,
                size_of::<usize>() + size_of::<trust_ir::value::FuncTyId>(),
            )?;
            if closure.func.as_usize() >= module.func_types.len() {
                work.admit(1, size_of::<Location<'_>>() + size_of::<Ty>())?;
                self.location(Location::Closure(i), work)?;
                self.node(module, registry, &Ty::Func(closure.func), work)?;
            }
            let mut j = 0usize;
            while let Some(ty) = work.at(&closure.captures, j)? {
                work.admit(1, size_of::<Location<'_>>())?;
                self.location(Location::Capture(i, j), work)?;
                self.ty(module, registry, ty, work)?;
                work.next(&mut j)?;
            }
            work.next(&mut i)?;
        }
        let mut i = 0usize;
        while let Some(signature) = work.at(&module.func_types, i)? {
            let mut j = 0usize;
            while let Some(ty) = work.at(&signature.params, j)? {
                work.admit(1, size_of::<Location<'_>>())?;
                self.location(Location::Parameter(i, j), work)?;
                self.ty(module, registry, ty, work)?;
                work.next(&mut j)?;
            }
            let mut j = 0usize;
            while let Some(ty) = work.at(&signature.returns, j)? {
                work.admit(1, size_of::<Location<'_>>())?;
                self.location(Location::Return(i, j), work)?;
                self.ty(module, registry, ty, work)?;
                work.next(&mut j)?;
            }
            work.next(&mut i)?;
        }
        let mut i = 0usize;
        while let Some(global) = work.at(&module.globals, i)? {
            work.admit(1, size_of::<Location<'_>>())?;
            self.location(Location::Global(&global.name), work)?;
            self.ty(module, registry, &global.ty, work)?;
            work.next(&mut i)?;
        }
        let mut i = 0usize;
        while let Some(row) = work.at(&module.drop_glue, i)? {
            work.admit(1, size_of::<Location<'_>>())?;
            self.location(Location::DropGlue(i), work)?;
            self.ty(module, registry, &row.ty, work)?;
            work.next(&mut i)?;
        }
        let mut i = 0usize;
        while let Some(function) = work.at(&module.functions, i)? {
            let mut j = 0usize;
            while let Some(block) = work.at(&function.blocks, j)? {
                work.admit(1, size_of::<Location<'_>>())?;
                self.location(Location::Function(&function.name, block.id.index()), work)?;
                let mut k = 0usize;
                while let Some((_, ty)) = work.at(&block.params, k)? {
                    self.ty(module, registry, ty, work)?;
                    work.next(&mut k)?;
                }
                let mut k = 0usize;
                while let Some(node) = work.at(&block.body, k)? {
                    self.instruction(module, registry, &node.inst, work)?;
                    work.next(&mut k)?;
                }
                work.next(&mut j)?;
            }
            work.next(&mut i)?;
        }
        Ok(())
    }
}
