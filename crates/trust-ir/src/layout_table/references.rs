// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Reference validity of payloads whose storage is deliberately absent.
//!
//! This is not a layout or inhabitedness query. Nominal cycles are visited
//! once and are valid references; only the separate least-fixed-point proof
//! can establish that an inactive variant is dead. Full source typing (such
//! as function signatures and refinement predicates) stays with validation.

use super::*;
use std::collections::BTreeSet;
use std::convert::Infallible;

pub(super) type Key = (u8, u32);

pub(super) trait Work {
    type Error;
    fn poll(&mut self) -> Result<(), Self::Error>;
    fn push<'a>(&mut self, pending: &mut Vec<&'a Ty>, ty: &'a Ty) -> Result<(), Self::Error>;
    fn mark(&mut self, seen: &mut BTreeSet<Key>, key: Key) -> Result<bool, Self::Error>;
    fn function_item(&mut self, module: &Module, id: crate::FuncId) -> Result<bool, Self::Error>;
    fn retire(&mut self, pending: Vec<&Ty>, seen: BTreeSet<Key>);
}

struct Ordinary<F> {
    function_item: F,
}
impl<F: FnMut(crate::FuncId) -> bool> Work for Ordinary<F> {
    type Error = Infallible;
    fn poll(&mut self) -> Result<(), Infallible> {
        Ok(())
    }
    fn push<'a>(&mut self, pending: &mut Vec<&'a Ty>, ty: &'a Ty) -> Result<(), Infallible> {
        pending.push(ty);
        Ok(())
    }
    fn mark(&mut self, seen: &mut BTreeSet<Key>, key: Key) -> Result<bool, Infallible> {
        Ok(seen.insert(key))
    }
    fn function_item(&mut self, _module: &Module, id: crate::FuncId) -> Result<bool, Infallible> {
        Ok((self.function_item)(id))
    }
    fn retire(&mut self, _pending: Vec<&Ty>, _seen: BTreeSet<Key>) {}
}

pub(crate) fn valid_with<'a>(
    module: &'a Module,
    tys: impl Iterator<Item = &'a Ty>,
    function_item: impl FnMut(crate::FuncId) -> bool,
) -> bool {
    match walk(module, tys, &mut Ordinary { function_item }) {
        Ok(valid) => valid,
        Err(never) => match never {},
    }
}

pub(super) fn walk<'a, W: Work>(
    module: &'a Module,
    tys: impl Iterator<Item = &'a Ty>,
    work: &mut W,
) -> Result<bool, W::Error> {
    let mut pending = Vec::new();
    let mut seen = BTreeSet::new();
    let result = (|| {
        for ty in tys {
            work.push(&mut pending, ty)?;
        }
        while !pending.is_empty() {
            work.poll()?;
            let Some(ty) = pending.pop() else { break };
            let key = match ty {
                Ty::Array(id, _)
                | Ty::Set(id, _)
                | Ty::Sequence(id)
                | Ty::Refine(id, _)
                | Ty::FatPtr(crate::ty::FatPtrKind::Slice(id)) => Some((0, id.index())),
                Ty::Struct(id) => Some((1, id.index())),
                Ty::Enum(id) => Some((2, id.index())),
                Ty::Record(id) => Some((3, id.index())),
                Ty::Closure(id) => Some((4, id.index())),
                _ => None,
            };
            if let Some(key) = key
                && !work.mark(&mut seen, key)?
            {
                continue;
            }
            match ty {
                Ty::FnItem(id) => {
                    if !work.function_item(module, *id)? {
                        return Ok(false);
                    }
                }
                Ty::Array(id, _)
                | Ty::Set(id, _)
                | Ty::Sequence(id)
                | Ty::Refine(id, _)
                | Ty::FatPtr(crate::ty::FatPtrKind::Slice(id)) => {
                    let Some(ty) = module.types.get(id.as_usize()) else {
                        return Ok(false);
                    };
                    work.push(&mut pending, ty)?;
                }
                Ty::Struct(id) => {
                    let mut found = None;
                    for def in &module.structs {
                        work.poll()?;
                        if def.id == *id {
                            found = Some(def);
                            break;
                        }
                    }
                    let Some(def) = found else { return Ok(false) };
                    for field in &def.fields {
                        work.push(&mut pending, &field.ty)?;
                    }
                }
                Ty::Enum(id) => {
                    let mut found = None;
                    for def in &module.enums {
                        work.poll()?;
                        if def.id == *id {
                            found = Some(def);
                            break;
                        }
                    }
                    let Some(def) = found else { return Ok(false) };
                    for variant in &def.variants {
                        work.poll()?;
                        for ty in &variant.fields {
                            work.push(&mut pending, ty)?;
                        }
                    }
                }
                Ty::Record(id) => {
                    let mut found = None;
                    for def in &module.records {
                        work.poll()?;
                        if def.id == *id {
                            found = Some(def);
                            break;
                        }
                    }
                    let Some(def) = found else { return Ok(false) };
                    for field in &def.fields {
                        work.push(&mut pending, &field.ty)?;
                    }
                }
                Ty::Closure(id) => {
                    let Some(def) = module.closure_type(*id) else {
                        return Ok(false);
                    };
                    for ty in &def.captures {
                        work.push(&mut pending, ty)?;
                    }
                }
                Ty::Vector(ty, _)
                | Ty::Ref(ty)
                | Ty::RefMut(ty)
                | Ty::PtrConst(ty)
                | Ty::PtrMut(ty)
                | Ty::Rc(ty) => work.push(&mut pending, ty)?,
                Ty::Tuple(tys) => {
                    for ty in tys {
                        work.push(&mut pending, ty)?;
                    }
                }
                Ty::Error => return Ok(false),
                _ => {}
            }
        }
        Ok(true)
    })();
    work.retire(pending, seen);
    work.poll()?;
    result
}
