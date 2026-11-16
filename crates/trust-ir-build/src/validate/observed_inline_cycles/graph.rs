// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

// The closures at every call below are fixed, private id-field projections,
// never a caller callback or a variable traversal hidden behind an admission.
pub(super) fn nominal<'m, T, O: ExecutionObserver>(
    rows: &'m [T],
    id: u32,
    identity: impl Fn(&T) -> u32,
    w: &mut Work<'_, '_, O>,
) -> R<Option<&'m T>> {
    if let Some(row) = w.at(rows, id as usize)? {
        w.admit(2, size_of::<bool>())?;
        if identity(row) == id {
            return Ok(Some(row));
        }
    }
    let mut i = 0;
    while let Some(row) = w.at(rows, i)? {
        w.admit(2, size_of::<bool>())?;
        if identity(row) == id {
            return Ok(Some(row));
        }
        w.next(&mut i)?;
    }
    Ok(None)
}
impl<'m> State<'m> {
    pub(super) fn graph<O: ExecutionObserver>(
        &mut self,
        m: &'m Module,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.table_nodes(m, w)?;
        let mut i = 0;
        while let Some(&node) = w.at(&self.nodes, i)? {
            self.queue_node(m, node, w)?;
            self.walk_pending(m, w)?;
            w.reserve(&mut self.successors)?;
            w.admit(1, 2 * size_of::<Vec<usize>>())?;
            self.successors.push(take(&mut self.edges));
            w.next(&mut i)?;
        }
        Ok(())
    }
    fn table_nodes<O: ExecutionObserver>(&mut self, m: &Module, w: &mut Work<'_, '_, O>) -> R {
        let mut i = 0;
        while let Some(def) = w.at(&m.structs, i)? {
            w.admit(1, size_of::<Node>())?;
            w.insert(&mut self.nodes, Node::Struct(def.id.index()))?;
            w.next(&mut i)?;
        }
        i = 0;
        while let Some(def) = w.at(&m.enums, i)? {
            w.admit(1, size_of::<Node>())?;
            w.insert(&mut self.nodes, Node::Enum(def.id.index()))?;
            w.next(&mut i)?;
        }
        i = 0;
        while let Some(def) = w.at(&m.records, i)? {
            w.admit(1, size_of::<Node>())?;
            w.insert(&mut self.nodes, Node::Record(def.id.index()))?;
            w.next(&mut i)?;
        }
        for (length, closure) in [(m.closure_types.len(), true), (m.types.len(), false)] {
            i = 0;
            while i < length {
                w.admit(
                    3,
                    size_of::<Node>() + size_of::<Result<u32, core::num::TryFromIntError>>(),
                )?;
                let Ok(id) = u32::try_from(i) else { break };
                let node = if closure {
                    Node::Closure(id)
                } else {
                    Node::Row(id)
                };
                w.insert(&mut self.nodes, node)?;
                w.next(&mut i)?;
            }
        }
        Ok(())
    }
    fn queue_node<O: ExecutionObserver>(
        &mut self,
        m: &'m Module,
        node: Node,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(5, 0)?;
        match node {
            Node::Struct(id) => {
                if let Some(def) = nominal(&m.structs, id, |d| d.id.index(), w)? {
                    let mut i = 0;
                    while let Some(field) = w.at(&def.fields, i)? {
                        w.push(&mut self.pending, &field.ty)?;
                        w.next(&mut i)?;
                    }
                }
            }
            Node::Record(id) => {
                if let Some(def) = nominal(&m.records, id, |d| d.id.index(), w)? {
                    let mut i = 0;
                    while let Some(field) = w.at(&def.fields, i)? {
                        w.push(&mut self.pending, &field.ty)?;
                        w.next(&mut i)?;
                    }
                }
            }
            Node::Enum(id) => {
                if let Some(def) = nominal(&m.enums, id, |d| d.id.index(), w)? {
                    let mut i = 0;
                    while let Some(variant) = w.at(&def.variants, i)? {
                        self.queue_types(&variant.fields, w)?;
                        w.next(&mut i)?;
                    }
                }
            }
            Node::Closure(id) => {
                if let Some(def) = w.at(&m.closure_types, id as usize)? {
                    self.queue_types(&def.captures, w)?;
                }
            }
            Node::Row(id) => {
                if let Some(ty) = w.at(&m.types, id as usize)? {
                    w.push(&mut self.pending, ty)?;
                }
            }
        }
        Ok(())
    }
    fn queue_types<O: ExecutionObserver>(&mut self, rows: &'m [Ty], w: &mut Work<'_, '_, O>) -> R {
        let mut i = 0;
        while let Some(ty) = w.at(rows, i)? {
            w.push(&mut self.pending, ty)?;
            w.next(&mut i)?;
        }
        Ok(())
    }
    fn walk_pending<O: ExecutionObserver>(&mut self, m: &Module, w: &mut Work<'_, '_, O>) -> R {
        loop {
            w.admit(67, size_of::<Option<&Ty>>())?;
            let Some(ty) = self.pending.pop() else {
                return Ok(());
            };
            let node = match ty {
                Ty::Storage(_) => None,
                Ty::Struct(id) => nominal(&m.structs, id.index(), |d| d.id.index(), w)?
                    .map(|_| Node::Struct(id.index())),
                Ty::Enum(id) => nominal(&m.enums, id.index(), |d| d.id.index(), w)?
                    .map(|_| Node::Enum(id.index())),
                Ty::Record(id) => nominal(&m.records, id.index(), |d| d.id.index(), w)?
                    .map(|_| Node::Record(id.index())),
                Ty::Closure(id) => w
                    .at(&m.closure_types, id.as_usize())?
                    .map(|_| Node::Closure(id.index())),
                Ty::Array(id, _) | Ty::Refine(id, _) => w
                    .at(&m.types, id.as_usize())?
                    .map(|_| Node::Row(id.index())),
                Ty::Tuple(rows) => {
                    self.queue_types(rows, w)?;
                    None
                }
                Ty::Vector(inner, _) => {
                    w.push(&mut self.pending, inner.as_ref())?;
                    None
                }
                Ty::Ptr
                | Ty::FatPtr(_)
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Rc(_)
                | Ty::Func(_)
                | Ty::FnItem(_)
                | Ty::Sequence(_)
                | Ty::Set(..)
                | Ty::Tensor(..)
                | Ty::Handle(_)
                | Ty::Dialect(_) => None,
                Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Char
                | Ty::F16
                | Ty::F32
                | Ty::F64
                | Ty::Bool
                | Ty::Unit
                | Ty::Never
                | Ty::Error => None,
                Ty::Ext(extension) => extension.unreachable(),
            };
            if let Some(node) = node {
                let mut i = 0;
                while let Some(&candidate) = w.at(&self.nodes, i)? {
                    w.admit(4, size_of::<bool>())?;
                    if candidate == node {
                        w.insert(&mut self.edges, i)?;
                        break;
                    }
                    w.next(&mut i)?;
                }
            }
        }
    }
}
