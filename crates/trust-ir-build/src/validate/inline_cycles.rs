// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! By-value aggregate cycles (roadmap WS2.4, finding F-045).
//!
//! A type that contains itself BY VALUE — `struct Node { next: Node }` — has no
//! finite layout. `shape` refuses one when asked for a layout
//! (`StructLayoutIncoherent` / `TyLayoutCycle`), but only when asked, and only
//! for a struct that declares a size; a size-less struct never reaches its
//! guard. Before this rule no validator pass looked at containment at all, so
//! such a module validated and the reference interpreter recursed on it until
//! the host stack overflowed.
//!
//! The rule is a graph question over the module's type tables. A NODE is
//! anything with a table identity a cycle can pass through: a struct, an enum,
//! a record, a closure type, or a `TyId` row of `Module::types`. An EDGE is
//! by-value containment:
//!
//! * struct → its field types; record → its field types;
//! * enum → every variant's field types;
//! * closure type → its capture types;
//! * `TyId` → the type in that row, reached from `Array(TyId, _)` (the element
//!   is stored inline) and from `Refine(TyId, _)` (a refinement is
//!   representation-preserving, so its base IS its representation);
//! * `Tuple` and `Vector` are inline and have no identity: their element types
//!   are walked in place.
//!
//! The walk STOPS at every type whose value is a fixed-size handle rather than
//! the pointee: `Ptr`, `FatPtr`, `Ref`, `RefMut`, `PtrConst`, `PtrMut`, `Rc`,
//! `Func`, `Sequence` / `Set` (out-of-line storage), `Handle` and `Dialect`.
//! That is what makes `struct Node { next: *mut Node }` legal and
//! `struct Node { next: Node }` not.
//!
//! A cycle is a strongly connected component with more than one node, or one
//! node with a self-edge. Each is reported ONCE, as
//! [`ValidationError::InlineAggregateCycle`], naming its least node (and the
//! rest of the component). References to undefined ids are not edges here —
//! `DanglingTypeReference` owns them.
//!
//! The SCC search is iterative (Tarjan with an explicit call stack), so an
//! adversarially deep but acyclic nesting chain cannot overflow the
//! validator's own stack either.
//!
//! D1a: nothing here may panic, index, wrap or truncate — every per-node read
//! goes through `get`, DFS numbers come from an exact range, and a table row
//! past `u32::MAX` (which nothing can name) is enumerated by
//! `(0..=u32::MAX).zip(..)`, never cast. Rung: a type-resolved lint (gate 0
//! `workspace-clippy`).

#![cfg_attr(
    not(test),
    deny(
        clippy::panic,
        clippy::unwrap_used,
        clippy::expect_used,
        clippy::indexing_slicing,
        clippy::arithmetic_side_effects,
        clippy::cast_possible_truncation
    )
)]

use super::ValidationError;
use std::collections::{BTreeMap, BTreeSet};
use trust_ir::value::{ClosureTyId, EnumId, RecordId, StructId, TyId};
use trust_ir::{Module, Ty};

/// A type with a table identity. The derived order (struct, enum, record,
/// closure, type row; then id) picks the node a component is reported by.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Struct(StructId),
    Enum(EnumId),
    Record(RecordId),
    Closure(ClosureTyId),
    Row(TyId),
}

/// The nodes a value of `ty` holds inline, walking through the identity-less
/// inline carriers (`Tuple`, `Vector`) and stopping at every indirection.
fn inline_nodes(module: &Module, ty: &Ty, out: &mut Vec<Node>) {
    let mut pending: Vec<&Ty> = vec![ty];
    while let Some(ty) = pending.pop() {
        let node = match ty {
            Ty::Storage(_) => None,
            Ty::Struct(id) => module.struct_def(*id).map(|_| Node::Struct(*id)),
            Ty::Enum(id) => module.enum_def(*id).map(|_| Node::Enum(*id)),
            Ty::Record(id) => module.record_def(*id).map(|_| Node::Record(*id)),
            Ty::Closure(id) => module.closure_type(*id).map(|_| Node::Closure(*id)),
            Ty::Array(elem, _) | Ty::Refine(elem, _) => module.ty(*elem).map(|_| Node::Row(*elem)),
            Ty::Tuple(elems) => {
                pending.extend(elems.iter());
                None
            }
            Ty::Vector(elem, _) => {
                pending.push(elem);
                None
            }
            // Indirections: a fixed-size handle, never the pointee inline.
            Ty::Ptr
            | Ty::FatPtr(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Func(_)
            | Ty::Sequence(_)
            | Ty::Set(..)
            // The tensor region: a tensor's extents are run-time values, so
            // its elements are never laid out inline (it has no layout).
            | Ty::Tensor(..)
            | Ty::Handle(_)
            | Ty::Dialect(_) => None,
            // Leaves.
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
            Ty::Ext(e) => e.unreachable(),
        };
        out.extend(node);
    }
}

/// The by-value successors of `node`.
fn successors(module: &Module, node: Node) -> Vec<Node> {
    let mut out = Vec::new();
    match node {
        Node::Struct(id) => {
            if let Some(def) = module.struct_def(id) {
                for field in &def.fields {
                    inline_nodes(module, &field.ty, &mut out);
                }
            }
        }
        Node::Enum(id) => {
            if let Some(def) = module.enum_def(id) {
                for ty in def.variants.iter().flat_map(|variant| &variant.fields) {
                    inline_nodes(module, ty, &mut out);
                }
            }
        }
        Node::Record(id) => {
            if let Some(def) = module.record_def(id) {
                for field in &def.fields {
                    inline_nodes(module, &field.ty, &mut out);
                }
            }
        }
        Node::Closure(id) => {
            if let Some(closure) = module.closure_type(id) {
                for ty in &closure.captures {
                    inline_nodes(module, ty, &mut out);
                }
            }
        }
        Node::Row(id) => {
            if let Some(ty) = module.ty(id) {
                inline_nodes(module, ty, &mut out);
            }
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

fn describe(module: &Module, node: Node) -> String {
    match node {
        Node::Struct(id) => match module.struct_def(id) {
            Some(def) => format!("struct #{} '{}'", id.index(), def.name),
            None => format!("struct #{}", id.index()),
        },
        Node::Enum(id) => match module.enum_def(id) {
            Some(def) => format!("enum #{} '{}'", id.index(), def.name),
            None => format!("enum #{}", id.index()),
        },
        Node::Record(id) => match module.record_def(id) {
            Some(def) => format!("record #{} '{}'", id.index(), def.name),
            None => format!("record #{}", id.index()),
        },
        Node::Closure(id) => format!("closure type #{}", id.index()),
        Node::Row(id) => match module.ty(id) {
            Some(ty) => format!("type #{} ({ty})", id.index()),
            None => format!("type #{}", id.index()),
        },
    }
}

/// Every node the module's tables define, in [`Node`] order. A closure-type or
/// type-table row past `u32::MAX` has no id, so nothing can name it and it is
/// no node (the exact enumeration `(0..=u32::MAX).zip(..)`).
fn table_nodes(module: &Module) -> Vec<Node> {
    let mut nodes = BTreeSet::new();
    nodes.extend(module.structs.iter().map(|def| Node::Struct(def.id)));
    nodes.extend(module.enums.iter().map(|def| Node::Enum(def.id)));
    nodes.extend(module.records.iter().map(|def| Node::Record(def.id)));
    nodes.extend(
        (0..=u32::MAX)
            .zip(&module.closure_types)
            .map(|(index, _)| Node::Closure(ClosureTyId::new(index))),
    );
    nodes.extend(
        (0..=u32::MAX)
            .zip(&module.types)
            .map(|(index, _)| Node::Row(TyId::new(index))),
    );
    nodes.into_iter().collect()
}

/// One node's Tarjan state. `index` is `None` until the node is visited.
#[derive(Debug, Clone, Copy, Default)]
struct Mark {
    index: Option<usize>,
    lowlink: usize,
    on_stack: bool,
}

/// Tarjan's strongly-connected-components state over the dense successor
/// lists `succ`. Every per-node access goes through `get` / `get_mut`, and DFS
/// numbers come from the exact range `0..=usize::MAX` (more numbers than a
/// `Vec` can hold nodes), so no index, increment or subtraction can panic.
struct Tarjan<'s> {
    succ: &'s [Vec<usize>],
    marks: Vec<Mark>,
    stack: Vec<usize>,
    numbers: core::ops::RangeInclusive<usize>,
}

/// The explicit call stack: a node and the rest of its edges.
type CallStack<'s> = Vec<(usize, core::slice::Iter<'s, usize>)>;

impl<'s> Tarjan<'s> {
    /// Number `v`, push it, and open its edge iterator on the call stack.
    fn enter(&mut self, v: usize, call: &mut CallStack<'s>) {
        let (Some(number), Some(mark)) = (self.numbers.next(), self.marks.get_mut(v)) else {
            return;
        };
        *mark = Mark {
            index: Some(number),
            lowlink: number,
            on_stack: true,
        };
        self.stack.push(v);
        call.push((v, self.succ.get(v).map_or([].iter(), |edges| edges.iter())));
    }

    /// Lower `v`'s lowlink to `value` if that is smaller.
    fn lower(&mut self, v: usize, value: usize) {
        if let Some(mark) = self.marks.get_mut(v) {
            mark.lowlink = mark.lowlink.min(value);
        }
    }
}

/// Every strongly connected component of `succ` that is a cycle (more than
/// one node, or one node with a self-edge), each sorted.
fn cycle_components(succ: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut tarjan = Tarjan {
        succ,
        marks: vec![Mark::default(); succ.len()],
        stack: Vec::new(),
        numbers: 0..=usize::MAX,
    };
    let mut cycles: Vec<Vec<usize>> = Vec::new();
    for root in 0..succ.len() {
        if tarjan
            .marks
            .get(root)
            .is_none_or(|mark| mark.index.is_some())
        {
            continue;
        }
        let mut call: CallStack<'_> = Vec::new();
        tarjan.enter(root, &mut call);
        while let Some((v, edge)) = call
            .last_mut()
            .map(|(v, edges)| (*v, edges.next().copied()))
        {
            if let Some(w) = edge {
                match tarjan.marks.get(w).copied() {
                    Some(Mark { index: None, .. }) => tarjan.enter(w, &mut call),
                    Some(Mark {
                        index: Some(w_index),
                        on_stack: true,
                        ..
                    }) => tarjan.lower(v, w_index),
                    _ => {}
                }
                continue;
            }
            call.pop();
            let Some(Mark {
                index: Some(v_index),
                lowlink: v_lowlink,
                ..
            }) = tarjan.marks.get(v).copied()
            else {
                continue;
            };
            if let Some(&(parent, _)) = call.last() {
                tarjan.lower(parent, v_lowlink);
            }
            if v_lowlink == v_index {
                let mut component = Vec::new();
                while let Some(w) = tarjan.stack.pop() {
                    if let Some(mark) = tarjan.marks.get_mut(w) {
                        mark.on_stack = false;
                    }
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                let self_edge = succ.get(v).is_some_and(|edges| edges.contains(&v));
                if component.len() > 1 || self_edge {
                    component.sort_unstable();
                    cycles.push(component);
                }
            }
        }
    }
    cycles
}

/// `InlineAggregateCycle` once per by-value containment cycle (see the module
/// doc). Runs on every module; empty for one without a cycle.
pub(super) fn validate_inline_aggregate_cycles(module: &Module) -> Vec<ValidationError> {
    let nodes = table_nodes(module);
    let dense: BTreeMap<Node, usize> = nodes
        .iter()
        .enumerate()
        .map(|(index, node)| (*node, index))
        .collect();
    let succ: Vec<Vec<usize>> = nodes
        .iter()
        .map(|node| {
            successors(module, *node)
                .into_iter()
                .filter_map(|next| dense.get(&next).copied())
                .collect()
        })
        .collect();

    // Dense indices follow `Node` order, so the first member of each sorted
    // component is its least node, and sorting components orders the report.
    // Every member is a dense index into `nodes`, so `get` never misses.
    let mut cycles = cycle_components(&succ);
    cycles.sort_unstable();
    let describe_member = |member: &usize| nodes.get(*member).map(|node| describe(module, *node));
    cycles
        .iter()
        .filter_map(|component| {
            let (head, rest) = component.split_first()?;
            let head = describe_member(head)?;
            let ty = if rest.is_empty() {
                head
            } else {
                let rest: Vec<String> = rest.iter().filter_map(describe_member).collect();
                format!("{head} (cycle through {})", rest.join(", "))
            };
            Some(ValidationError::InlineAggregateCycle { ty })
        })
        .collect()
}
