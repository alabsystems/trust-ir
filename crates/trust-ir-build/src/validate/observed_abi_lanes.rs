// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual structural ABI-lane solver and original module-local memo.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use std::sync::Arc;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::shape::TyLayoutShape;
use trust_ir::ty::{EnumDef, EnumTagEncoding, FieldDef};
use trust_ir::value::{EnumId, StructId};
use trust_ir::{LayoutError, LayoutTable};
mod engine;
mod memo;
mod resume;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy, PartialEq, Eq)]
enum Node {
    Struct(StructId),
    Enum(EnumId),
}
#[derive(Clone, Copy)]
enum Slot {
    Open,
    Counted(Option<usize>),
}
#[derive(Clone, Copy)]
enum Rule {
    Untagged { variant: usize },
    Niche { dataful: usize },
    Direct { widest: usize },
}
#[derive(Clone, Copy)]
enum Owner {
    Inline,
    Struct(StructId),
    Variant,
}
#[derive(Clone, Copy)]
enum Fields<'a> {
    Types(&'a [Ty]),
    Struct(&'a [FieldDef]),
}
#[derive(Clone, Copy)]
enum Frame<'a> {
    Sum {
        fields: Fields<'a>,
        next: usize,
        lanes: usize,
        owner: Owner,
    },
    Enum {
        id: EnumId,
        def: &'a EnumDef,
        rule: Rule,
        counted: usize,
    },
}
#[derive(Clone, Copy)]
enum Action<'a> {
    Enter(&'a Ty),
    Return(Option<usize>),
    Sum(Fields<'a>, Owner),
    NextVariant,
    Summed(Owner, Option<usize>),
}
#[derive(Default)]
struct State<'a> {
    frames: Vec<Frame<'a>>,
    layout: Option<Result<Arc<TyLayoutShape>, LayoutError>>,
}
/// Private derived DATA for this exact immutable module, not layout, type,
/// producer/ABI/source/module/proof authority. The actual full caller owns it
/// only within one original operation/session and consumes it before return.
/// A paid linear Copy-row memo replaces the ordinary entropy-initialized
/// HashMap. Successful nominal counts are reused only in this same context;
/// any outer operational failure drains ALL memo rows, including open paths.
pub(super) struct ObservedAbiLanes<'m> {
    module: &'m Module,
    nodes: Vec<(Node, Slot)>,
}
impl<'m> ObservedAbiLanes<'m> {
    pub(super) fn new_observed<O: ExecutionObserver>(
        layouts: &LayoutTable<'m>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        let mut w = Work { session, site };
        w.admit(1, size_of::<Self>() + size_of::<Work<'_, '_, O>>())?;
        let mut out = Self {
            module: layouts.module(),
            nodes: Vec::new(),
        };
        if let Err(error) = w.publication(size_of::<Self>()) {
            out.retire_nodes(&mut w);
            return Err(w.terminal(error));
        }
        Ok(out)
    }
    /// Original complete explicit-stack lane count. Semantic missing, cycle or
    /// usize overflow stays None; an observer/allocation failure is outer Err,
    /// never None. The table MUST borrow this same module. Actual layout child,
    /// memo/frame growth, lookup, source rows and full cleanup use the original
    /// session/site; no renewed owner/grant/deadline/TLS/fuel or opaque prewalk.
    /// Borrowed field views and derived niche order remove only redundant
    /// pointer/index collections, preserving original visit/short-circuit order.
    /// Physical std/allocator/deallocator/OOM/panic/unwind/RSS/hard-time, caller
    /// input/context disposal and mandatory type/ABI/source validation stay OPEN.
    pub(super) fn lanes_observed<'a, O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'m>,
        ty: &'a Ty,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<usize>>
    where
        'm: 'a,
    {
        let mut w = Work { session, site };
        if let Err(error) = w.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>()) {
            self.retire_nodes(&mut w);
            return Err(w.terminal(error));
        }
        let mut state = State::default();
        let result = (|| {
            w.admit(1, size_of::<bool>())?;
            if !core::ptr::eq(self.module, layouts.module()) {
                return Err(ObservedValueError::InvalidRange);
            }
            state.run(self, layouts, ty, &mut w)
        })();
        let cleanup = state.retire(&mut w);
        match result.and_then(|count| {
            cleanup?;
            w.publication(size_of::<Option<usize>>())?;
            Ok(count)
        }) {
            Ok(count) => Ok(count),
            Err(error) => {
                self.retire_nodes(&mut w);
                Err(w.terminal(error))
            }
        }
    }
    pub(super) fn retire_observed<O: ExecutionObserver>(
        mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut w = Work { session, site };
        self.retire_nodes(&mut w);
        w.publication(0)
    }
    fn retire_nodes<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.rows(take(&mut self.nodes));
    }
}
impl State<'_> {
    fn retire_layout<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        w.step(size_of::<Option<Result<Arc<TyLayoutShape>, LayoutError>>>().saturating_add(1));
        let result = match self.layout.take() {
            Some(Ok(shape)) => shape.retire_arc_observed(w.session, w.site),
            Some(Err(error)) => error.retire_observed(w.session, w.site),
            None => Ok(()),
        };
        w.poll();
        result.map_err(|error| w.terminal(error))
    }
    fn retire<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        let result = self.retire_layout(w);
        w.rows(take(&mut self.frames));
        result
    }
}
