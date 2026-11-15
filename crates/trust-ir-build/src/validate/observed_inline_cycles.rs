// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! The complete inline-containment SCC diagnostic under the original observer.
//! Same iterative Tarjan algorithm as `inline_cycles.rs`; derived graph data
//! and diagnostics confer no layout, validation or proof authority.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod describe;
mod graph;
mod storage;
mod tarjan;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

// Exactly the ordinary discriminant/id ordering used to choose report heads.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Struct(u32),
    Enum(u32),
    Record(u32),
    Closure(u32),
    Row(u32),
}
#[derive(Clone, Copy, Default)]
struct Mark {
    index: Option<usize>,
    lowlink: usize,
    on_stack: bool,
}
#[derive(Clone, Copy)]
struct Frame {
    node: usize,
    next: usize,
}
#[derive(Default)]
struct State<'m> {
    nodes: Vec<Node>,
    pending: Vec<&'m Ty>,
    edges: Vec<usize>,
    successors: Vec<Vec<usize>>,
    marks: Vec<Mark>,
    stack: Vec<usize>,
    calls: Vec<Frame>,
    component: Vec<usize>,
    cycles: Vec<Vec<usize>>,
    number: usize,
    text: String,
    render: String,
    errors: Vec<ValidationError>,
}

/// Exact ordinary whole cycle diagnostics, including raw names and malformed
/// zero-length inline carriers. Missing ids remain the dangling-type pass's
/// responsibility. Actual module getters' indexed-then-first fallback is
/// reproduced with admitted reads; no ordinary graph/SCC/formatting prewalk.
/// All graph, traversal and complete text state remains held through later
/// admissions and consuming retirement. Caller supplies the original session,
/// site and limits; this creates none and consumes no instruction fuel.
/// Paid linear maps/insertion sorting can be quadratic and remain refusable.
/// Physical std/allocator/deallocator/stack/OOM/unwind/RSS/callback/preemption
/// and hard-time bounds are separate; full module/proof/source checks remain.
pub(super) fn validate_inline_aggregate_cycles_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut w = Work { session, site };
    w.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = (|| {
        state.graph(module, &mut w)?;
        state.components(&mut w)?;
        state.describe_cycles(module, &mut w)
    })();
    state.retire_scratch(&mut w);
    match result.and_then(|()| w.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
            Err(w.terminal(error))
        }
    }
}
impl State<'_> {
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.rows(take(&mut self.nodes));
        w.rows(take(&mut self.pending));
        w.rows(take(&mut self.edges));
        w.rows(take(&mut self.marks));
        w.rows(take(&mut self.stack));
        w.rows(take(&mut self.calls));
        w.rows(take(&mut self.component));
        for store in [&mut self.successors, &mut self.cycles] {
            loop {
                w.step(size_of::<Option<Vec<usize>>>().saturating_add(1));
                let Some(row) = store.pop() else { break };
                w.rows(row);
            }
            w.step(size_of::<Vec<Vec<usize>>>().saturating_add(1));
            drop(take(store));
            w.poll();
        }
        w.flat(take(&mut self.text));
        w.flat(take(&mut self.render));
    }
}
