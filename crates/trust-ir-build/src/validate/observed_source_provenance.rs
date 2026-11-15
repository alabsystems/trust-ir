// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original structural source-provenance checks, not compiler authority.
use super::*;
use core::mem::{size_of, take};
use trust_ir::analysis::DominatorTree;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::{SourceLoopProvenance, SourceProvenance};
mod bindings;
mod diagnostics;
mod loops;
mod spelling;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
type Place = (u8, u32, u32);
#[derive(Default)]
struct State<'f> {
    detail: String,
    pending: String,
    errors: Vec<ValidationError>,
    dominators: Option<DominatorTree>,
    edges: Vec<trust_ir::Edge<'f>>,
    loop_hir: Vec<u32>,
    headers: Vec<u32>,
    local_hir: Vec<u32>,
    local_places: Vec<SourcePlace>,
    global_names: Vec<(u32, &'f str, Place)>,
    global_places: Vec<(Place, u32)>,
}
/// Complete original validate_source_provenance diagnostic constituent, with
/// actual binding/body digest construction, first entry/header lookup, original
/// natural-loop dominance question and every ordered source binding check.
/// The supplied module context must be the original containing module, just
/// like the ordinary caller; this diagnostic API brands no source authority.
/// Compiler-owned HIR equality and all other function/module/proof checks are
/// separate mandatory caller duties. Successful output/input disposal is owned
/// by that caller. Physical allocator/stdlib/panic/hard-time limits are separate.
///
/// Every actual traversal/allocation/comparison/spelling and failed output
/// retirement uses this same original session/site, without an opaque ordinary
/// validator or a fresh owner/grant/deadline. Typed refusal returns no smaller
/// diagnostic list. Borrowing immutable map names omits only discarded clones.
pub fn validate_function_source_provenance_observed<O: ExecutionObserver>(
    function: &Function,
    module: Option<&Module>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.walk(function, module, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State<'_> {
    fn retire_edges<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.session
                .retirement_step(work.site, size_of::<trust_ir::Edge<'_>>().saturating_add(1));
            if self.edges.pop().is_none() {
                break;
            }
        }
        work.flat(take(&mut self.edges));
    }
    fn retire_local<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.rows(&mut self.local_hir);
        work.rows(&mut self.local_places);
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_text(&mut self.detail);
        work.retire_text(&mut self.pending);
        self.retire_edges(work);
        self.retire_local(work);
        work.rows(&mut self.loop_hir);
        work.rows(&mut self.headers);
        work.rows(&mut self.global_names);
        work.rows(&mut self.global_places);
        work.session.retirement_step(
            work.site,
            size_of::<Option<DominatorTree>>().saturating_add(1),
        );
        if let Some(tree) = self.dominators.take() {
            let _ = tree.retire_observed(work.session, work.site);
        }
    }
}
