// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact post-replay DATA checks. No public input or replay/authority constructor.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
mod composition;
mod cycles;
mod duplicate;
mod islands;
mod messages;
mod state;
#[cfg(test)]
mod tests;
use state::Post;
struct Content {
    scope: u32,
    bytes: Vec<u8>,
    ids: Vec<u32>,
}
#[derive(Default)]
struct Scratch {
    reason: String,
    edges: Vec<(usize, usize)>,
    named: Vec<FuncId>,
    parents: Vec<(usize, usize)>,
    queue: Vec<usize>,
    path: Vec<usize>,
    content: Vec<Content>,
    pending_content: Option<Vec<u8>>,
}
/// This private function takes the actual producer's private replay outcomes.
/// It cannot turn candidate status/evidence into a replay outcome or currency.
/// The full replay builder remains a mandatory, unfinished dependency.
pub(super) fn checks<O: ExecutionObserver>(
    module: &Module,
    catalog: &ModuleFunctionCatalog<'_>,
    tv: &[TvRechecked],
    theorems: &[IslandTheoremRechecked],
    v8: &[&ProofObligation],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut w = Work { session, site };
    w.admit(1, size_of::<Post>())?;
    let mut state = Post::default();
    let result = (|| -> R {
        w.admit(8, size_of::<bool>())?;
        if !core::ptr::eq(catalog.source_module(), module) {
            return Err(ObservedValueError::InvalidRange);
        }
        state.composition(module, catalog, tv, &mut w)?;
        state.bridge(theorems, tv, &mut w)?;
        state.names(theorems, &mut w)?;
        state.duplicates(v8, catalog, &mut w)
    })();
    state.finish(result, &mut w)
}
