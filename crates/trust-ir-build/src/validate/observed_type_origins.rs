// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact in-module split/refuse nominal-origin uniqueness constituent.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::proof::{ProofDigest, ProofDigestAlgorithm};
use trust_ir::ty::TypeOrigin;
mod origin;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
struct Key<'m> {
    origin: &'m TypeOrigin,
    table: &'static str,
    name: &'m str,
}
#[derive(Default)]
struct State<'m> {
    keys: Vec<Key<'m>>,
    seen: Vec<usize>,
    origin: String,
    first: String,
    second: String,
    errors: Vec<ValidationError>,
}
/// Preserve the original keyed definition order (structs then enums), the
/// first holder of each whole key and every later duplicate. No origin admits
/// a type, unkeyed rows remain absent, and structure is irrelevant to this
/// original within-module uniqueness rule. Full variant/field/digest identity
/// and exact original Display spelling are traversed under the supplied same
/// original session/site, without opaque derived equality/clone/format walks.
///
/// All partial names/rendering and complete diagnostics remain owned across
/// fallible reserves/polls and are consumed on refusal. No shorter list,
/// authority, new owner/grant/deadline/TLS/fuel/flag or accepting fallback.
/// Borrowed linear indexes charge actual work; no old tree-complexity claim.
/// Successful output/input disposal and physical scalar-stdlib/allocator/
/// deallocator/OOM/panic/unwind/RSS/hard100ms remain OPEN, as do full module/
/// linked source/proof authority/native orchestration and MC adoption.
pub fn validate_module_type_origins_observed<O: ExecutionObserver>(
    module: &Module,
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
    let result = state.run(module, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication(1, size_of::<Vec<ValidationError>>())) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State<'_> {
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_text(take(&mut self.origin));
        work.retire_text(take(&mut self.first));
        work.retire_text(take(&mut self.second));
        retire_fixed(take(&mut self.keys), work);
        retire_fixed(take(&mut self.seen), work);
    }
}
fn retire_fixed<T: Copy, O: ExecutionObserver>(mut rows: Vec<T>, work: &mut Work<'_, '_, O>) {
    loop {
        work.step(size_of::<Option<T>>().saturating_add(1));
        let Some(value) = rows.pop() else {
            break;
        };
        work.fixed(value);
    }
    work.step(size_of::<Vec<T>>().saturating_add(1));
    drop(rows);
    work.poll();
}
