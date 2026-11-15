// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact canonical-drop spellings; no destructor or proof authority.
#![allow(
    dead_code,
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::ObservedDropGlueIndex;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod render;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    ty: String,
    reason: String,
    name: String,
    errors: Vec<ValidationError>,
}
#[derive(Clone, Copy)]
enum TypeRule {
    Refined,
    Trivial,
}
/// Original S1/S2 refined/trivial Drop and DropInvoke checks, followed by
/// S3 direct registered-glue call/panic/SeqMap refusal in physical order.
/// Uses only original supplied session/site; preserves every earlier error
/// and all partial text through typed operational failure and full cleanup.
/// This constituent does not validate a glue table, resolve a destructor,
/// authenticate a runtime or grant complete module/source/proof authority.
pub(crate) fn validate_module_drop_sites_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(
        1,
        size_of::<State>() + size_of::<Work<'_, '_, O>>() + size_of::<ObservedDropGlueIndex<'_>>(),
    )?;
    let mut state = State::default();
    let result = (|| -> R {
        // The returned index contains only the exact borrowed Module pointer.
        // Its full descriptor transport was admitted before this child call.
        let index = module.drop_glue_index_observed(work.session, work.site)?;
        let result = state.walk(module, &index, &mut work);
        work.step(size_of::<ObservedDropGlueIndex<'_>>().saturating_add(1));
        drop(index);
        work.poll();
        result
    })();
    state.finish(result, &mut work)
}
impl State {
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        work.flat(take(&mut self.ty));
        work.flat(take(&mut self.reason));
        work.flat(take(&mut self.name));
        match result.and_then(|()| work.publication()) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                let _ = retire_validation_errors_observed(
                    take(&mut self.errors),
                    work.session,
                    work.site,
                );
                Err(work.terminal(error))
            }
        }
    }
}
