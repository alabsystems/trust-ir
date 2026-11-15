// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Original flow-insensitive borrow structure, not borrow liveness.
use super::{Function, Inst, ObservedValueTypes, Ty, ValidationError, ValueId};
use core::mem::{size_of, take};
use trust_ir::inst::CastOp;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::{Edge, EdgeKind};
mod collect;
mod incoming;
mod retirement;
mod roots;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Clone, Copy)]
enum Definition<'f> {
    Parameter { block: u32, index: usize },
    Node(&'f Inst),
}
type DefRow<'f> = (ValueId, Definition<'f>);
type Incoming = (u32, usize, ValueId);
#[derive(Clone, Copy)]
enum Issue {
    Shared,
    End,
}
#[derive(Default)]
struct State<'f> {
    definitions: Option<Vec<DefRow<'f>>>,
    incoming: Option<Vec<Incoming>>,
    edges: Vec<Edge<'f>>,
    stack: Vec<ValueId>,
    seen: Vec<ValueId>,
    name: String,
    errors: Vec<ValidationError>,
}

/// Exact original borrow-structure diagnostics against the supplied complete
/// last-write type context. This borrows that context and never reconstructs a
/// first-definition map. All duplicate definitions and normal incoming edges
/// participate in the original ANY-shared-root / ALL-direct-borrow questions.
/// The caller's original session/site owns actual traversal, storage and failed
/// output cleanup. Successful errors/input/map disposal remains caller-owned.
/// Flow-sensitive liveness remains a producer obligation; this creates no
/// complete borrow/type/module/source/proof authority or physical time bound.
pub fn validate_function_borrow_structure_observed<O: ExecutionObserver>(
    function: &Function,
    types: &ObservedValueTypes,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.borrows(function, types, &mut work);
    state.finish(result, &mut work)
}

/// Exact original TRust-only prohibition on permission instructions. Other
/// producer spellings, including arbitrary Other strings, remain untouched.
/// This original-session diagnostic constituent does not validate producer or
/// source identity, nor establish a complete function or borrow-check result.
pub fn validate_function_rust_reference_spelling_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.references(function, &mut work);
    state.finish(result, &mut work)
}

fn header<O: ExecutionObserver>(session: &mut ObservedSession<'_, O>, site: ExecutionSite) -> R {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
        })
        .map_err(Into::into)
}
impl State<'_> {
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(work);
        match result.and_then(|()| work.publication()) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                self.retire_errors(work);
                Err(work.terminal(error))
            }
        }
    }
}
