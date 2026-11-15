// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual vector structural checks, preserving every original diagnostic.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod locations;
mod retirement;
mod storage;
mod tables;
#[cfg(test)]
mod tests;
mod types;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Clone, Copy)]
enum Frame<'a> {
    Visit(&'a Ty),
    Children(&'a [Ty]),
}
#[derive(Clone, Copy)]
enum Context {
    Block(u32),
    Module,
}
enum Location<'a> {
    Type(usize),
    SignatureParameter(usize, usize),
    SignatureReturn(usize, usize),
    Global(&'a str),
    Drop(usize),
    Struct(&'a str, &'a str),
    Record(&'a str, &'a str),
    Enum(&'a str, &'a str, usize),
    Capture(usize, usize),
}
#[derive(Default)]
struct State<'a> {
    frames: Vec<Frame<'a>>,
    location: String,
    pending_location: String,
    pending_ty: String,
    pending_reason: String,
    errors: Vec<ValidationError>,
}

/// The ordinary block-scoped vector structural check, including every
/// duplicate report and recursion into invalid elements. This borrows only
/// the supplied type and uses the caller's original session/site throughout.
/// Successful errors/input disposal remains caller-owned; no full function,
/// module, source or proof authority follows from this diagnostic result.
pub fn validate_vector_type_observed<O: ExecutionObserver>(
    ty: &Ty,
    block: u32,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.check(ty, Context::Block(block), &mut work);
    state.finish(result, &mut work)
}

/// Exact ordinary module vector surfaces, including globals BEFORE drop glue.
/// Functions, inline instructions, dialect attrs and nominal IDs are not added
/// to this constituent. Actual traversal, bounded diagnostic copies and the
/// observed type formatter share this original caller session/site. Refusal
/// retires owned partials and returns no smaller diagnostic list.
pub fn validate_module_vector_types_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state
        .tables(module, &mut work)
        .and_then(|()| state.aggregates(module, &mut work));
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
    fn report<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        reason: &'static str,
        context: Context,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if let Context::Module = context {
            work.text(&self.location, &mut self.pending_location)?;
        }
        // Successful helper output is immediately retained before any next
        // fallible operation. Its failed output is retired by that helper.
        work.admit(1, size_of::<String>())?;
        self.pending_ty = ty.display_observed(work.session, work.site)?;
        work.text(reason, &mut self.pending_reason)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        // No admission follows the owned moves into the retained error row.
        let error = match context {
            Context::Block(block) => ValidationError::InvalidVectorType {
                block,
                ty: take(&mut self.pending_ty),
                reason: take(&mut self.pending_reason),
            },
            Context::Module => ValidationError::InvalidModuleVectorType {
                location: take(&mut self.pending_location),
                ty: take(&mut self.pending_ty),
                reason: take(&mut self.pending_reason),
            },
        };
        self.errors.push(error);
        Ok(())
    }

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
