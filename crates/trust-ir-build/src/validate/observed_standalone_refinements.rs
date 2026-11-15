// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Original standalone refinement-surface diagnostics under one caller session.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod predicate;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

const DETAIL: &str = "standalone function validation has no module type table to resolve refinement bases or predicates; validate the containing module instead";

#[derive(Clone, Copy)]
enum Frame<'a> {
    Visit(&'a Ty),
    Children(&'a [Ty]),
}
enum Surface {
    Parameter(usize),
    Instruction(usize),
}
#[derive(Default)]
struct Checking<'a> {
    frames: Vec<Frame<'a>>,
    types: Vec<&'a Ty>,
    location: String,
    detail: String,
    errors: Vec<ValidationError>,
}

/// Report the exact ordinary standalone inline-refinement diagnostics without
/// obtaining module authority. The actual borrowed inline-type collector and
/// iterative type predicate use this original session/site. Only the ordinary
/// Ref/RefMut/PtrConst/PtrMut/Vector/Rc/Tuple containers are followed; table IDs
/// and other nominal/container surfaces remain excluded by that original rule.
/// Each inline field is inspected even after another field contains Refine.
///
/// Refusal supplies no partial diagnostics. Retained local strings, borrowed
/// reference/frame vectors and refused diagnostics are explicitly retired.
/// Successful diagnostics/input disposal remains caller-owned. This provides
/// no module/type/source/proof authority or physical allocator/time guarantee.
pub fn validate_function_standalone_refinements_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<Checking<'_>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = Checking::default();
    let mut work = Work { session, site };
    let result = state.walk(function, &mut work);
    state.retire_scratch(&mut work);
    let result = result.and_then(|()| work.publication());
    match result {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            state.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}

impl Checking<'_> {
    fn diagnostic<O: ExecutionObserver>(
        &mut self,
        name: &str,
        block: u32,
        surface: Surface,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("function '", &mut self.location)?;
        work.text(name, &mut self.location)?;
        work.text("' bb", &mut self.location)?;
        work.number(block as u128, &mut self.location)?;
        match surface {
            Surface::Parameter(index) => {
                work.text(" param ", &mut self.location)?;
                work.number(index as u128, &mut self.location)?;
            }
            Surface::Instruction(index) => {
                work.text(" instruction ", &mut self.location)?;
                work.number(index as u128, &mut self.location)?;
            }
        }
        work.text(DETAIL, &mut self.detail)?;
        // Both completed or partial strings stay in Checking until every
        // remaining fallible storage/construction admission has succeeded.
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::RefinementTypeInvalid {
            location: take(&mut self.location),
            detail: take(&mut self.detail),
        });
        Ok(())
    }
}
