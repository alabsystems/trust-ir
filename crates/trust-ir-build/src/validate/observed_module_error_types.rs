// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact module poison-type occurrences and original global alignment checks.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod functions;
mod locations;
mod retirement;
mod storage;
mod tables;
#[cfg(test)]
mod tests;
mod types;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
const EXPECTED: &str = "a well-formed type (Ty::Error is producer-internal and never module-legal)";

#[derive(Clone, Copy)]
enum Frame<'a> {
    Visit(&'a Ty),
    Children(&'a [Ty]),
}
#[derive(Clone, Copy)]
enum Buffer {
    Base,
    Attribute,
}
enum Location<'a> {
    Type(usize),
    SignatureParameter(usize, usize),
    SignatureReturn(usize, usize),
    Drop(usize),
    Global(&'a str),
    Struct(&'a str, &'a str),
    Record(&'a str, &'a str),
    Enum(&'a str, &'a str, usize),
    Capture(usize, usize),
    Parameter(&'a str, u32, u32),
    Instruction(&'a str, u32, usize, &'static str),
}
#[derive(Default)]
struct State<'a> {
    frames: Vec<Frame<'a>>,
    types: Vec<&'a Ty>,
    location: String,
    attribute: String,
    pending_location: String,
    pending_expected: String,
    pending_actual: String,
    errors: Vec<ValidationError>,
}

/// Preserve every ordinary inline Ty::Error occurrence, in module surface and
/// depth-first child order, plus the original per-global alignment diagnostic.
/// Only the original seven recursive containers and exact original surfaces
/// are walked. Instruction inline fields use the actual observed collector;
/// top-level dialect Ty attributes remain a separate original-order traversal.
///
/// All traversal, diagnostic text/storage and rejected-output retirement use
/// this original caller session/site. Refusal returns no partial diagnostics.
/// Successful output/input disposal is caller-owned. These diagnostics confer
/// no complete module/type/source/proof authority or physical time guarantee.
pub fn validate_module_error_types_observed<O: ExecutionObserver>(
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
    let result = state
        .tables(module, &mut work)
        .and_then(|()| state.aggregates(module, &mut work))
        .and_then(|()| state.functions(module, &mut work));
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

impl State<'_> {
    fn poison<O: ExecutionObserver>(&mut self, location: Buffer, work: &mut Work<'_, '_, O>) -> R {
        let source = match location {
            Buffer::Base => &self.location,
            Buffer::Attribute => &self.attribute,
        };
        work.text(source, &mut self.pending_location)?;
        work.text(EXPECTED, &mut self.pending_expected)?;
        work.text("error", &mut self.pending_actual)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        // All three owned strings remain in State until every fallible
        // admission succeeds; no fallible step follows their retained move.
        self.errors.push(ValidationError::ConstTypeMismatch {
            location: take(&mut self.pending_location),
            expected: take(&mut self.pending_expected),
            actual: take(&mut self.pending_actual),
        });
        Ok(())
    }

    fn alignment<O: ExecutionObserver>(
        &mut self,
        name: &str,
        align: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(name, &mut self.pending_location)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::GlobalAlignInvalid {
            global: take(&mut self.pending_location),
            align,
        });
        Ok(())
    }

    fn end_location<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.retire(take(&mut self.location));
        work.admit(1, 0)
    }
}
