// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original physical enum declaration checks, one row at its original stage.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::ty::EnumDef;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Part<'a> {
    Text(&'a str),
    Number(u128),
}
#[derive(Default)]
struct State {
    location: String,
    expected: String,
    actual: String,
    values: Vec<i128>,
    errors: Vec<ValidationError>,
}
/// Original duplicate-ID, effective-discriminant/canonical-tag and variant
/// field-name diagnostics for exactly the physical row at `index`. This per-row
/// constituent lets its enclosing pass retain interleaving with that row's
/// descriptor checks. An invalid index is an outer refusal, never acceptance.
/// It is diagnostic-only: no module/layout/source/proof or native authority.
pub fn validate_enum_declaration_observed<O: ExecutionObserver>(
    module: &Module,
    index: usize,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.run(module, index, &mut work);
    state.finish(result, &mut work)
}
impl State {
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(work);
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
    fn message<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        variant: Option<(usize, &str)>,
        expected: &[Part<'_>],
        actual: &[Part<'_>],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.location.capacity() != 0
            || self.expected.capacity() != 0
            || self.actual.capacity() != 0
        {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text("enum.", &mut self.location)?;
        work.number(u128::from(enm.id.index()), &mut self.location)?;
        work.text(" (", &mut self.location)?;
        work.text(&enm.name, &mut self.location)?;
        work.text(")", &mut self.location)?;
        if let Some((index, name)) = variant {
            work.text(" variant ", &mut self.location)?;
            work.number(index as u128, &mut self.location)?;
            work.text(" (", &mut self.location)?;
            work.text(name, &mut self.location)?;
            work.text(")", &mut self.location)?;
        }
        work.parts(expected, &mut self.expected)?;
        work.parts(actual, &mut self.actual)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::ConstTypeMismatch {
            location: take(&mut self.location),
            expected: take(&mut self.expected),
            actual: take(&mut self.actual),
        });
        Ok(())
    }
    fn retire_values<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.step(size_of::<Option<i128>>().saturating_add(1));
            if self.values.pop().is_none() {
                break;
            }
        }
        work.step(size_of::<Vec<i128>>().saturating_add(1));
        drop(take(&mut self.values));
        work.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_values(work);
        work.retire_text(&mut self.location);
        work.retire_text(&mut self.expected);
        work.retire_text(&mut self.actual);
    }
}
// Same supplied original owner/site throughout. Successful output/input disposal,
// full validator/native orchestration and physical allocator/deallocator/OOM/
// panic/unwind/RSS/stdlib/hard100ms remain OPEN. No new grant/deadline/TLS/fuel.
