// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original per-enum diagnostic order, using actual observed stages.
use super::observed_enum_layout_encoding::{
    validate_enum_layout_encoding_observed, validate_enum_layout_prelude_observed,
};
use super::observed_enum_layout_fields::validate_enum_layout_fields_observed;
use super::*;
use core::mem::{size_of, take};
use std::vec::IntoIter;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    batch: Option<IntoIter<ValidationError>>,
    pending: Option<ValidationError>,
    errors: Vec<ValidationError>,
}
/// Complete original physical enum declaration/descriptor block: each row's
/// duplicate/discriminant/name checks, lane/global prelude, field checks, then
/// encoding clauses, before the next row. Every constituent receives the same
/// original session/site. This yields diagnostics, never an authority token or
/// a whole-module/source/proof verdict; no unobserved validator callback runs.
pub fn validate_module_enums_observed<O: ExecutionObserver>(
    module: &Module,
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
    let result = state.run(module, &mut work);
    state.finish(result, &mut work)
}
impl State {
    fn run<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        let mut index = 0;
        while let Some(enm) = work.at(&module.enums, index)? {
            self.ready(work)?;
            self.batch = Some(
                validate_enum_declaration_observed(module, index, work.session, work.site)?
                    .into_iter(),
            );
            self.merge(work)?;
            work.admit(1, 0)?;
            if let Some(layout) = &enm.layout {
                self.ready(work)?;
                let (batch, align) = validate_enum_layout_prelude_observed(
                    module,
                    enm,
                    layout,
                    work.session,
                    work.site,
                )?;
                self.batch = Some(batch.into_iter());
                self.merge(work)?;
                self.ready(work)?;
                self.batch = Some(
                    validate_enum_layout_fields_observed(
                        module,
                        enm,
                        layout,
                        work.session,
                        work.site,
                    )?
                    .into_iter(),
                );
                self.merge(work)?;
                self.ready(work)?;
                self.batch = Some(
                    validate_enum_layout_encoding_observed(
                        module,
                        enm,
                        layout,
                        align,
                        work.session,
                        work.site,
                    )?
                    .into_iter(),
                );
                self.merge(work)?;
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
    fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        // Admit fixed transport headers before any constituent can return an
        // owned diagnostic vector. Assignment/into_iter then cannot allocate.
        work.admit(
            3,
            size_of::<IntoIter<ValidationError>>()
                + size_of::<Vec<ValidationError>>()
                + size_of::<Option<u64>>(),
        )?;
        if self.batch.is_some() || self.pending.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn merge<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        loop {
            work.admit(1, size_of::<Option<ValidationError>>())?;
            if self.pending.is_some() {
                return Err(ObservedValueError::InvalidRange);
            }
            // Preserve the next owning error before output reserve/move.
            self.pending = self
                .batch
                .as_mut()
                .ok_or(ObservedValueError::InvalidRange)?
                .next();
            if self.pending.is_none() {
                break;
            }
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            if let Some(error) = self.pending.take() {
                self.errors.push(error);
            } else {
                return Err(ObservedValueError::InvalidRange);
            }
        }
        self.retire_empty_batch(work);
        work.admit(1, 0)
    }
    fn retire_empty_batch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<IntoIter<ValidationError>>>().saturating_add(1));
        drop(self.batch.take());
        work.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<ValidationError>>().saturating_add(1));
        if let Some(error) = self.pending.take() {
            let _ = retire_validation_error_observed(error, work.session, work.site);
        }
        loop {
            work.step(size_of::<Option<ValidationError>>().saturating_add(1));
            let error = self.batch.as_mut().and_then(Iterator::next);
            let Some(error) = error else {
                break;
            };
            let _ = retire_validation_error_observed(error, work.session, work.site);
        }
        self.retire_empty_batch(work);
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
// Every child batch, pending error and collected prefix remains owned until
// successful publication or complete original-context consuming retirement.
// Full module/native/source/HIR/proof/MC, old layout Work internals, successful
// caller/input disposal and physical std/allocator/deallocator/OOM/panic/unwind/
// RSS/hard100ms remain OPEN. No new owner/grant/deadline/TLS/fuel/flag/fallback.
