// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original blank-module and Trust-internal spec namespace constituents.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::{SpecEnforcementMode, SpecModule, SpecOrigin};
mod keys;
mod namespace;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Case {
    Exact,
    AsciiInsensitive,
}
#[derive(Default)]
struct State {
    name: String,
    detail: String,
    errors: Vec<ValidationError>,
}
/// Original trim-is-empty module name check at the start of spec semantics.
/// Separate from reserved-name checks so intervening structural/typed spec
/// stages keep their original global diagnostic order.
pub fn validate_module_name_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = (|| {
        if work.trim(&module.name)?.is_empty() {
            work.reserve(&mut state.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            state.errors.push(ValidationError::BlankModuleName);
        }
        Ok(())
    })();
    state.finish(result, &mut work)
}
/// Exact reserved-name membership, disclosure shape and canonical Clean fn:N
/// key rules. The key's body/ID binding authenticates no disclosure CONTENT;
/// those rows remain unauthenticated producer statements as before.
pub fn validate_reserved_spec_module_names_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.run(module, &mut work);
    state.finish(result, &mut work)
}
fn header<O: ExecutionObserver>(session: &mut ObservedSession<'_, O>, site: ExecutionSite) -> R {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
        })
        .map_err(Into::into)
}
impl State {
    fn begin<O: ExecutionObserver>(&mut self, spec: &SpecModule, work: &mut Work<'_, '_, O>) -> R {
        work.admit(2, 0)?;
        if self.name.capacity() != 0 || self.detail.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text(&spec.name, &mut self.name)
    }
    fn push<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::ReservedSpecModuleName {
            name: take(&mut self.name),
            detail: take(&mut self.detail),
        });
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_text(&mut self.name);
        work.retire_text(&mut self.detail);
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
// Same supplied original owner/site. No namespace rule authenticates a producer
// or mints spec/source/proof authority. Full spec/module/native/MC composition,
// successful caller/input disposal and physical std/allocator/deallocator/OOM/
// panic/unwind/RSS/hard100ms remain OPEN; no new grant/deadline/TLS/fuel/flag.
