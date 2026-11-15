// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original byval/sret signature placement diagnostics.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    name: String,
    errors: Vec<ValidationError>,
}
/// Original physical function/attribute rule. Only exact pointer spellings
/// satisfy byval/sret; refinements are not newly peeled here. Dangling function
/// types remain the other validator's defect. No ABI/module/proof authority.
pub fn validate_module_param_abi_attrs_observed<O: ExecutionObserver>(
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
    fn issue<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        index: usize,
        reason: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.name.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text(&function.name, &mut self.name)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::ParamAbiAttrInvalid {
            func_name: take(&mut self.name),
            param_index: index,
            reason,
        });
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_text(&mut self.name);
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
// Same original supplied session/site; full ABI/module/native orchestration,
// caller/input disposal and physical std/allocator/deallocator/OOM/panic/
// unwind/RSS/hard100ms remain OPEN. No new grant/deadline/TLS/fuel/flag/fallback.
