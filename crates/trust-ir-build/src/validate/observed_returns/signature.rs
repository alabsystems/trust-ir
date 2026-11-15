// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Default)]
struct Getter {
    name: String,
    error: Option<ValidationError>,
}
/// Actual module-row lookup and get_func_ty's full original missing-type
/// diagnostic. Borrowed success is DATA, never validated signature authority.
/// Caller resolves once in the original cross-function group, retains complete
/// returned semantic error before the next fee, and skips return checks only
/// for that already-reported original absence. Outer stop is never absence.
pub(in crate::validate) fn function_signature_observed<'m, O: ExecutionObserver>(
    module: &'m Module,
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Result<&'m FuncTy, ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<Getter>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = Getter::default();
    let result = state.run(module, function, &mut work);
    work.flat(take(&mut state.name));
    match result.and_then(|signature| {
        work.publication_value(size_of::<Result<&FuncTy, ValidationError>>())?;
        Ok(signature)
    }) {
        Ok(Some(signature)) => Ok(Ok(signature)),
        Ok(None) => match state.error.take() {
            Some(error) => Ok(Err(error)),
            None => Err(ObservedValueError::InvalidRange),
        },
        Err(error) => {
            work.step(size_of::<Option<ValidationError>>() + 1);
            if let Some(error) = state.error.take() {
                let _ = retire_validation_error_observed(error, work.session, work.site);
            }
            work.poll();
            Err(work.terminal(error))
        }
    }
}
impl Getter {
    fn run<'m, O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'m FuncTy>> {
        if let Some(signature) = work.at(&module.func_types, function.ty.as_usize())? {
            return Ok(Some(signature));
        }
        work.text(&function.name, &mut self.name)?;
        work.admit(
            1,
            size_of::<ValidationError>() + size_of::<Option<ValidationError>>(),
        )?;
        self.error = Some(ValidationError::FuncTypeNotFound {
            func_name: take(&mut self.name),
            func_ty_id: function.ty.index(),
        });
        Ok(None)
    }
}
