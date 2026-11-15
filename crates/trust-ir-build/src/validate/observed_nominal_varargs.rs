// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual variadic nominal-transport refusal rule, not call acceptance.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::ObservedNominalTypeReachability;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
const HANDLE: &str = "a variadic argument slot has no exact type contract, so it cannot carry an opaque runtime handle";
const DIALECT: &str = "variadic arguments have no exact semantic type contract; nominal dialect values require explicit legalization";
#[derive(Default)]
struct State {
    location: String,
    detail: String,
    errors: Vec<ValidationError>,
}
#[derive(Clone, Copy)]
enum Family {
    Handle,
    Dialect,
}
/// Preserve original fixed-prefix skip, unknown-value skip and handle-before-
/// dialect refusal order. Actual argument rows, last-definition value lookup
/// and full nominal queries share the supplied original session/site. Missing
/// optional summary means the original no-nominal lane; callers must derive
/// that choice from the mandatory complete census, never an observed stop.
///
/// This is only a diagnostic constituent, never type/signature/call/module/
/// proof/source authority. All partial strings and prior errors stay owned
/// through final transfer and exhaustively retire on failure. Caller-owned
/// value map/summary/original inputs and physical hard bounds remain OPEN.
pub(super) fn validate_nominal_varargs_observed<O: ExecutionObserver>(
    args: &[ValueId],
    fixed_count: usize,
    value_types: &ObservedValueTypes,
    nominal_types: Option<&ObservedNominalTypeReachability<'_>>,
    location: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(
        args,
        fixed_count,
        value_types,
        nominal_types,
        location,
        &mut work,
    );
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State {
    fn run<O: ExecutionObserver>(
        &mut self,
        args: &[ValueId],
        fixed_count: usize,
        value_types: &ObservedValueTypes,
        nominal_types: Option<&ObservedNominalTypeReachability<'_>>,
        location: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            1,
            size_of::<Option<&ObservedNominalTypeReachability<'_>>>() + size_of::<usize>(),
        )?;
        let Some(nominal_types) = nominal_types else {
            return Ok(());
        };
        let mut at = fixed_count;
        while let Some(value) = work.at(args, at)? {
            work.admit(1, size_of::<ValueId>())?;
            let value = *value;
            if let Some(ty) = value_types.get_observed(value, work.session, work.site)? {
                if nominal_types.contains_handle_observed(ty, work.session, work.site)? {
                    self.error(Family::Handle, location, work)?;
                } else if nominal_types.contains_dialect_observed(ty, work.session, work.site)? {
                    self.error(Family::Dialect, location, work)?;
                }
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn error<O: ExecutionObserver>(
        &mut self,
        family: Family,
        location: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(location, &mut self.location)?;
        work.admit(1, size_of::<&str>())?;
        work.text(
            match family {
                Family::Handle => HANDLE,
                Family::Dialect => DIALECT,
            },
            &mut self.detail,
        )?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        let location = take(&mut self.location);
        let detail = take(&mut self.detail);
        self.errors.push(match family {
            Family::Handle => ValidationError::InvalidHandleUse { location, detail },
            Family::Dialect => ValidationError::InvalidDialectType { location, detail },
        });
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.location));
        work.flat(take(&mut self.detail));
    }
}
