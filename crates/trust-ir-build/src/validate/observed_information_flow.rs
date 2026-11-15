// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual intra-function value-flow fixed point; no heap-alias or proof authority.

use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Default)]
struct Checking {
    tainted: Vec<u32>,
    operands: Vec<ValueId>,
    errors: Vec<ValidationError>,
    // These fixed fields retain a diagnostic across error-storage admission.
    pending: Option<(u32, u32)>,
}

/// Preserve the ordinary node-only Tainted seeds, forward value-ID fixed point
/// and TrustedSink operand diagnostics, including stored unreachable blocks and
/// duplicate sink operands. Every actual operand collection, membership scan,
/// insertion and retirement uses the caller's original session and site.
///
/// The exhaustive observed operand collector materializes all operands even
/// where the ordinary propagation visitor can stop early. That extra work and
/// storage is charged; no equivalent complexity or physical allocator/time
/// bound is claimed. Empty diagnostics establish only this constituent, not
/// full validation, heap-alias noninterference, source or proof authority.
/// Successful diagnostics and the borrowed input remain caller-owned.
pub fn validate_function_information_flow_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<Checking>() + size_of::<Work<'_, '_, O>>(),
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

impl Checking {
    fn diagnostic<O: ExecutionObserver>(
        &mut self,
        block: u32,
        value: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<(u32, u32)>())?;
        self.pending = Some((block, value));
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        if let Some((block, value)) = self.pending.take() {
            self.errors
                .push(ValidationError::TaintedValueReachesTrustedSink { block, value });
        }
        Ok(())
    }

    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_ids(&mut self.operands);
        work.retire_ids(&mut self.tainted);
        work.retire(self.pending.take());
    }

    fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(error) = self.errors.pop() {
                // This private vector contains only the fixed-field variant
                // constructed above, never any string/type-bearing error.
                work.retire(error);
            }
        }
        work.retire(take(&mut self.errors));
    }
}
