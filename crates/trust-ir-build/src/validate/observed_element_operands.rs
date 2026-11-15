// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact element operand rules under the caller's original observation owner.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod diagnostics;
mod index;
mod operands;
mod storage;
mod table;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Default)]
struct State {
    op: String,
    reason: String,
    spelling: String,
    errors: Vec<ValidationError>,
}

/// Only ExtractElement/InsertElement are admitted; another family is an
/// operational InvalidRange, never a clean validation result. The complete
/// inferred map and constant rows must correspond to the original function
/// and selected module context. Constant rows represent last qualifying
/// integer Const definitions; non-Const redefinitions do not remove a row.
/// A reverse lookup preserves last-row semantics if duplicate rows are supplied.
///
/// This is the four original element helpers only. Vector well-formedness,
/// refinement consumption, constant validity and full type-pass ordering are
/// separate caller responsibilities. Missing rows retain the original local
/// exemptions; no absence establishes validation/source/proof authority.
pub(super) fn validate_element_operands_observed<O: ExecutionObserver>(
    block: u32,
    instruction: &Inst,
    values: &ObservedValueTypes,
    constants: &[(u32, i128)],
    module: Option<&Module>,
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
    let result = state.check(block, instruction, values, constants, module, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            state.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}

impl State {
    fn check<O: ExecutionObserver>(
        &mut self,
        block: u32,
        instruction: &Inst,
        values: &ObservedValueTypes,
        constants: &[(u32, i128)],
        module: Option<&Module>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(67, 0)?;
        match instruction {
            Inst::ExtractElement { ty, array, index } => {
                self.extract(block, ty, *array, *index, values, constants, module, work)
            }
            Inst::InsertElement {
                ty,
                array,
                index,
                value,
            } => self.insert(
                block, ty, *array, *index, *value, values, constants, module, work,
            ),
            _ => Err(ObservedValueError::InvalidRange),
        }
    }

    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire(take(&mut self.op));
        work.retire(take(&mut self.reason));
        work.retire(take(&mut self.spelling));
    }

    fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        // Consuming exhaustive retirement retains the original first cause
        // and continues draining all nested payloads after any sticky stop.
        let _ = retire_validation_errors_observed(take(&mut self.errors), work.session, work.site);
    }
}
