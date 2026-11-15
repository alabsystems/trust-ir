// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual pointer-word and select operand checks under the original owner.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod checks;
mod diagnostics;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    op: String,
    role: String,
    pointer: String,
    expected: String,
    actual: String,
    reason: String,
    pending_ty: Option<Ty>,
    errors: Vec<ValidationError>,
}
enum Diagnostic {
    Operand(u32),
    Pointer(u32),
    Metadata(u32),
    Select(u32),
}

/// Exactly PtrData/PtrMetadata/PtrFromParts/Select from the original type
/// pass, borrowing its complete original inferred map. Other instruction
/// families are a typed misuse, never an accepting validation fallback.
/// Vector well-formedness, result inference and all other constituents remain
/// the complete type-pass caller's responsibility. No authority is conferred.
///
/// Actual type comparisons and spelling run under this same original owner;
/// no outer Refine exemption is introduced. Fixed metadata shapes are priced
/// before classification and actual logical-mask allocation before growth.
/// All pending output/expected types survive any later failure until consuming
/// original-session retirement; no partial diagnostic vector is published.
pub(super) fn validate_pointer_select_operands_observed<O: ExecutionObserver>(
    block: u32,
    instruction: &Inst,
    values: &ObservedValueTypes,
    pointer_bits: u32,
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
    let result = state.check(block, instruction, values, pointer_bits, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            state.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}
