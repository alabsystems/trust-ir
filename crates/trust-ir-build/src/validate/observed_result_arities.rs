// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual module result-count validation without discarded type clones.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod count;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Default)]
struct State {
    op: String,
    errors: Vec<ValidationError>,
}

/// Preserve every ordinary module instruction-result arity diagnostic, with
/// exhaustive actual instruction classification and concrete module lookup.
/// The old result_tys().len() clones carried no checks; count exact borrowed
/// signature/dialect result headers instead, without reading any type payload.
/// This is only one validation constituent, never source/proof authority.
/// Successful diagnostics/input disposal and physical allocator/deallocator,
/// OOM, panic/unwind and time containment remain caller responsibilities.
pub fn validate_module_result_arities_observed<O: ExecutionObserver>(
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
    let result = state.walk(module, &mut work);
    work.retire(take(&mut state.op));
    let result = result.and_then(|()| work.publication());
    match result {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            state.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}

impl State {
    fn walk<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        let mut function_index = 0;
        loop {
            work.admit(1, 0)?;
            let Some(function) = module.functions.get(function_index) else {
                break;
            };
            let mut block_index = 0;
            loop {
                work.admit(1, 0)?;
                let Some(block) = function.blocks.get(block_index) else {
                    break;
                };
                let mut node_index = 0;
                loop {
                    work.admit(1, 0)?;
                    let Some(node) = block.body.get(node_index) else {
                        break;
                    };
                    let expected = count::expected(&node.inst, module, work)?;
                    work.admit(1, size_of::<usize>())?;
                    let actual = node.results.len();
                    if expected != actual {
                        self.diagnostic(block.id.index(), &node.inst, expected, actual, work)?;
                    }
                    node_index = node_index
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                }
                block_index = block_index
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            function_index = function_index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        Ok(())
    }

    fn diagnostic<O: ExecutionObserver>(
        &mut self,
        block: u32,
        instruction: &Inst,
        expected: usize,
        actual: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(67, size_of::<&'static str>())?;
        let op = instruction_kind(instruction);
        work.token(op, &mut self.op)?;
        // Pending op storage stays owned through every later allocation/copy
        // refusal. The remaining diagnostic payload is fixed scalar data.
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::InstrResultArityMismatch {
            block,
            op: take(&mut self.op),
            expected,
            actual,
        });
        Ok(())
    }

    fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(error) = self.errors.pop() {
                match error {
                    ValidationError::InstrResultArityMismatch { op, .. } => work.retire(op),
                    // The private constructor above produces only that variant.
                    other => work.retire(other),
                }
            }
        }
        work.retire(take(&mut self.errors));
    }
}
