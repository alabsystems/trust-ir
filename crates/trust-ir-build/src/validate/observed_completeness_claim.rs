// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original Partial carrier consistency only, never completeness authority.
use super::*;
use core::mem::{size_of, take};
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
    symbol: String,
    errors: Vec<ValidationError>,
}
/// Run the exact original Partial-carrier row consistency rule. None and
/// Complete produce no diagnostics here; they establish NO completeness fact.
/// Preserve first symbol, duplicate-row continue, every physical definition
/// and original error order. Reason/display-path/body contents are not read by
/// this specific old rule, and are never treated as trusted evidence.
/// Actual symbol reads/comparisons/copies, nested scans and storage admission
/// use the same original session/site. Retain partial owned names and consume
/// all refused diagnostics before returning no partial list. Successful input/
/// output disposal and physical allocator/stdlib/deallocator/time stay with
/// the caller. This grants no module, completeness, source or proof authority.
pub fn validate_module_completeness_claim_observed<O: ExecutionObserver>(
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
    work.retire_text(&mut state.symbol);
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
    fn walk<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        work.admit(3, size_of::<Option<&[trust_ir::UnloweredRow]>>())?;
        let rows = match &module.completeness {
            None | Some(trust_ir::ModuleCompleteness::Complete) => return Ok(()),
            Some(trust_ir::ModuleCompleteness::Partial(rows)) => rows,
        };
        work.admit(1, 0)?;
        if rows.is_empty() {
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::EmptyPartialClaim);
        }
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<Option<&trust_ir::UnloweredRow>>())?;
            let Some(row) = rows.get(index) else {
                return Ok(());
            };
            let mut earlier = 0usize;
            let mut duplicate = false;
            loop {
                work.admit(2, size_of::<Option<&trust_ir::UnloweredRow>>())?;
                if earlier == index {
                    break;
                }
                let prior = rows.get(earlier).ok_or(ObservedValueError::InvalidRange)?;
                if work.equal(&prior.symbol, &row.symbol)? {
                    duplicate = true;
                    break;
                }
                work.next(&mut earlier)?;
            }
            if duplicate {
                self.diagnostic(&row.symbol, None, work)?;
            } else {
                let mut fi = 0usize;
                loop {
                    work.admit(1, size_of::<Option<&Function>>())?;
                    let Some(function) = module.functions.get(fi) else {
                        break;
                    };
                    if work.equal(&function.name, &row.symbol)? {
                        work.admit(1, 0)?;
                        if !function.blocks.is_empty() {
                            self.diagnostic(&row.symbol, Some(function.id.index()), work)?;
                        }
                    }
                    work.next(&mut fi)?;
                }
            }
            work.next(&mut index)?;
        }
    }
    fn diagnostic<O: ExecutionObserver>(
        &mut self,
        symbol: &str,
        function: Option<u32>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.symbol.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text(symbol, &mut self.symbol)?;
        work.reserve(&mut self.errors)?;
        work.admit(2, size_of::<ValidationError>())?;
        self.errors.push(match function {
            None => ValidationError::DuplicateUnloweredRow {
                symbol: take(&mut self.symbol),
            },
            Some(function) => ValidationError::UnloweredRowNamesDefinition {
                symbol: take(&mut self.symbol),
                function,
            },
        });
        Ok(())
    }
}
