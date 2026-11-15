// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact original complete module formula inventory and two-text diagnostics.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::proof::{FormulaSite, FormulaSiteRef, ProofFormula};
use trust_ir::spec::TemporalForm;
mod inventory;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    machine: String,
    label: String,
    errors: Vec<ValidationError>,
}
/// Visit the actual original canonical inventory: obligation formulas, physical
/// functions' requires/ensures/decreases, then each spec's typed invariants and
/// temporal leaves, all in source order. LeadsTo yields both leaves at the same
/// location; an unrecorded fairness relation yields none. Every actual row,
/// child decision, raw diagnostic label and requested growth/copy is observed
/// in the same original session/site. This is the formula diagnostic group,
/// not a parsed formula, spec link, certificate, module or proof authority.
///
/// Other proof-integrity groups retain their original outer order. Typed child
/// refusal never becomes acceptance/disagreement or a shorter diagnostic list.
/// Complete/partial labels and previous diagnostics remain held through failure
/// and original-owner retirement. Successful external input/result disposal,
/// physical std/allocator/deallocator/OOM/panic/unwind/RSS/hardtime remain OPEN.
pub(crate) fn validate_module_formula_texts_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, &mut work);
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
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.machine));
        work.flat(take(&mut self.label));
    }
    fn prepare<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(
            1,
            size_of::<ValidationError>() + size_of::<FormulaSite>() + 2 * size_of::<String>(),
        )
    }
    fn formula<O: ExecutionObserver>(
        &mut self,
        source: FormulaSiteRef<'_>,
        formula: &ProofFormula,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            1,
            size_of::<FormulaSiteRef<'_>>() + size_of::<trust_ir::pred::PredTable<'_>>(),
        )?;
        let predicates = module.pred_table();
        if !formula.states_two_texts_observed(&predicates, work.session, work.site)? {
            return Ok(());
        }
        work.admit(4, size_of::<FormulaSiteRef<'_>>())?;
        // All labels stay in State until the final admitted infallible assembly.
        // No owned FormulaSite exists outside custody before a fallible fee.
        match source {
            FormulaSiteRef::Obligation(id) => {
                self.prepare(work)?;
                self.errors.push(ValidationError::FormulaTextsDisagree {
                    site: FormulaSite::Obligation(id),
                });
            }
            FormulaSiteRef::SummaryClause {
                function,
                clause,
                index,
            } => {
                self.prepare(work)?;
                self.errors.push(ValidationError::FormulaTextsDisagree {
                    site: FormulaSite::SummaryClause {
                        function,
                        clause,
                        index,
                    },
                });
            }
            FormulaSiteRef::SpecInvariant { machine, invariant } => {
                work.text(machine, &mut self.machine)?;
                work.text(invariant, &mut self.label)?;
                self.prepare(work)?;
                self.errors.push(ValidationError::FormulaTextsDisagree {
                    site: FormulaSite::SpecInvariant {
                        machine: take(&mut self.machine),
                        invariant: take(&mut self.label),
                    },
                });
            }
            FormulaSiteRef::SpecTemporal { machine, property } => {
                work.text(machine, &mut self.machine)?;
                work.text(property, &mut self.label)?;
                self.prepare(work)?;
                self.errors.push(ValidationError::FormulaTextsDisagree {
                    site: FormulaSite::SpecTemporal {
                        machine: take(&mut self.machine),
                        property: take(&mut self.label),
                    },
                });
            }
        }
        Ok(())
    }
}
