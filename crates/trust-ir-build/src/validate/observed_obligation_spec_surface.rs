// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact original obligation-side temporal backrefs and spec-variable bindings.
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
use trust_ir::proof::{ClauseBinding, ClausePlace, ObligationKind, ProofObligation};
use trust_ir::spec::TemporalForm;
use trust_ir::{SpecModule, SpecTemporal};
mod binding;
mod lookup;
mod render;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Resolution<T: Copy> {
    Missing,
    Unique(T),
    Ambiguous,
}
type Resolved<'a> = Option<(&'a SpecModule, &'a SpecTemporal)>;
#[derive(Default)]
struct State {
    machine: String,
    temporal: String,
    detail: String,
    sort: Option<String>,
    debug: String,
    errors: Vec<ValidationError>,
}
/// Preserve the original unique temporal-backref rule and exact spec-variable
/// diagnostics/order. All actual source/name scans, effective-sort parsing,
/// recursive comparison/Debug, formatting and requested storage use the same
/// original session/site. This diagnostic vector conveys no proof authority.
/// Other binding places remain the separate ordinary binding constituent.
pub(crate) fn validate_module_obligation_spec_surface_observed<O: ExecutionObserver>(
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
    fn run<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        let mut index = 0usize;
        while let Some(obligation) = work.at(&module.proof_obligations, index)? {
            self.row(module, obligation, work)?;
            work.next(&mut index)?;
        }
        Ok(())
    }
    fn row<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        obligation: &ProofObligation,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let resolved = self.resolve(module, obligation, work)?;
        work.admit(1, size_of::<Option<&trust_ir::proof::ProofFormula>>())?;
        let Some(formula) = &obligation.formula else {
            return Ok(());
        };
        let mut index = 0usize;
        while let Some((name, binding)) = work.at(&formula.bindings, index)? {
            // ClausePlace is a fixed Copy discriminant/index; no payload walk.
            work.admit(12, size_of::<Option<(u32, bool)>>())?;
            let place = match binding.place {
                ClausePlace::SpecVar { index } => Some((index, false)),
                ClausePlace::SpecVarNext { index } => Some((index, true)),
                _ => None,
            };
            if let Some((at, primed)) = place {
                self.binding(obligation, name, binding, at, primed, resolved, work)?;
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
    fn resolve<'m, O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        obligation: &ProofObligation,
        work: &mut Work<'_, '_, O>,
    ) -> R<Resolved<'m>> {
        work.admit(1, size_of::<Option<&trust_ir::proof::SpecObligationRef>>())?;
        let Some(spec) = &obligation.spec else {
            return work.publish_value(None);
        };
        work.admit(16, size_of::<bool>())?;
        if !matches!(
            obligation.kind,
            ObligationKind::Liveness | ObligationKind::TemporalSafety
        ) {
            self.reference(
                obligation,
                spec,
                "only a Liveness or TemporalSafety obligation states a temporal property",
                work,
            )?;
            return work.publish_value(None);
        }
        let machine = match work.machine(&module.spec_modules, &spec.machine)? {
            Resolution::Missing => {
                self.reference(
                    obligation,
                    spec,
                    "no SpecModule of this module carries that machine name",
                    work,
                )?;
                return work.publish_value(None);
            }
            Resolution::Ambiguous => {
                self.reference(
                    obligation,
                    spec,
                    "the machine name is ambiguous in this module",
                    work,
                )?;
                return work.publish_value(None);
            }
            Resolution::Unique(machine) => machine,
        };
        match work.temporal(&machine.temporal, &spec.temporal)? {
            Resolution::Missing => {
                self.reference(
                    obligation,
                    spec,
                    "that machine declares no temporal property of that name",
                    work,
                )?;
                work.publish_value(None)
            }
            Resolution::Ambiguous => {
                self.reference(
                    obligation,
                    spec,
                    "that machine declares the temporal property more than once",
                    work,
                )?;
                work.publish_value(None)
            }
            Resolution::Unique(property) => work.publish_value(Some((machine, property))),
        }
    }
    fn reference<O: ExecutionObserver>(
        &mut self,
        obligation: &ProofObligation,
        spec: &trust_ir::proof::SpecObligationRef,
        reason: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(&spec.machine, &mut self.machine)?;
        work.text(&spec.temporal, &mut self.temporal)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors
            .push(ValidationError::UnresolvedObligationSpecRef {
                obligation: obligation.id.index(),
                machine: take(&mut self.machine),
                temporal: take(&mut self.temporal),
                reason,
            });
        Ok(())
    }
    fn emit<O: ExecutionObserver>(
        &mut self,
        obligation: &ProofObligation,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + size_of::<String>())?;
        self.errors.push(ValidationError::InvalidObligationBinding {
            obligation: obligation.id.index(),
            detail: take(&mut self.detail),
        });
        Ok(())
    }
    fn clear_sort<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.step(size_of::<Option<String>>().saturating_add(1));
        if let Some(text) = self.sort.take() {
            work.flat(text);
        }
        work.admit(1, 0)
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.machine));
        work.flat(take(&mut self.temporal));
        work.flat(take(&mut self.detail));
        work.flat(take(&mut self.debug));
        work.step(size_of::<Option<String>>().saturating_add(1));
        if let Some(text) = self.sort.take() {
            work.flat(text);
        }
        work.poll();
    }
}
// Full module/proof/source/native authority and non-spec bindings remain OPEN.
// Successful caller/input disposal and physical std/allocator/deallocator/OOM/
// panic/unwind/RSS/hardtime remain OPEN. No owner/grant/deadline/TLS/fuel reset.
