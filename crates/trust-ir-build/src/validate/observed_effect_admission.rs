// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Only borrowed callee lookup and the existing recorded effect-summary policy.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::ImportPolicy;
use core::mem::size_of;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::value::FuncId;
use trust_ir::{EffectSummary, Function, Linkage, Module};
mod lookup;
#[cfg(test)]
pub(crate) mod tests;
type R<T> = Result<T, ObservedValueError>;
struct Work<'s, 'o, O: ExecutionObserver> {
    session: &'s mut ObservedSession<'o, O>,
    site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    fn admit(&mut self, work: usize, copy_bytes: usize) -> R<()> {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    fn publication<T>(&mut self, value: T) -> R<T> {
        self.session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: self.site,
            work: 1,
            copy_bytes: size_of::<T>(),
        })?;
        Ok(value)
    }
}
/// Exact ordinary effect admission, not module/proof/import authentication.
/// Definitions still require the whole enclosing validator to check their
/// bodies. A declaration uses only the linked validator's already-recorded
/// Authenticated outcome; Reported, Refused and absent outcomes all mean havoc.
pub(crate) fn admissible_effects_observed<'m, O: ExecutionObserver>(
    module: &'m Module,
    callee: FuncId,
    policy: ImportPolicy<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<&'m EffectSummary>> {
    let mut work = Work { session, site };
    work.admit(
        1,
        size_of::<Option<&EffectSummary>>() + size_of::<Work<'_, '_, O>>(),
    )?;
    let answer = (|| -> R<Option<&'m EffectSummary>> {
        let Some(target) = function_by_id_observed(module, callee, work.session, work.site)? else {
            return Ok(None);
        };
        work.admit(2, 2 * size_of::<Option<&EffectSummary>>())?;
        let Some(effects) = target
            .summary
            .as_ref()
            .and_then(|summary| summary.effects.as_ref())
        else {
            return Ok(None);
        };
        work.admit(9, size_of::<Linkage>() + size_of::<bool>())?;
        if interposable(target.linkage) {
            return Ok(None);
        }
        work.admit(1, size_of::<usize>() + size_of::<bool>())?;
        if !target.blocks.is_empty() {
            return Ok(Some(effects));
        }
        work.admit(3, size_of::<ImportPolicy<'_>>())?;
        match policy {
            ImportPolicy::Structural | ImportPolicy::Refuse => Ok(None),
            ImportPolicy::Authenticated(authenticated) => {
                let outcome =
                    authenticated.backed_by_outcome_observed(callee, work.session, work.site)?;
                work.admit(3, size_of::<Option<&crate::linked::SiteOutcome>>())?;
                Ok(
                    matches!(outcome, Some(crate::linked::SiteOutcome::Authenticated))
                        .then_some(effects),
                )
            }
        }
    })()?;
    work.publication(answer)
}
// Exhaustive existing linker premise; no name, body or proof restatement scan.
fn interposable(linkage: Linkage) -> bool {
    match linkage {
        Linkage::Weak | Linkage::LinkOnce | Linkage::ExternalWeak => true,
        Linkage::External
        | Linkage::Internal
        | Linkage::Private
        | Linkage::AvailableExternally
        | Linkage::WeakOdr
        | Linkage::LinkOnceOdr => false,
    }
}
pub(crate) use lookup::function_by_id_observed;
