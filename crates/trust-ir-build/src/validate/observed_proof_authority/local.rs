// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Same-module inheritance DATA verdict over the private actual kernel currency.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::proof::{CoverageBound, ObligationKind, ProofCertificate, ProofEvidence};
mod fields;
mod rule;
#[cfg(test)]
mod tests;
mod text;
#[derive(Clone, Copy)]
enum Verdict {
    NotRouted,
    Admitted,
    NamedElsewhere,
    Refused,
}
#[derive(Default)]
struct Local {
    selector: State,
    reason: String,
    recorded: Vec<CoverageBound>,
}
impl Authority<'_> {
    /// A private predicate for the eventual real authority assembler. This does
    /// not append a currency, mint kernel evidence, or accept a caller callback.
    pub(super) fn local_inheritance<O: ExecutionObserver>(
        &self,
        module: &Module,
        cert: &ProofCertificate,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<LocalInheritance> {
        let mut w = Work { session, site };
        w.admit(1, size_of::<Local>())?;
        self.source(module, &mut w)?;
        let mut state = Local::default();
        let result = state.run(self, cert, &mut w);
        state.retire_children(&mut w);
        match result {
            Ok(verdict) => {
                if let Err(error) = w.admit_result() {
                    w.local_string(take(&mut state.reason));
                    return Err(w.terminal(error));
                }
                Ok(match verdict {
                    Verdict::NotRouted => LocalInheritance::NotRouted,
                    Verdict::Admitted => LocalInheritance::Admitted,
                    Verdict::NamedElsewhere => LocalInheritance::RefusedNamedElsewhere,
                    Verdict::Refused => LocalInheritance::Refused(take(&mut state.reason)),
                })
            }
            Err(error) => {
                w.local_string(take(&mut state.reason));
                Err(w.terminal(error))
            }
        }
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    fn admit_result(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: size_of::<LocalInheritance>(),
            })
            .map_err(Into::into)
    }
}
impl Local {
    fn refused<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R<Verdict> {
        w.admit(1, size_of::<Verdict>())?;
        Ok(Verdict::Refused)
    }
}

impl Local {
    fn retire_children<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        self.selector.retire_candidate(w);
        let _ =
            retire_validation_errors_observed(take(&mut self.selector.errors), w.session, w.site);
        w.local_rows(take(&mut self.recorded));
    }
    fn retire<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        self.retire_children(w);
        w.local_string(take(&mut self.reason));
    }
}
impl LocalInheritance {
    pub(super) fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut w = Work { session, site };
        w.step(size_of::<LocalInheritance>().saturating_add(1));
        if let Self::Refused(reason) = self {
            w.local_string(reason);
        }
        w.terminal_publication()
    }
}
