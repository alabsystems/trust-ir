// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Authority<'_> {
    pub(super) fn contexts<O: ExecutionObserver>(
        &self,
        module: &Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<ValidationError>> {
        let mut w = Work { session, site };
        w.admit(1, size_of::<State>())?;
        self.source(module, &mut w)?;
        let mut state = State::default();
        let result = state.contexts(self, &mut w);
        state.finish(result, &mut w)
    }
    pub(super) fn references<O: ExecutionObserver>(
        &self,
        module: &Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<ValidationError>> {
        let mut w = Work { session, site };
        w.admit(1, size_of::<State>())?;
        self.source(module, &mut w)?;
        let mut state = State::default();
        let result = state.references(self, &mut w);
        state.finish(result, &mut w)
    }
    pub(super) fn discharged_errors<O: ExecutionObserver>(
        &self,
        module: &Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<ValidationError>> {
        let mut w = Work { session, site };
        w.admit(1, size_of::<State>())?;
        self.source(module, &mut w)?;
        let mut state = State::default();
        let result = state.discharged(self, &mut w);
        state.finish(result, &mut w)
    }
}
impl State {
    fn discharged<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(row) = w.at(&a.module.proof_obligations, at)? {
            w.admit(2, size_of::<ProofStatus>() + size_of::<bool>())?;
            if row.status == ProofStatus::Discharged
                && !self.grounds(a, row.id, Currency::Discharged, w)?
            {
                fixed_error!(
                    self,
                    w,
                    ValidationError::DischargedWithoutCertificate {
                        obligation: row.id.index(),
                    }
                )?;
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
}
