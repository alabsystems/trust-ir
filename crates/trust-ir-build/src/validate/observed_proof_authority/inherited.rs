// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact inherited-proof diagnostics over private replay currency and sealed records.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::proof::{ProofCertificate, ProofEvidence};
mod external;
mod local;
#[cfg(test)]
mod tests;
mod text;
#[derive(Default)]
struct Inherited {
    errors: Vec<ValidationError>,
    reason: String,
    selector: State,
    key: Option<ProofCertificateRef>,
    local: Option<LocalInheritance>,
}
#[derive(Clone, Copy)]
enum Message {
    Dangling,
    Unauthenticated(u32),
}
impl Authority<'_> {
    pub(super) fn inherited_errors<O: ExecutionObserver>(
        &self,
        module: &Module,
        policy: ImportPolicy<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<ValidationError>> {
        let mut w = Work { session, site };
        w.admit(1, size_of::<Inherited>())?;
        self.source(module, &mut w)?;
        let mut state = Inherited::default();
        let result = state.run(self, policy, &mut w);
        state.retire_scratch(&mut w);
        match result.and_then(|()| w.publication()) {
            Ok(()) => Ok(take(&mut state.errors)),
            Err(error) => {
                let _ =
                    retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
                Err(w.terminal(error))
            }
        }
    }
}
impl Inherited {
    fn run<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        policy: ImportPolicy<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(cert) = w.at(&a.module.proof_certificates, at)? {
            w.admit(8, size_of::<Option<(&FuncId, &ProofId)>>())?;
            if let ProofEvidence::InheritedFromCallee {
                callee,
                obligation,
                external,
            } = &cert.evidence
            {
                if let Some(reference) = external {
                    self.external(a, cert, reference, policy, w)?;
                } else {
                    self.local(a, cert, *callee, *obligation, w)?;
                }
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn prepare<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        w.reserve(&mut self.errors)?;
        w.admit(1, size_of::<ValidationError>())
    }
    fn message<O: ExecutionObserver>(&mut self, kind: Message, w: &mut Work<'_, '_, O>) -> R {
        self.prepare(w)?;
        self.errors.push(match kind {
            Message::Dangling => ValidationError::DanglingExternRef {
                detail: take(&mut self.reason),
            },
            Message::Unauthenticated(import) => ValidationError::UnauthenticatedImport {
                import,
                site: "inherited",
                detail: take(&mut self.reason),
            },
        });
        Ok(())
    }
    fn retire_key<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.step(size_of::<Option<ProofCertificateRef>>().saturating_add(1));
        if let Some(key) = self.key.take() {
            let _ = key.retire_observed(w.session, w.site);
        }
        w.poll();
    }
    fn retire_local<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.step(size_of::<Option<LocalInheritance>>().saturating_add(1));
        if let Some(local) = self.local.take() {
            let _ = local.retire_observed(w.session, w.site);
        }
        w.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        self.selector.retire_candidate(w);
        let _ =
            retire_validation_errors_observed(take(&mut self.selector.errors), w.session, w.site);
        self.retire_key(w);
        self.retire_local(w);
        w.inherited_string(take(&mut self.reason));
    }
}
