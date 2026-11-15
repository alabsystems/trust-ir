// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::linked::SiteOutcome;
impl Inherited {
    pub(super) fn external<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        cert: &ProofCertificate,
        reference: &trust_ir::ExternRef,
        policy: ImportPolicy<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        if w.at(&a.module.imports, reference.module.index() as usize)?
            .is_none()
        {
            self.text("certificate for obligation #", w)?;
            self.number(cert.obligation.index() as u64, w)?;
            self.text(" inherits from import #", w)?;
            self.number(reference.module.index() as u64, w)?;
            self.text(", which is not declared in `Module::imports`", w)?;
            self.message(Message::Dangling, w)?;
        }
        w.admit(2, size_of::<Option<ProofId>>())?;
        if reference.obligation.is_none() {
            self.text("certificate for obligation #", w)?;
            self.number(cert.obligation.index() as u64, w)?;
            self.text(" inherits from an ExternRef that names no obligation, so it carries no proof claim to inherit",w)?;
            self.message(Message::Dangling, w)?;
        }
        w.admit(3, size_of::<ImportPolicy<'_>>())?;
        match policy {
            ImportPolicy::Structural => Ok(()),
            ImportPolicy::Refuse => {
                self.text("certificate for obligation #", w)?;
                self.number(cert.obligation.index() as u64, w)?;
                self.text(" inherits obligation #", w)?;
                self.number(reference.obligation.map_or(0, |id| id.index()) as u64, w)?;
                self.text(" of ", w)?;
                self.quoted(&reference.symbol, w)?;
                self.text(" from import #", w)?;
                self.number(reference.module.index() as u64, w)?;
                self.text(", but this entry point has no import resolver and takes no cross-crate claim on faith; authenticate it with `validate_linked_module`",w)?;
                self.message(Message::Unauthenticated(reference.module.index()), w)
            }
            ImportPolicy::Authenticated(authenticated) => {
                w.admit(1, size_of::<Option<ProofCertificateRef>>())?;
                self.key = Some(cert.lineage_ref_observed(w.session, w.site)?);
                let key = self.key.as_ref().ok_or(ObservedValueError::InvalidRange)?;
                let outcome = authenticated.inherited_outcome_observed(key, w.session, w.site)?;
                match outcome {
                    Some(SiteOutcome::Authenticated | SiteOutcome::Reported) => {}
                    Some(SiteOutcome::Refused(detail)) => {
                        self.text(detail, w)?;
                        self.message(Message::Unauthenticated(reference.module.index()), w)?;
                    }
                    None => {
                        self.text("certificate for obligation #", w)?;
                        self.number(cert.obligation.index() as u64, w)?;
                        self.text(" was not examined by the linked validator", w)?;
                        self.message(Message::Unauthenticated(reference.module.index()), w)?;
                    }
                }
                self.retire_key(w);
                w.admit(1, 0)
            }
        }
    }
}
