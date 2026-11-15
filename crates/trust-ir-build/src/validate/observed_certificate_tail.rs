// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original proof-integrity certificate/status/justification tail only.
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
use trust_ir::proof::{ProofEvidence, ProofObligation, ProofStatus};
use trust_ir::value::ProofId;
mod lookup;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    errors: Vec<ValidationError>,
}
/// Preserve the original proof-integrity tail's three groups: dangling
/// certificate rows, unique-row status/evidence-kind consistency in certificate
/// order, then every Trusted row lacking nonblank Trusted attribution. Actual
/// borrowed scans replace discarded cloned/set/map lookup state. Every actual
/// scan, fixed shape decision and Unicode justification scalar uses this same
/// original session/site. No evidence payload is parsed or trusted here; the
/// exact existing finite evidence-kind table remains unchanged.
///
/// All prior diagnostics stay owned through admission, transfer or complete
/// sticky original-owner retirement. No partial list or stop fallback returns.
/// This establishes no kernel replay/certificate/proof/module/source authority.
/// Full ordered integrity/module/bundle composition, successful external input
/// and result disposal, physical Unicode/std/allocator/deallocator/OOM/panic/
/// unwind/RSS/hardtime remain OPEN. No owner/grant/deadline/TLS/fuel is reset.
pub(crate) fn validate_module_certificate_integrity_tail_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, &mut work);
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
    fn prepare<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())
    }
    fn run<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        let mut at = 0usize;
        while let Some(cert) = work.at(&module.proof_certificates, at)? {
            work.admit(1, size_of::<ProofId>())?;
            if !work.exists(module, cert.obligation)? {
                self.prepare(work)?;
                self.errors.push(ValidationError::DanglingProofCertificate {
                    obligation: cert.obligation.index(),
                });
            }
            work.next(&mut at)?;
        }
        let mut at = 0usize;
        while let Some(cert) = work.at(&module.proof_certificates, at)? {
            work.admit(1, size_of::<ProofId>())?;
            if let Some(row) = work.unique(module, cert.obligation)? {
                work.admit(16, size_of::<ProofStatus>() + size_of::<bool>())?;
                if row.status == ProofStatus::Failed
                    && !matches!(cert.evidence, ProofEvidence::InheritedFromCallee { .. })
                {
                    self.prepare(work)?;
                    self.errors
                        .push(ValidationError::GroundCertificateStatusInconsistent {
                            obligation: row.id.index(),
                            status: "Failed",
                        });
                }
                // These existing helpers project fixed Copy discriminants and
                // static labels only; no evidence/kind payload, parser or
                // authority is traversed or admitted by this finite table.
                work.admit(128, 4 * size_of::<&'static str>() + size_of::<bool>())?;
                if !evidence_admits_obligation_kind(&cert.evidence, &row.kind) {
                    let kind = obligation_kind_name(&row.kind);
                    let evidence = evidence_variant_name(&cert.evidence);
                    self.prepare(work)?;
                    self.errors.push(ValidationError::EvidenceKindMismatch {
                        obligation: row.id.index(),
                        kind,
                        evidence,
                    });
                }
            }
            work.next(&mut at)?;
        }
        let mut at = 0usize;
        while let Some(row) = work.at(&module.proof_obligations, at)? {
            work.admit(
                1,
                size_of::<ProofStatus>() + size_of::<bool>() + size_of::<ProofId>(),
            )?;
            if row.status == ProofStatus::Trusted && !work.justified(module, row.id)? {
                self.prepare(work)?;
                self.errors
                    .push(ValidationError::TrustedWithoutJustification {
                        obligation: row.id.index(),
                    });
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
}
