//! Exact config-selected unbound certificate diagnostics, never a replay.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::proof::{KERNEL_ANCHOR_CLEAN_BACKEND_TV, ProofCertificate, ProofEvidence};
mod storage;
#[cfg(test)]
mod tests;
#[derive(Clone, Copy)]
enum Mode {
    Unbound,
    Source,
}
#[derive(Default)]
struct State<'m> {
    errors: Vec<ValidationError>,
    pending: Option<ValidationError>,
    field: String,
    detail: String,
    row: Option<&'m ProofObligation>,
    certificate: Option<&'m ProofCertificate>,
    lineage: Option<bool>,
}
pub(crate) fn unbound_certificate_errors_observed<O: ExecutionObserver>(
    module: &Module,
    catalog: &ModuleFunctionCatalog<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    run(module, catalog, Mode::Unbound, session, site)
}
pub(crate) fn source_unbound_certificate_errors_observed<O: ExecutionObserver>(
    module: &Module,
    catalog: &ModuleFunctionCatalog<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    run(module, catalog, Mode::Source, session, site)
}
fn run<O: ExecutionObserver>(
    module: &Module,
    catalog: &ModuleFunctionCatalog<'_>,
    mode: Mode,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut w = Work { session, site };
    let copies = size_of::<State<'_>>()
        .checked_add(size_of::<Work<'_, '_, O>>())
        .and_then(|n| n.checked_add(size_of::<Vec<ValidationError>>()))
        .and_then(|n| n.checked_mul(2))
        .ok_or(ObservedValueError::CapacityOverflow)?;
    w.admit(
        copies
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?,
        copies,
    )?;
    let mut state = State::default();
    let result = (|| {
        w.admit(2, 2 * size_of::<&Module>())?;
        if !core::ptr::eq(catalog.source_module(), module) {
            return Err(ObservedValueError::InvalidRange);
        }
        state.run(module, catalog, mode, &mut w)
    })();
    state.finish(result, &mut w)
}
impl<'m> State<'m> {
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        catalog: &ModuleFunctionCatalog<'_>,
        mode: Mode,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(row) = w.at(&module.proof_obligations, at)? {
            w.admit(
                size_of::<ProofObligation>() + 1,
                2 * size_of::<Option<&ProofObligation>>(),
            )?;
            self.row = Some(row);
            if row.status.is_kernel_tier() && self.any(module, catalog, row, mode, w)? {
                self.diagnostic(row.id, mode, w)?;
            }
            self.retire_borrows(w);
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn any<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        catalog: &ModuleFunctionCatalog<'_>,
        row: &ProofObligation,
        mode: Mode,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(certificate) = w.at(&module.proof_certificates, at)? {
            w.admit(
                2 * size_of::<ProofCertificate>() + 1,
                2 * (size_of::<Option<&ProofCertificate>>() + size_of::<Option<bool>>()),
            )?;
            self.certificate = Some(certificate);
            if certificate.obligation == row.id && Self::candidate(&certificate.evidence, mode, w)?
            {
                // Whole child result/current/pending and consuming images
                // prepaid BEFORE the real child can return its bool or error.
                let copies = size_of::<R<bool>>()
                    .checked_add(size_of::<Option<bool>>())
                    .and_then(|n| n.checked_add(size_of::<bool>()))
                    .and_then(|n| n.checked_mul(2))
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                w.admit(
                    copies
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?,
                    copies,
                )?;
                self.lineage = Some(
                    certificate
                        .evidence
                        .clean_cic_lineage_binds_observed(row, catalog, w.session, w.site)?,
                );
                // The complete child bool+Result header stays held BEFORE
                // this next parent callback. Failure is never semantic false.
                w.admit(
                    size_of::<bool>() + 1,
                    2 * size_of::<bool>() + size_of::<Option<bool>>(),
                )?;
                if self.lineage == Some(true) {
                    return Ok(true);
                }
            }
            self.retire_certificate(w);
            w.next(&mut at)?;
        }
        Ok(false)
    }
    fn candidate<O: ExecutionObserver>(
        evidence: &ProofEvidence,
        mode: Mode,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(
            size_of::<ProofEvidence>() + 1,
            size_of::<Option<&trust_ir::proof::CleanCicKernelRecheck>>(),
        )?;
        let ProofEvidence::CleanCic {
            term,
            kernel_recheck,
            ..
        } = evidence
        else {
            return Ok(false);
        };
        w.admit(size_of::<Vec<u8>>() + 1, 0)?;
        if term.is_empty() {
            return Ok(false);
        }
        w.admit(3, size_of::<bool>())?;
        match mode {
            Mode::Unbound => Ok(kernel_recheck.as_ref().is_none_or(|r| r.binding.is_none())),
            Mode::Source => {
                let Some(recheck) = kernel_recheck.as_ref() else {
                    return Ok(false);
                };
                if !w.text_equal(&recheck.anchor, KERNEL_ANCHOR_CLEAN_BACKEND_TV)? {
                    return Ok(false);
                }
                w.admit(
                    size_of::<trust_ir::proof::CertificateBinding>() + 1,
                    size_of::<bool>(),
                )?;
                Ok(recheck
                    .binding
                    .as_deref()
                    .is_none_or(|binding| binding.environment.is_none()))
            }
        }
    }
    fn diagnostic<O: ExecutionObserver>(
        &mut self,
        id: ProofId,
        mode: Mode,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        if matches!(mode, Mode::Source) {
            storage::text(&mut self.field, "environment", w)?;
            storage::text(&mut self.detail, DETAIL, w)?;
        }
        w.admit(
            size_of::<ValidationError>() + 1,
            2 * size_of::<ValidationError>() + size_of::<Option<ValidationError>>(),
        )?;
        if self.pending.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.pending = Some(match mode {
            Mode::Unbound => ValidationError::UnboundCertificate {
                obligation: id.index(),
            },
            Mode::Source => ValidationError::CertificateBindingMismatch {
                obligation: id.index(),
                field: take(&mut self.field),
                detail: take(&mut self.detail),
            },
        });
        w.reserve(&mut self.errors)?;
        w.admit(
            size_of::<ValidationError>() + 1,
            2 * size_of::<ValidationError>() + size_of::<Option<ValidationError>>(),
        )?;
        if self.errors.len() >= self.errors.capacity() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.errors.push(
            self.pending
                .take()
                .ok_or(ObservedValueError::InvalidRange)?,
        );
        Ok(())
    }
}
const DETAIL: &str = "the clean_backend_tv certificate carries no island, so its comparand is the \
                     minter's word, not a checked source declaration; \
                     with_source_bound_certificates requires every translation-validation \
                     certificate to be source-bound through one (WS1.13, F-008)";
