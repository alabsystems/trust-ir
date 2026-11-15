// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn last<'m, O: ExecutionObserver>(
    module: &'m Module,
    id: ProofId,
    w: &mut Work<'_, '_, O>,
) -> R<Option<&'m ProofObligation>> {
    let (mut at, mut found) = (0, None);
    while let Some(row) = w.at(&module.proof_obligations, at)? {
        w.admit(2, size_of::<Option<&ProofObligation>>())?;
        if row.id == id {
            found = Some(row);
        }
        w.next(&mut at)?;
    }
    Ok(found)
}
pub(super) fn owner<O: ExecutionObserver>(
    module: &Module,
    id: ProofId,
    w: &mut Work<'_, '_, O>,
) -> R<Option<FuncId>> {
    let (mut at, mut found) = (0, None);
    while let Some(row) = w.at(&module.proof_obligations, at)? {
        w.admit(3, size_of::<Option<FuncId>>())?;
        // Original filtered owner map: a later unscoped duplicate does NOT
        // erase the last scoped owner. ProofRef's whole last row differs.
        if row.id == id && row.function.is_some() {
            found = row.function;
        }
        w.next(&mut at)?;
    }
    Ok(found)
}
impl State {
    pub(super) fn grounds<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        id: ProofId,
        currency: Currency,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(certificate) = w.at(&a.module.proof_certificates, at)? {
            w.admit(2, size_of::<bool>())?;
            if certificate.obligation == id {
                w.admit(1, size_of::<Option<ProofCertificateRef>>())?;
                if self.candidate.is_some() {
                    return Err(ObservedValueError::InvalidRange);
                }
                self.candidate = Some(certificate.lineage_ref_observed(w.session, w.site)?);
                let result = self.member(
                    match currency {
                        Currency::Discharged => &a.discharged,
                        Currency::Kernel => &a.kernel,
                    },
                    w,
                );
                self.retire_candidate(w);
                let found = result?;
                w.admit(1, 0)?;
                if found {
                    return Ok(true);
                }
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
    pub(super) fn member<O: ExecutionObserver>(
        &self,
        refs: &[ProofCertificateRef],
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let candidate = self
            .candidate
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        let mut at = 0;
        while let Some(row) = w.at(refs, at)? {
            // Both digest carriers are closed fixed Copy records; no payload
            // parse/normalization/status reads stand in for exact identity.
            w.admit(
                128,
                2 * size_of::<trust_ir::proof::ProofDigest>() + size_of::<bool>(),
            )?;
            if candidate.obligation == row.obligation
                && candidate.evidence_digest == row.evidence_digest
                && w.text_equal(&candidate.prover, &row.prover)?
            {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
}
