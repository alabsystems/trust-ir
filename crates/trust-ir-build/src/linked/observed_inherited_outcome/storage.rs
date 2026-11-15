// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
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
    pub(super) fn cursor(&mut self, population: usize, header: usize) -> R<()> {
        // Exact installed698 source: lazy initial descent, ascent to next KV,
        // then descent to successor leaf: three height walks, each <=n+1.
        let visits = population
            .checked_add(1)
            .and_then(|n| n.checked_mul(3))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        self.admit(visits, header)
    }
    pub(super) fn equal(
        &mut self,
        left: &ProofCertificateRef,
        right: &ProofCertificateRef,
    ) -> R<bool> {
        self.admit(
            128,
            2 * size_of::<trust_ir::proof::ProofDigest>()
                + 2 * size_of::<ProofId>()
                + size_of::<bool>(),
        )?;
        if left.obligation != right.obligation || left.evidence_digest != right.evidence_digest {
            return Ok(false);
        }
        self.admit(2, 2 * size_of::<usize>())?;
        if left.prover.len() != right.prover.len() {
            return Ok(false);
        }
        let mut at = 0;
        while at < left.prover.len() {
            self.admit(2, size_of::<usize>())?;
            let n = (left.prover.len() - at).min(1024);
            let end = at
                .checked_add(n)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                n.checked_mul(2)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
                0,
            )?;
            if left.prover.as_bytes()[at..end] != right.prover.as_bytes()[at..end] {
                return Ok(false);
            }
            at = end;
        }
        Ok(true)
    }
    pub(super) fn publication(&mut self, copy_bytes: usize) -> R<()> {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes,
            })
            .map_err(Into::into)
    }
}
