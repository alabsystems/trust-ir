// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Borrow actual sealed records; neither a candidate callback nor an authenticator.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::size_of;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T> = Result<T, ObservedValueError>;
impl AuthenticatedImports {
    /// Read only this exact linked walk's retained inheritance outcome. No
    /// default, report flag, new owner, or authentication is manufactured.
    pub(crate) fn inherited_outcome_observed<O: ExecutionObserver>(
        &self,
        key: &ProofCertificateRef,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<&SiteOutcome>> {
        let mut w = Work { session, site };
        w.cursor(
            self.inherited.len(),
            size_of::<std::collections::btree_map::Iter<'_, ProofCertificateRef, SiteOutcome>>(),
        )?;
        let mut rows = self.inherited.iter();
        let result = loop {
            w.cursor(
                self.inherited.len(),
                size_of::<Option<(&ProofCertificateRef, &SiteOutcome)>>(),
            )?;
            let Some((candidate, outcome)) = rows.next() else {
                break None;
            };
            if w.equal(candidate, key)? {
                break Some(outcome);
            }
        };
        w.publication(size_of::<Option<&SiteOutcome>>())?;
        Ok(result)
    }
    /// The original LinkedAuthority reads the actual admitted SET. Do not
    /// infer this from an outcome or a public status: record_inherited may
    /// update an outcome while an earlier admitted key remains in that set.
    pub(crate) fn inherited_admission_observed<O: ExecutionObserver>(
        &self,
        key: &ProofCertificateRef,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut w = Work { session, site };
        w.cursor(
            self.admitted.len(),
            size_of::<std::collections::btree_set::Iter<'_, ProofCertificateRef>>(),
        )?;
        let mut rows = self.admitted.iter();
        let result = loop {
            w.cursor(
                self.admitted.len(),
                size_of::<Option<&ProofCertificateRef>>(),
            )?;
            let Some(candidate) = rows.next() else {
                break false;
            };
            if w.equal(candidate, key)? {
                break true;
            }
        };
        w.publication(size_of::<bool>())?;
        Ok(result)
    }
}
