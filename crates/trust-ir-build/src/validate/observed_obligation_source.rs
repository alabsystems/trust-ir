// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact original embedded source/public obligation identity diagnostics.
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
use trust_ir::proof::{
    PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES, ProofObligation, ProofObligationSourceIdentity,
};
mod ids;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    public_id: String,
    errors: Vec<ValidationError>,
}
/// Exact original source/public identity group, between formula-text integrity
/// and certificates. The semantic1024-byte ID limit comes from the existing
/// source-owned vocabulary; it does not cap or exempt raw duplicate-ID copying.
/// All actual text/classification, source/duplicate scans and requested storage
/// use the supplied original session/site; no owned ID index or clone is hidden.
/// This diagnostic data does not authenticate a source or issue proof authority.
pub(crate) fn validate_module_obligation_source_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, &mut work);
    work.flat(take(&mut state.public_id));
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
        work.admit(1, size_of::<ValidationError>() + size_of::<String>())
    }
    fn run<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        let mut at = 0usize;
        while let Some(row) = work.at(&module.proof_obligations, at)? {
            work.admit(1, size_of::<Option<&ProofObligationSourceIdentity>>())?;
            if let Some(source) = &row.source {
                self.row(module, row, source, at, work)?;
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn row<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        row: &ProofObligation,
        source: &ProofObligationSourceIdentity,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if !work.source_id(&source.source_id)? {
            self.prepare(work)?;
            self.errors
                .push(ValidationError::InvalidProofObligationSourceTextId {
                    obligation: row.id.index(),
                    field: "source_id",
                });
        }
        if !work.source_id(&source.assertion_id)? {
            self.prepare(work)?;
            self.errors
                .push(ValidationError::InvalidProofObligationSourceTextId {
                    obligation: row.id.index(),
                    field: "assertion_id",
                });
        }
        work.admit(
            1,
            size_of::<Option<trust_ir::proof::ProofObligationSourceRange>>(),
        )?;
        if let Some(range) = source.range {
            work.admit(
                14,
                size_of::<trust_ir::proof::ProofObligationSourceRange>() + size_of::<usize>(),
            )?;
            let file =
                usize::try_from(range.file).map_err(|_| ObservedValueError::CapacityOverflow)?;
            if file >= module.files.len() {
                self.prepare(work)?;
                self.errors
                    .push(ValidationError::ProofObligationSourceRangeFileOutOfRange {
                        obligation: row.id.index(),
                        file: range.file,
                        file_count: module.files.len(),
                    });
            }
            if range.start_line == 0 || range.end_line == 0 {
                self.prepare(work)?;
                self.errors
                    .push(ValidationError::InvalidProofObligationSourceRange {
                        obligation: row.id.index(),
                        reason: "start_line and end_line must be nonzero",
                    });
            }
            if (range.end_line, range.end_col) < (range.start_line, range.start_col) {
                self.prepare(work)?;
                self.errors
                    .push(ValidationError::InvalidProofObligationSourceRange {
                        obligation: row.id.index(),
                        reason: "end position precedes start position",
                    });
            }
        }
        work.admit(
            1,
            size_of::<Option<&trust_ir::proof::PublicObligationIdentity>>(),
        )?;
        if let Some(public) = &source.public {
            if !work.public_id(&public.obligation_id)? {
                self.prepare(work)?;
                self.errors
                    .push(ValidationError::InvalidPublicObligationId {
                        obligation: row.id.index(),
                    });
            }
            work.admit(2, size_of::<ProofDigestAlgorithm>())?;
            if public.semantic_digest.algorithm != ProofDigestAlgorithm::Sha256 {
                self.prepare(work)?;
                self.errors
                    .push(ValidationError::PublicObligationDigestNotSha256 {
                        obligation: row.id.index(),
                    });
            }
            // The original digest is a fixed32-byte Copy value. This prepaid
            // fixed walk has no variable payload/crypto or allocation in it.
            work.admit(64, size_of::<trust_ir::proof::ProofDigest>())?;
            if public.semantic_digest.is_zero() {
                self.prepare(work)?;
                self.errors
                    .push(ValidationError::PublicObligationDigestZero {
                        obligation: row.id.index(),
                    });
            }
            if let Some(first) = work.first_public(module, index, &public.obligation_id)? {
                work.text(&public.obligation_id, &mut self.public_id)?;
                self.prepare(work)?;
                self.errors
                    .push(ValidationError::DuplicatePublicObligationId {
                        obligation_id: take(&mut self.public_id),
                        first_obligation: first,
                        duplicate_obligation: row.id.index(),
                    });
            }
        }
        Ok(())
    }
}
// Formula-text and certificate/status/authority groups remain separate and in
// original order. Full module/source/proof/native authority, successful external
// caller/input disposal and physical std/Unicode/allocator/deallocator/OOM/
// panic/unwind/RSS/hardtime remain OPEN. No owner/grant/deadline/TLS/fuel reset.
