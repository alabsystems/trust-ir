// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'f> State<'f> {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        module: Option<&Module>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<&SourceProvenance>>())?;
        let Some(source) = &function.source_provenance else {
            return Ok(());
        };
        let id = function.id.index();
        work.admit(1, 0)?;
        if source.schema != SOURCE_PROVENANCE_SCHEMA_V1 {
            self.schema(id, source.schema, work)?;
        }
        work.admit(3, 3 * size_of::<(&str, trust_ir::ProofDigest)>())?;
        for (name, digest) in [
            ("compiler_source_digest", source.compiler_source_digest),
            ("semantic_body_digest", source.semantic_body_digest),
            ("binding_digest", source.binding_digest),
        ] {
            work.admit(2, 0)?;
            if digest.algorithm != ProofDigestAlgorithm::Sha256 {
                self.algorithm(id, name, digest.algorithm, work)?;
            }
            work.admit(32, 0)?;
            if digest.is_zero() {
                self.zero(id, name, work)?;
            }
        }
        if !source.binding_digest_is_valid_observed(work.session, work.site)? {
            self.static_error(
                id,
                "binding_digest does not cover the stored identity/body/map",
                work,
            )?;
        }
        match module {
            None => self.static_error(
                id,
                "module context is required to rederive semantic_body_digest",
                work,
            )?,
            Some(module) => {
                work.admit(1, 0)?;
                if self.pending.capacity() != 0 {
                    return Err(ObservedValueError::InvalidRange);
                }
                match module.source_provenance_semantic_digest_observed(
                    function.id,
                    work.session,
                    work.site,
                )? {
                    Ok(expected) => {
                        work.admit(34, 0)?;
                        if expected != source.semantic_body_digest {
                            self.stale(id, &source.semantic_body_digest, &expected, work)?;
                        }
                    }
                    Err(detail) => {
                        // Retain the actual returned owned detail before a copy,
                        // reserve, diagnostic construction or publication can stop.
                        self.pending = detail;
                        self.ready(work)?;
                        work.text("cannot derive semantic_body_digest: ", &mut self.detail)?;
                        work.text(&self.pending, &mut self.detail)?;
                        self.commit(id, work)?;
                        work.retire_text(&mut self.pending);
                        work.admit(1, 0)?;
                    }
                }
            }
        }
        work.admit(1, 0)?;
        if source.loops.is_empty() {
            self.static_error(
                id,
                "a present carrier must contain at least one source loop",
                work,
            )?;
            return Ok(());
        }
        let entry = work.block(function, function.entry)?;
        self.dominators = Some(DominatorTree::new_observed(
            function,
            work.session,
            work.site,
        )?);
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<&SourceLoopProvenance>())?;
            let Some(source_loop) = source.loops.get(index) else {
                return Ok(());
            };
            work.admit(1, size_of::<u32>())?;
            let expected = u32::try_from(index).unwrap_or(u32::MAX);
            if source_loop.source_loop_id != expected {
                self.row_id(id, index, source_loop.source_loop_id, expected, work)?;
            }
            if !work.insert(&mut self.loop_hir, source_loop.hir_local_id)? {
                self.duplicate_loop_hir(id, source_loop.hir_local_id, work)?;
            }
            if !work.insert(&mut self.headers, source_loop.header.index())? {
                self.duplicate_header(id, source_loop.header.index(), work)?;
            }
            if let Some(header) = work.block(function, source_loop.header)? {
                if !self.backedge(function, source_loop.header, work)? {
                    self.no_backedge(id, source_loop.header.index(), work)?;
                }
                self.bindings(id, source_loop, entry, header, work)?;
                self.retire_local(work);
                work.admit(1, 0)?;
            } else {
                self.missing_header(
                    id,
                    source_loop.source_loop_id,
                    source_loop.header.index(),
                    work,
                )?;
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
}
