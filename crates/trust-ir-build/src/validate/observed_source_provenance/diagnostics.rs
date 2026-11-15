// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, 0)?;
        if self.detail.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    pub(super) fn commit<O: ExecutionObserver>(
        &mut self,
        id: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::InvalidSourceProvenance {
            function: id,
            detail: take(&mut self.detail),
        });
        Ok(())
    }
    pub(super) fn static_error<O: ExecutionObserver>(
        &mut self,
        id: u32,
        detail: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text(detail, &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn schema<O: ExecutionObserver>(
        &mut self,
        id: u32,
        schema: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("unsupported schema ", &mut self.detail)?;
        work.number(u128::from(schema), &mut self.detail)?;
        work.text(" (expected ", &mut self.detail)?;
        work.number(u128::from(SOURCE_PROVENANCE_SCHEMA_V1), &mut self.detail)?;
        work.text(")", &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn algorithm<O: ExecutionObserver>(
        &mut self,
        id: u32,
        name: &'static str,
        algorithm: ProofDigestAlgorithm,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text(name, &mut self.detail)?;
        work.text(" must use sha256, not ", &mut self.detail)?;
        work.algorithm(algorithm, &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn zero<O: ExecutionObserver>(
        &mut self,
        id: u32,
        name: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text(name, &mut self.detail)?;
        work.text(" must not be zero", &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn stale<O: ExecutionObserver>(
        &mut self,
        id: u32,
        stored: &trust_ir::ProofDigest,
        expected: &trust_ir::ProofDigest,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("semantic_body_digest is stale: stored ", &mut self.detail)?;
        work.digest(stored, &mut self.detail)?;
        work.text(", expected ", &mut self.detail)?;
        work.digest(expected, &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn row_id<O: ExecutionObserver>(
        &mut self,
        id: u32,
        position: usize,
        actual: u32,
        expected: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("source-loop row ", &mut self.detail)?;
        work.number(position as u128, &mut self.detail)?;
        work.text(" has id ", &mut self.detail)?;
        work.number(u128::from(actual), &mut self.detail)?;
        work.text(", expected dense ordered id ", &mut self.detail)?;
        work.number(u128::from(expected), &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn duplicate_loop_hir<O: ExecutionObserver>(
        &mut self,
        id: u32,
        hir: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("source loop HIR local id ", &mut self.detail)?;
        work.number(u128::from(hir), &mut self.detail)?;
        work.text(" is duplicated", &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn duplicate_header<O: ExecutionObserver>(
        &mut self,
        id: u32,
        header: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("TrustIR loop header bb", &mut self.detail)?;
        work.number(u128::from(header), &mut self.detail)?;
        work.text(" is claimed by more than one source loop", &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn missing_header<O: ExecutionObserver>(
        &mut self,
        id: u32,
        source: u32,
        header: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("source loop ", &mut self.detail)?;
        work.number(u128::from(source), &mut self.detail)?;
        work.text(" names missing header bb", &mut self.detail)?;
        work.number(u128::from(header), &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn no_backedge<O: ExecutionObserver>(
        &mut self,
        id: u32,
        header: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("bb", &mut self.detail)?;
        work.number(u128::from(header), &mut self.detail)?;
        work.text(
            " is not a reachable natural-loop header with a dominated backedge",
            &mut self.detail,
        )?;
        self.commit(id, work)
    }
    pub(super) fn blank_binding<O: ExecutionObserver>(
        &mut self,
        id: u32,
        source: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("source loop ", &mut self.detail)?;
        work.number(u128::from(source), &mut self.detail)?;
        work.text(" contains a blank binding name", &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn unsorted<O: ExecutionObserver>(
        &mut self,
        id: u32,
        source: u32,
        name: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("source loop ", &mut self.detail)?;
        work.number(u128::from(source), &mut self.detail)?;
        work.text(
            " bindings are not strictly name-sorted at ",
            &mut self.detail,
        )?;
        work.quoted(name, &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn duplicate_binding_hir<O: ExecutionObserver>(
        &mut self,
        id: u32,
        source: u32,
        hir: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("source loop ", &mut self.detail)?;
        work.number(u128::from(source), &mut self.detail)?;
        work.text(" duplicates binding HIR local id ", &mut self.detail)?;
        work.number(u128::from(hir), &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn duplicate_place<O: ExecutionObserver>(
        &mut self,
        id: u32,
        source: u32,
        place: SourcePlace,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("source loop ", &mut self.detail)?;
        work.number(u128::from(source), &mut self.detail)?;
        work.text(" maps more than one identifier to ", &mut self.detail)?;
        work.source_place(place, &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn missing_parameter<O: ExecutionObserver>(
        &mut self,
        id: u32,
        name: &str,
        index: u32,
        header: Option<u32>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("binding ", &mut self.detail)?;
        work.quoted(name, &mut self.detail)?;
        work.text(" names missing ", &mut self.detail)?;
        if let Some(header) = header {
            work.text("bb", &mut self.detail)?;
            work.number(u128::from(header), &mut self.detail)?;
            work.text(" loop parameter ", &mut self.detail)?;
        } else {
            work.text("function parameter ", &mut self.detail)?;
        }
        work.number(u128::from(index), &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn inconsistent<O: ExecutionObserver>(
        &mut self,
        id: u32,
        hir: u32,
        name: &str,
        place: Place,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("HIR local id ", &mut self.detail)?;
        work.number(u128::from(hir), &mut self.detail)?;
        work.text(" is inconsistently mapped as ", &mut self.detail)?;
        work.quoted(name, &mut self.detail)?;
        work.text("/", &mut self.detail)?;
        work.scoped_place(place, &mut self.detail)?;
        self.commit(id, work)
    }
    pub(super) fn ambiguous<O: ExecutionObserver>(
        &mut self,
        id: u32,
        place: Place,
        old: u32,
        new: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text("place ", &mut self.detail)?;
        work.scoped_place(place, &mut self.detail)?;
        work.text(" is ambiguously mapped to HIR locals ", &mut self.detail)?;
        work.number(u128::from(old), &mut self.detail)?;
        work.text(" and ", &mut self.detail)?;
        work.number(u128::from(new), &mut self.detail)?;
        self.commit(id, work)
    }
}
