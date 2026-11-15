// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! One Frame call's exact reached proofs, with prepaid lexical restoration.
use super::*;
use clean_kernel::FVarId;

struct Entry {
    local: ScopedLocal,
    proof: Expr,
    previous: Option<usize>,
}
#[derive(Default)]
pub(super) struct ReachedRelations {
    entries: Vec<Entry>,
    latest: HashMap<FVarId, usize>,
}
impl ReachedRelations {
    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }
    pub(super) fn ids(&self) -> impl Iterator<Item = FVarId> + '_ {
        self.entries.iter().map(|entry| entry.local.id())
    }
    pub(super) fn push(
        &mut self,
        parts: &mut ProofComponents,
        local: &ScopedLocal,
        proof: &Expr,
    ) -> Result<(), String> {
        // Two pins, three record slots, old lookup, map insertion/storage,
        // and four units reserved for this entry's later pop/map restoration.
        // No mutation precedes payment, and restoration never refunds work.
        parts.spend_context_work(12)?;
        let id = local.id();
        let previous = self.latest.insert(id, self.entries.len());
        self.entries.push(Entry {
            local: local.clone(),
            proof: proof.clone(),
            previous,
        });
        Ok(())
    }
    pub(super) fn get(
        &self,
        parts: &mut ProofComponents,
        id: FVarId,
    ) -> Result<Option<Expr>, String> {
        parts.spend_context_work(3)?; // hash probe, entry lookup, proof pin
        Ok(self
            .latest
            .get(&id)
            .map(|&index| self.entries[index].proof.clone()))
    }
    pub(super) fn restore(&mut self, checkpoint: usize) {
        assert!(checkpoint <= self.entries.len());
        while self.entries.len() > checkpoint {
            let entry = self.entries.pop().expect("nonempty paid Frame suffix");
            if let Some(previous) = entry.previous {
                self.latest.insert(entry.local.id(), previous);
            } else {
                self.latest.remove(&entry.local.id());
            }
        }
    }
    #[cfg(test)]
    pub(super) fn proof_at(&self, index: usize) -> &Expr {
        &self.entries[index].proof
    }
}

#[cfg(test)]
#[path = "cps_image_frame_relations_tests.rs"]
mod tests;
