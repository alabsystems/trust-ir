// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Private capture pruning from ACTUAL successful materialization outputs.
//! The external inventory is only an upper bound. No raw graph, closed-term,
//! dependency or typing certificate is accepted from a caller.
use super::*;
use std::collections::hash_map::Entry;

impl ProofComponents {
    pub(super) fn remember_materialized_capture_roots(
        &mut self,
        external: &[ScopedLocal],
        roots: &[Expr],
        visits: usize,
    ) -> Result<(), String> {
        // A successful canonical projection traversal visits every distinct
        // input node before a per-call memo can skip that graph. Thus its
        // aggregate visits upper-bound every complete original input path.
        // Binder-to-BVar translation does not increase expression height.
        // Keep the deliberately conservative bound; no approximate metadata.
        if self.materialized_capture_failed || visits == 0 || visits > 16_384 {
            return Ok(());
        }
        self.spend_context_work(roots.len())?;
        let available = self
            .limits
            .operations
            .saturating_sub(self.dependencies.len());
        let count = roots
            .iter()
            .filter(|root| {
                root.has_fvar_quick()
                    && !self
                        .dependencies
                        .contains_key(&DependencyKey((*root).clone()))
            })
            .count()
            .min(available);
        if count == 0 {
            return Ok(());
        }
        // Count before allocating so the retained external vector has its
        // actual capacity paid. The owner/duplicate admission already passed
        // in the SAME canonical call that returned these exact roots.
        self.spend_context_work(external.len())?;
        let nonambient = external
            .iter()
            .filter(|local| !self.base_ids.contains(&local.id()))
            .count();
        let fee = external
            .len()
            .checked_add(nonambient)
            .and_then(|n| n.checked_add(roots.len())) // second bounded root scan
            .and_then(|n| n.checked_add(2)) // Vec + Arc headers
            .and_then(|n| n.checked_add(count.checked_mul(2)?)) // root pin + entry
            .ok_or("materialized capture publication work overflow")?;
        self.spend_context_work(fee)?;
        let mut required = Vec::with_capacity(nonambient);
        for local in external {
            if !self.base_ids.contains(&local.id()) {
                required.push(local.id());
            }
        }
        let required = Arc::new(required);
        let mut published = 0;
        for root in roots {
            if published >= count {
                break;
            }
            if root.has_fvar_quick()
                && let Entry::Vacant(entry) = self.dependencies.entry(DependencyKey(root.clone()))
            {
                entry.insert(DependencyEntry::Materialized {
                    external: required.clone(),
                    height_bound: visits as u32,
                });
                published += 1;
            }
        }
        self.materialized_capture_roots += published;
        Ok(())
    }
}
