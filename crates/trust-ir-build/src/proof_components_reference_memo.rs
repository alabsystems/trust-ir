// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Bounded complete syntactic FVar sets. Issuers determine which immutable
//! retained-original graphs may enter a cache; this supplies no typing authority.
use super::DependencyKey;
use clean_kernel::{
    Expr,
    expr::{ExprFolderOpt, FVarId},
};
use std::{
    collections::{HashMap, HashSet, hash_map::Entry},
    sync::Arc,
};

type Words = Arc<Vec<(u64, u64)>>;
#[derive(Clone)]
struct Summary {
    words: Words,
    // Maximum relative depth of nodes whose FVar metadata requires descent.
    // A hit under a deeper parent must not bypass the original depth guard.
    height: u32,
}

pub(super) struct Cache {
    entries: HashMap<DependencyKey, Summary>,
    retained_words: usize,
    retained_sets: HashSet<usize>,
    bound: usize,
    failed: bool,
}
impl Cache {
    pub(super) fn new(bound: usize) -> Self {
        Self {
            entries: HashMap::new(),
            retained_words: 0,
            retained_sets: HashSet::new(),
            bound,
            failed: false,
        }
    }
    pub(super) fn poison(&mut self) {
        self.failed = true;
    }
    pub(super) fn has_failed(&self) -> bool {
        self.failed
    }
    pub(super) fn clear_entries(&mut self) {
        self.entries.clear();
        self.retained_sets.clear();
        self.retained_words = 0;
        // A changed base invalidates data; it cannot erase a failed scan.
    }
}

pub(super) struct Scan<'a> {
    cache: &'a mut Cache,
    needed: Words,
    empty: Words,
    pub(super) work: usize,
    limit: usize,
    depth: u32,
    max_depth: u32,
    height: u32,
    error: Option<&'static str>,
}
impl<'a> Scan<'a> {
    pub(super) fn new(cache: &'a mut Cache, limit: usize) -> Result<Self, String> {
        if cache.failed {
            return Err("normalization dependency cache retains a failed scan".into());
        }
        let empty = Arc::new(Vec::new());
        Ok(Self {
            cache,
            needed: empty.clone(),
            empty,
            work: 0,
            limit,
            depth: 0,
            max_depth: 16_384,
            height: 0,
            error: None,
        })
    }
    pub(super) fn contains(&self, id: FVarId) -> bool {
        let raw = id.as_u64();
        self.needed
            .binary_search_by_key(&(raw >> 6), |row| row.0)
            .ok()
            .is_some_and(|index| self.needed[index].1 & (1 << (raw & 63)) != 0)
    }
    pub(super) fn reserve_input_work(&mut self, work: usize) {
        self.limit = self.limit.saturating_sub(work);
    }
    pub(super) fn poison(&mut self) {
        self.cache.poison();
    }
    pub(super) fn charged_contains(&mut self, id: FVarId) -> Result<bool, String> {
        if !self.charge(1) {
            self.poison();
            return Err("normalization dependency visit limit".into());
        }
        Ok(self.contains(id))
    }
    pub(super) fn scan(&mut self, expression: &Expr) -> Result<(), String> {
        self.fold_expr_opt(expression);
        if let Some(error) = self.error {
            self.cache.failed = true;
            Err(format!("{error}: visits={}", self.work))
        } else {
            Ok(())
        }
    }
    fn charge(&mut self, amount: usize) -> bool {
        let Some(work) = self
            .work
            .checked_add(amount)
            .filter(|work| *work <= self.limit)
        else {
            self.error = Some("normalization dependency visit limit");
            return false;
        };
        self.work = work;
        true
    }
    fn merge(&mut self, incoming: &Words) {
        if self.error.is_some() || incoming.is_empty() || Arc::ptr_eq(&self.needed, incoming) {
            return;
        }
        if self.needed.is_empty() {
            self.needed = incoming.clone();
            return;
        }
        let old = self.needed.clone();
        let mut result = Vec::with_capacity(old.len().saturating_add(incoming.len()));
        let (mut left, mut right) = (0, 0);
        while left < old.len() || right < incoming.len() {
            if !self.charge(1) {
                return;
            }
            let row = if right == incoming.len()
                || (left < old.len() && old[left].0 < incoming[right].0)
            {
                let row = old[left];
                left += 1;
                row
            } else if left == old.len() || incoming[right].0 < old[left].0 {
                let row = incoming[right];
                right += 1;
                row
            } else {
                let row = (old[left].0, old[left].1 | incoming[right].1);
                left += 1;
                right += 1;
                row
            };
            result.push(row);
        }
        self.needed = Arc::new(result);
    }
}
impl ExprFolderOpt for Scan<'_> {
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        if self.error.is_some() || !self.charge(1) {
            return None;
        }
        if !expression.has_fvar_quick() {
            return None;
        }
        let key = DependencyKey(expression.clone());
        if let Some(known) = self.cache.entries.get(&key).cloned() {
            if self
                .depth
                .checked_add(known.height)
                .is_none_or(|depth| depth > self.max_depth)
            {
                self.error = Some("normalization dependency depth limit");
                return None;
            }
            self.height = self.height.max(known.height);
            self.merge(&known.words);
            return None;
        }
        if self.depth >= self.max_depth {
            self.error = Some("normalization dependency depth limit");
            return None;
        }
        let parent = std::mem::replace(&mut self.needed, self.empty.clone());
        let parent_height = std::mem::replace(&mut self.height, 0);
        self.depth += 1;
        ReferenceStack(self).fold_expr_opt(expression);
        self.depth -= 1;
        let own = std::mem::replace(&mut self.needed, parent);
        let height = std::mem::replace(&mut self.height, parent_height) + 1;
        if self.error.is_some() {
            return None;
        }
        self.height = self.height.max(height);
        // Retain exact graphs with their immutable summaries. No entry is
        // replaced/evicted, so retained-set addresses cannot be recycled.
        let allocation = Arc::as_ptr(&own) as usize;
        if self.cache.entries.len() < self.cache.bound {
            // Charge the actual storage lookup before making that probe, even
            // when its answer declines publication under the word bound.
            if !own.is_empty() && !self.charge(1) {
                return None;
            }
            let shared = own.is_empty() || self.cache.retained_sets.contains(&allocation);
            if shared || own.len() <= self.cache.bound.saturating_sub(self.cache.retained_words) {
                // Entry publication is another map probe; a unique retained
                // allocation also requires the set insertion probe.
                if !self.charge(if shared { 1 } else { 2 }) {
                    return None;
                }
                if let Entry::Vacant(entry) = self.cache.entries.entry(key) {
                    entry.insert(Summary {
                        words: own.clone(),
                        height,
                    });
                    if !shared {
                        self.cache.retained_words += own.len();
                        self.cache.retained_sets.insert(allocation);
                    }
                }
            }
        }
        self.merge(&own);
        None
    }
    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        let raw = id.as_u64();
        self.needed = Arc::new(vec![(raw >> 6, 1 << (raw & 63))]);
        None
    }
}

// Preserve the kernel folder's stack-growth boundary after overriding its
// public entry point for charged graph memoization.
struct ReferenceStack<'a, 'b>(&'a mut Scan<'b>);
impl ExprFolderOpt for ReferenceStack<'_, '_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(expression)
    }
}

#[cfg(test)]
#[path = "proof_components_complete_references_memo_tests.rs"]
mod tests;
