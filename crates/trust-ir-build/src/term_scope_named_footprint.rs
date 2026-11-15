// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Exact sparse external-index footprints, never scope or dependency authority.
use super::{Arc, Closer, Renaming};

#[derive(Clone, Default)]
struct ExactIndices {
    low: u64,
    high: Option<Arc<Vec<(u32, u64)>>>,
}

/// None is affirmative unknown/non-reuse, never the known-empty footprint.
/// High words are sorted, nonzero and allocated only from visited indices.
/// New merged high words and high-index probes pay the original closing
/// visitor before allocation/publication. Retained words share immutable Arcs.
#[derive(Clone)]
pub(super) struct NamedFootprint {
    indices: Option<ExactIndices>,
    pub(super) walk_extent: u32,
}
impl Default for NamedFootprint {
    fn default() -> Self {
        Self {
            indices: Some(ExactIndices::default()),
            walk_extent: 0,
        }
    }
}
impl NamedFootprint {
    pub(super) fn is_known(&self) -> bool {
        self.indices.is_some()
    }
    pub(super) fn under_parent(mut self) -> Self {
        self.walk_extent = self.walk_extent.saturating_add(1);
        self
    }
    pub(super) fn fits(&self, walk_depth: u32, limit: u32) -> bool {
        walk_depth
            .checked_add(self.walk_extent)
            .is_some_and(|depth| depth < limit)
    }
    pub(super) fn include_index(&mut self, index: u32, closer: &mut Closer<'_>) {
        if self.indices.is_none() {
            return;
        }
        if index < 64 {
            self.indices.as_mut().expect("known footprint").low |= 1u64 << index;
            return;
        }
        if !closer.visit() {
            self.indices = None;
            return;
        }
        let incoming = Self {
            indices: Some(ExactIndices {
                low: 0,
                high: Some(Arc::new(vec![(index >> 6, 1u64 << (index & 63))])),
            }),
            walk_extent: 0,
        };
        self.include(&incoming, closer);
    }
    pub(super) fn include(&mut self, incoming: &Self, closer: &mut Closer<'_>) {
        // Taking known state first makes every incomplete merge non-reusable.
        let Some(mut exact) = self.indices.take() else {
            return;
        };
        let Some(other) = &incoming.indices else {
            return;
        };
        exact.low |= other.low;
        let Some(right) = &other.high else {
            self.indices = Some(exact);
            return;
        };
        let Some(left) = &exact.high else {
            exact.high = Some(right.clone());
            self.indices = Some(exact);
            return;
        };
        if Arc::ptr_eq(left, right) {
            self.indices = Some(exact);
            return;
        }
        let (mut i, mut j) = (0, 0);
        let mut merged = Vec::new();
        while i < left.len() || j < right.len() {
            if !closer.visit() {
                return;
            }
            let word = match (left.get(i), right.get(j)) {
                (Some(&(a, bits)), Some(&(b, other))) if a == b => {
                    i += 1;
                    j += 1;
                    (a, bits | other)
                }
                (Some(&(a, bits)), Some(&(b, _))) if a < b => {
                    i += 1;
                    (a, bits)
                }
                (Some(_), Some(&word)) => {
                    j += 1;
                    word
                }
                (Some(&word), None) => {
                    i += 1;
                    word
                }
                (None, Some(&word)) => {
                    j += 1;
                    word
                }
                (None, None) => unreachable!("at least one sparse footprint word remains"),
            };
            merged.push(word);
        }
        exact.high = Some(Arc::new(merged));
        self.indices = Some(exact);
    }
    pub(super) fn matches(
        &self,
        previous: &Renaming,
        current: &Renaming,
        closer: &mut Closer<'_>,
    ) -> bool {
        let Some(exact) = &self.indices else {
            return false;
        };
        // At most64 cheap low-index probes, preserving the existing fast path.
        let mut low = exact.low;
        while low != 0 {
            let index = low.trailing_zeros();
            let Some(old) = previous.get(&index) else {
                return false;
            };
            if current.get(&index) != Some(old) {
                return false;
            }
            low &= low - 1;
        }
        if let Some(high) = &exact.high {
            for &(word, mut bits) in high.iter() {
                while bits != 0 {
                    if !closer.visit() {
                        return false;
                    }
                    let Some(index) = word
                        .checked_mul(64)
                        .and_then(|base| base.checked_add(bits.trailing_zeros()))
                    else {
                        return false;
                    };
                    let Some(old) = previous.get(&index) else {
                        return false;
                    };
                    if current.get(&index) != Some(old) {
                        return false;
                    }
                    bits &= bits - 1;
                }
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term_scope::{TermScope, TermScopeError, TermScopeLimits};
    #[test]
    fn unknown_footprint_is_never_empty_and_incomplete_merges_never_publish() {
        let scope = TermScope::new();
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let mut known = NamedFootprint::default();
        known.include_index(130, &mut closer);
        assert!(known.is_known());
        let unknown = NamedFootprint {
            indices: None,
            walk_extent: 0,
        };
        known.include(&unknown, &mut closer);
        known.include_index(0, &mut closer);
        assert!(!known.is_known());
        let map = Renaming::from([(130, 131)]);
        assert!(!known.matches(&map, &map, &mut closer));
        let mut partial = NamedFootprint::default();
        partial.include_index(64, &mut closer);
        closer.limits.max_visits = closer.stats.visits + 1;
        // One charged leaf allocation leaves no budget for the merged word.
        partial.include_index(130, &mut closer);
        assert!(!partial.is_known());
        assert_eq!(closer.error, Some(TermScopeError::VisitLimit));
    }
}
