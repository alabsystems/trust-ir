// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::scoped_local::LocalScope;
use clean_kernel::{
    Expr,
    expr::{ExprFolderOpt, FVarId},
};
use std::{
    collections::{HashMap, HashSet, hash_map::Entry},
    hash::{Hash, Hasher},
    sync::Arc,
};

#[derive(Clone)]
pub(super) struct DependencyKey(pub(super) Expr);
impl PartialEq for DependencyKey {
    fn eq(&self, other: &Self) -> bool {
        crate::proof_assembly::normalize::same_graph(&self.0, &other.0)
    }
}
impl Eq for DependencyKey {}
impl Hash for DependencyKey {
    fn hash<H: Hasher>(&self, hash: &mut H) {
        crate::proof_assembly::normalize::hash_graph(&self.0, hash);
    }
}

/// A materialized root is privately minted only after successful strict
/// closure in this same component. Its remaining FVars are a SUBSET of the
/// recorded external inventory; it is not a typing or exact dependency fact.
#[derive(Clone)]
pub(super) enum DependencyEntry {
    Exact(Arc<Vec<(u64, u64)>>),
    Materialized {
        external: Arc<Vec<FVarId>>,
        height_bound: u32,
    },
}
impl DependencyEntry {
    #[cfg(test)]
    fn exact(&self) -> &Arc<Vec<(u64, u64)>> {
        match self {
            Self::Exact(value) => value,
            Self::Materialized { .. } => panic!("expected an exact dependency entry"),
        }
    }
}

/// Producer-only overapproximation: collect every encountered FVar, including
/// named-binder formals. Extra declarations may be retained; no dependency can
/// be omitted by binder subtraction. This never changes capture ABIs or replay.
pub(super) struct NormalizationReferences {
    needed: HashSet<FVarId>,
    seen: HashMap<DependencyKey, u32>,
    pub(super) work: usize,
    limit: usize,
    depth: u32,
    height: u32,
    error: Option<&'static str>,
}
impl NormalizationReferences {
    pub(super) fn new(limit: usize) -> Self {
        Self {
            needed: HashSet::new(),
            seen: HashMap::new(),
            work: 0,
            limit,
            depth: 0,
            height: 0,
            error: None,
        }
    }
    pub(super) fn contains(&self, id: FVarId) -> bool {
        self.needed.contains(&id)
    }
    pub(super) fn scan(&mut self, expression: &Expr) -> Result<(), String> {
        self.height = 0;
        self.fold_expr_opt(expression);
        self.error.map_or(Ok(()), |error| {
            Err(format!("{error}: visits={}", self.work))
        })
    }
}
struct ReferenceStack<'a>(&'a mut NormalizationReferences);
impl ExprFolderOpt for ReferenceStack<'_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(expression)
    }
}
impl ExprFolderOpt for NormalizationReferences {
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        if self.error.is_some() {
            return None;
        }
        if self.work >= self.limit {
            self.error = Some("normalization dependency visit limit");
            return None;
        }
        self.work += 1;
        if !expression.has_fvar_quick() {
            return None;
        }
        if self.depth >= 16_384 {
            self.error = Some("normalization dependency depth limit");
            return None;
        }
        let key = DependencyKey(expression.clone());
        if let Some(&height) = self.seen.get(&key) {
            if self
                .depth
                .checked_add(height)
                .is_none_or(|depth| depth > 16_384)
            {
                self.error = Some("normalization dependency cached depth limit");
                return None;
            }
            self.height = self.height.max(height);
            return None;
        }
        let enclosing = std::mem::take(&mut self.height);
        self.depth += 1;
        ReferenceStack(self).fold_expr_opt(expression);
        self.depth -= 1;
        let height = self.height + 1;
        self.height = enclosing.max(height);
        if self.error.is_none() {
            // Height covers every FVar-bearing search path. Constructor-proven
            // FVar-free children need no reference search, as before.
            self.seen.insert(key, height);
        }
        None
    }
    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        self.needed.insert(id);
        None
    }
}

pub(super) struct CaptureDependencies<'a> {
    pub(super) scope: &'a LocalScope,
    pub(super) ambient: &'a HashSet<FVarId>,
    pub(super) work: &'a mut usize,
    pub(super) word_work: &'a mut usize,
    pub(super) cache: &'a mut HashMap<DependencyKey, DependencyEntry>,
    pub(super) retained_words: &'a mut usize,
    pub(super) retained_sets: &'a mut HashSet<usize>,
    pub(super) limit: usize,
    pub(super) needed: Arc<Vec<(u64, u64)>>,
    pub(super) empty: Arc<Vec<(u64, u64)>>,
    pub(super) error: Option<&'static str>,
    pub(super) depth: u32,
    pub(super) max_depth: u32,
    pub(super) materialized_reuse: bool,
    pub(super) bound: HashSet<FVarId>,
    // A guarded prune is relative to its ACTUAL ancestors. Never publish an
    // ordinary context-free summary above it, even after leaving that binder.
    pub(super) pruned: bool,
}
impl CaptureDependencies<'_> {
    fn has_work_room(&self) -> bool {
        (*self.work)
            .checked_add(*self.word_work)
            .is_some_and(|work| work < self.limit)
    }
    fn charge(&mut self, amount: usize) -> bool {
        let next = (*self.work).checked_add(amount);
        if next
            .and_then(|work| work.checked_add(*self.word_work))
            .is_none_or(|work| work > self.limit)
        {
            self.error = Some("aggregate materialized dependency guard work limit");
            return false;
        }
        *self.work = next.unwrap();
        true
    }
    pub(super) fn scan(&mut self, expression: &Expr) -> Result<(), String> {
        self.fold_expr_opt(expression);
        self.error.map_or(Ok(()), |error| {
            Err(format!(
                "{error}: visits={}, word unions={}, retained words={}",
                *self.work, *self.word_work, *self.retained_words
            ))
        })
    }
    fn scoped_children(&mut self, expression: &Expr) -> Option<Expr> {
        let Some(id) = self.scope.named_binder_id(expression) else {
            return self.fold_expr_opt_inner(expression);
        };
        let (ty, value, body) = match expression.kind() {
            clean_kernel::ExprKind::Lam(_, ty, body) | clean_kernel::ExprKind::Pi(_, ty, body) => {
                (ty, None, body)
            }
            clean_kernel::ExprKind::Let(_, ty, value, body, _) => (ty, Some(value), body),
            _ => return self.fold_expr_opt_inner(expression),
        };
        self.fold_expr_opt(ty);
        if let Some(value) = value {
            self.fold_expr_opt(value);
        }
        if self.error.is_some() {
            return None;
        }
        let inserted = if self.materialized_reuse {
            // Probe/insertion and eventual removal are paid before mutation.
            if !self.charge(3) {
                return None;
            }
            self.bound.insert(id)
        } else {
            false
        };
        let outside = std::mem::replace(&mut self.needed, self.empty.clone());
        self.fold_expr_opt(body);
        if inserted {
            self.bound.remove(&id);
        }
        if self.error.is_some() {
            self.needed = outside;
            return None;
        }
        if self.contains(id) {
            let mut retained = Vec::with_capacity(self.needed.len());
            for &(word, bits) in self.needed.iter() {
                if !self.has_work_room() {
                    self.error = Some("aggregate scoped dependency word-work limit");
                    break;
                }
                *self.word_work += 1;
                let bits = if word == id.as_u64() >> 6 {
                    bits & !(1 << (id.as_u64() & 63))
                } else {
                    bits
                };
                if bits != 0 {
                    retained.push((word, bits));
                }
            }
            self.needed = Arc::new(retained);
        }
        let body = std::mem::replace(&mut self.needed, outside);
        self.merge(&body);
        None
    }
    pub(super) fn contains(&self, id: FVarId) -> bool {
        let raw = id.as_u64();
        self.needed
            .binary_search_by_key(&(raw >> 6), |word| word.0)
            .ok()
            .is_some_and(|index| self.needed[index].1 & (1 << (raw & 63)) != 0)
    }
    fn merge(&mut self, incoming: &Arc<Vec<(u64, u64)>>) {
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
            if !self.has_work_room() {
                self.error = Some("aggregate component dependency word-work limit");
                return;
            }
            *self.word_work += 1;
            let word = if right == incoming.len()
                || (left < old.len() && old[left].0 < incoming[right].0)
            {
                let word = old[left];
                left += 1;
                word
            } else if left == old.len() || incoming[right].0 < old[left].0 {
                let word = incoming[right];
                right += 1;
                word
            } else {
                let word = (old[left].0, old[left].1 | incoming[right].1);
                left += 1;
                right += 1;
                word
            };
            result.push(word);
        }
        self.needed = Arc::new(result);
    }
}
struct DependencyStack<'a, 'b>(&'a mut CaptureDependencies<'b>);
impl ExprFolderOpt for DependencyStack<'_, '_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        self.0.scoped_children(expression)
    }
}
impl ExprFolderOpt for CaptureDependencies<'_> {
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        if self.error.is_some() {
            return None;
        }
        if !self.has_work_room() {
            self.error = Some("aggregate component dependency visit limit");
            return None;
        }
        *self.work += 1;
        if !expression.has_fvar_quick() {
            return None;
        }
        let key = DependencyKey(expression.clone());
        if let Some(known) = self.cache.get(&key).cloned() {
            match known {
                DependencyEntry::Exact(known) => {
                    self.merge(&known);
                    return None;
                }
                DependencyEntry::Materialized {
                    external,
                    height_bound,
                } if self.materialized_reuse
                    && self
                        .depth
                        .checked_add(height_bound)
                        .is_some_and(|depth| depth <= self.max_depth) =>
                {
                    // Charge all inventory probes before choosing a result;
                    // HashSet ordering must not select a failed work prefix.
                    let Some(probes) = external.len().checked_mul(2) else {
                        self.error = Some("materialized dependency guard overflow");
                        return None;
                    };
                    if !self.charge(probes) {
                        return None;
                    }
                    if external
                        .iter()
                        .all(|id| self.ambient.contains(id) || self.bound.contains(id))
                    {
                        self.pruned = true;
                        return None;
                    }
                }
                DependencyEntry::Materialized { .. } => {}
            }
        }
        if self.depth >= self.max_depth {
            self.error = Some("component dependency depth limit");
            return None;
        }
        let parent = std::mem::replace(&mut self.needed, self.empty.clone());
        self.depth += 1;
        DependencyStack(self).fold_expr_opt(expression);
        self.depth -= 1;
        let own = std::mem::replace(&mut self.needed, parent);
        if self.error.is_some() {
            return None;
        }
        // Several graph nodes can retain the same immutable dependency vector.
        // Charge its storage once, while keeping the independent entry bound.
        // Entries are never removed or replaced: their owning Arcs keep every
        // recorded allocation live, so an address cannot be recycled here.
        let allocation = Arc::as_ptr(&own) as usize;
        let shared = own.is_empty() || self.retained_sets.contains(&allocation);
        if !self.pruned
            && self.cache.len() < self.limit
            && (shared || own.len() <= self.limit.saturating_sub(*self.retained_words))
            && let Entry::Vacant(entry) = self.cache.entry(key)
        {
            entry.insert(DependencyEntry::Exact(own.clone()));
            if !shared {
                *self.retained_words += own.len();
                self.retained_sets.insert(allocation);
            }
        }
        self.merge(&own);
        None
    }
    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        // Ambient declarations are already in every component's context and
        // are never lifted as dynamic captures. The ambient set only grows:
        // older cached summaries may retain extra ambient IDs, but cannot
        // omit an ID that later becomes dynamic. Keep charging every visit.
        if !self.ambient.contains(&id) {
            self.needed = Arc::new(vec![(id.as_u64() >> 6, 1 << (id.as_u64() & 63))]);
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn constant(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    #[test]
    fn reference_forest_memo_checks_complete_search_height_under_a_deeper_parent() {
        let mut root = Expr::fvar(FVarId::new(7));
        for _ in 0..16_383 {
            root = Expr::app(constant("Nat.succ"), root);
        }
        let mut references = NormalizationReferences::new(100_000);
        references.scan(&root).unwrap();
        assert!(references.contains(FVarId::new(7)));
        let before = references.work;
        let deeper = Expr::app(constant("Nat.succ"), root);
        let error = references.scan(&deeper).unwrap_err();
        assert!(error.contains("cached depth limit"), "{error}");
        assert_eq!(
            references.work,
            before + 3,
            "failed memo probe stays charged"
        );
    }

    #[test]
    fn shared_dependency_storage_keeps_repeated_graph_scans_within_one_budget() {
        let mut scope = LocalScope::new();
        let locals: Vec<_> = (0..129)
            .map(|_| scope.try_local(constant("Nat")).unwrap())
            .collect();
        // Three different dependency words, propagated unchanged through
        // ordinary Nat.succ applications. Each wrapper has its own graph key.
        let mut term = Expr::apps(
            constant("Nat.add"),
            [
                Expr::apps(
                    constant("Nat.add"),
                    [locals[0].term().clone(), locals[64].term().clone()],
                ),
                locals[128].term().clone(),
            ],
        );
        for _ in 0..24 {
            term = Expr::app(constant("Nat.succ"), term);
        }
        let (mut work, mut word_work, mut retained_words) = (0, 0, 0);
        let mut cache = HashMap::new();
        let mut retained_sets = HashSet::new();
        let ambient = HashSet::new();
        let mut walker = CaptureDependencies {
            scope: &scope,
            ambient: &ambient,
            work: &mut work,
            word_work: &mut word_work,
            cache: &mut cache,
            retained_words: &mut retained_words,
            retained_sets: &mut retained_sets,
            limit: 64,
            needed: Arc::new(Vec::new()),
            empty: Arc::new(Vec::new()),
            error: None,
            depth: 0,
            max_depth: 64,
            materialized_reuse: false,
            bound: HashSet::new(),
            pruned: false,
        };
        walker.scan(&term).unwrap();
        let before = *walker.work;
        walker
            .scan(&term)
            .expect("the shared root must remain cached");
        assert_eq!(*walker.work, before + 1);
        for local in [&locals[0], &locals[64], &locals[128]] {
            assert!(walker.contains(local.id()));
        }
        assert!(!walker.contains(locals[1].id()));
        let unique: HashMap<_, _> = walker
            .cache
            .values()
            .map(|words| (Arc::as_ptr(words.exact()) as usize, words.exact().len()))
            .collect();
        assert_eq!(*walker.retained_words, unique.values().sum::<usize>());
        assert!(walker.cache.len() <= walker.limit);
        assert!(*walker.retained_words <= walker.limit);
        assert!(
            walker
                .cache
                .values()
                .map(|words| words.exact().len())
                .sum::<usize>()
                > walker.limit
        );

        // Reuse does not reset either part of the combined bill or suppress
        // refusal. The cold walk already spent word work as well as visits.
        while *walker.work + *walker.word_work < walker.limit {
            let before = *walker.work + *walker.word_work;
            walker.scan(&term).unwrap();
            assert_eq!(*walker.work + *walker.word_work, before + 1);
        }
        assert_eq!(*walker.work + *walker.word_work, walker.limit);
        let before = (*walker.work, *walker.word_work, walker.cache.len());
        assert!(walker.scan(&term).unwrap_err().contains("visit limit"));
        assert_eq!(
            (*walker.work, *walker.word_work, walker.cache.len()),
            before,
            "a refused cached scan cannot overdraw or publish"
        );
    }
    #[test]
    fn separately_allocated_equal_dependency_vectors_both_charge_storage() {
        let mut scope = LocalScope::new();
        let x = scope.try_local(constant("Nat")).unwrap();
        for _ in 0..64 {
            scope.try_local(constant("Nat")).unwrap();
        }
        let y = scope.try_local(constant("Nat")).unwrap();
        let first = Expr::apps(constant("Nat.add"), [x.term().clone(), y.term().clone()]);
        let second = Expr::apps(constant("Nat.add"), [y.term().clone(), x.term().clone()]);
        let (mut work, mut word_work, mut retained_words) = (0, 0, 0);
        let mut cache = HashMap::new();
        let mut retained_sets = HashSet::new();
        let ambient = HashSet::new();
        let mut walker = CaptureDependencies {
            scope: &scope,
            ambient: &ambient,
            work: &mut work,
            word_work: &mut word_work,
            cache: &mut cache,
            retained_words: &mut retained_words,
            retained_sets: &mut retained_sets,
            limit: 64,
            needed: Arc::new(Vec::new()),
            empty: Arc::new(Vec::new()),
            error: None,
            depth: 0,
            max_depth: 64,
            materialized_reuse: false,
            bound: HashSet::new(),
            pruned: false,
        };
        walker.scan(&first).unwrap();
        let first_words = walker.cache[&DependencyKey(first)].exact().clone();
        let before = *walker.retained_words;
        walker.scan(&second).unwrap();
        let second_words = walker.cache[&DependencyKey(second)].exact().clone();
        assert_eq!(first_words, second_words);
        assert!(!Arc::ptr_eq(&first_words, &second_words));
        assert_eq!(*walker.retained_words, before + second_words.len());
    }
}
