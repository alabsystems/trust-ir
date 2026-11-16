// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Complete summaries only for registered constructed-observation roots.
//! Embedded arbitrary inputs have only a fresh per-query height/visit map.
use super::*;
use clean_kernel::expr::ExprFolderOpt;
type Words = HashMap<u64, u64>;
#[path = "proof_components_generated_words.rs"]
mod words;
use words::Accumulator;
#[derive(Clone)]
pub(super) struct Completed {
    words: Arc<Words>,
    height: u32,
}
impl Completed {
    pub(super) fn contains(&self, id: FVarId) -> bool {
        let raw = id.as_u64();
        self.words
            .get(&(raw >> 6))
            .is_some_and(|bits| bits & (1 << (raw & 63)) != 0)
    }
}
pub(super) struct Memo {
    roots: HashMap<DependencyKey, Option<Completed>>,
    hashes: HashSet<u32>,
    hash_bits: Option<Vec<u64>>,
    retained_words: usize,
    bound: usize,
    failed: bool,
    nested_reuse: bool,
    shared_query: bool,
    shared_probes: bool,
    statistics: std::cell::Cell<words::Statistics>,
}
impl Memo {
    pub(super) fn new(bound: usize) -> Self {
        Self {
            roots: HashMap::new(),
            hashes: HashSet::new(),
            hash_bits: None,
            retained_words: 0,
            bound,
            failed: false,
            nested_reuse: true,
            shared_query: false,
            shared_probes: false,
            statistics: std::cell::Cell::new(words::Statistics::default()),
        }
    }
    #[cfg(test)]
    pub(super) fn root_only(bound: usize) -> Self {
        let mut memo = Self::new(bound);
        memo.nested_reuse = false;
        memo
    }
    #[cfg(test)]
    pub(super) fn root_only_shared_query(bound: usize) -> Self {
        let mut memo = Self::root_only(bound);
        memo.shared_query = true;
        memo
    }
    pub(super) fn shared_children(bound: usize) -> Self {
        let mut memo = Self::new(bound);
        memo.shared_query = true;
        memo.shared_probes = true;
        memo
    }
    pub(super) fn hash_filter_words(bound: usize) -> usize {
        (bound / 32).clamp(1, 128).next_power_of_two()
    }
    /// The caller prepays these cells and their header before construction.
    /// A set bit is only a possible hash match, never a completed root fact.
    pub(super) fn shared_children_bitmap(bound: usize) -> Self {
        let mut memo = Self::shared_children(bound);
        memo.hash_bits = Some(vec![0; Self::hash_filter_words(bound)]);
        memo
    }
    fn may_have_hash(&self, hash: u32) -> bool {
        if let Some(bits) = &self.hash_bits {
            let (word, mask) = filter_slot(hash, bits.len());
            bits[word] & mask != 0
        } else {
            self.hashes.contains(&hash)
        }
    }
    pub(super) fn statistics(&self) -> String {
        format!(
            "nested_reuse={} shared_query={} shared_probes={} bitmap_words={} {:?}",
            self.nested_reuse,
            self.shared_query,
            self.shared_probes,
            self.hash_bits.as_ref().map_or(0, Vec::len),
            self.statistics.get()
        )
    }
    pub(super) fn has_failed(&self) -> bool {
        self.failed
    }
    pub(super) fn poison(&mut self) {
        self.failed = true;
    }
    pub(super) fn register(&mut self, root: &Expr) -> Result<(), String> {
        if self.failed {
            return Err("constructed observation retains a failed scan".into());
        }
        if self.roots.len() >= self.bound && !self.roots.contains_key(&DependencyKey(root.clone()))
        {
            return Err("constructed observation root inventory limit".into());
        }
        if self.nested_reuse {
            if let Some(bits) = &mut self.hash_bits {
                let (word, mask) = filter_slot(root.hash_cached(), bits.len());
                bits[word] |= mask;
            } else {
                self.hashes.insert(root.hash_cached());
            }
        }
        self.roots
            .entry(DependencyKey(root.clone()))
            .or_insert(None);
        Ok(())
    }
    pub(super) fn scan(&self, root: &Expr, limit: usize) -> (Result<Completed, String>, usize) {
        if self.failed {
            return (
                Err("constructed observation retains a failed scan".into()),
                0,
            );
        }
        if limit < 2 {
            return (Err("generated reference work limit".into()), 0);
        }
        match self.roots.get(&DependencyKey(root.clone())) {
            Some(Some(known)) => return (Ok(known.clone()), 2),
            None => return (Err("unregistered constructed observation root".into()), 2),
            Some(None) => {}
        }
        let mut scan = Scan {
            memo: self,
            seen: HashMap::new(),
            needed: Accumulator::default(),
            work: 2,
            limit,
            depth: 0,
            height: 0,
            error: None,
            root: root as *const Expr as usize,
            root_lookup_avoided: false,
        };
        scan.fold_expr_opt(root);
        if scan.error.is_none() && scan.needed.requires_header() {
            scan.charge(1);
        } // allocate a completed root-set header only for owned words
        let mut statistics = scan.needed.statistics();
        statistics.root_lookups_avoided = usize::from(scan.root_lookup_avoided);
        let mut totals = self.statistics.get();
        totals.include(statistics);
        self.statistics.set(totals);
        let work = scan.work;
        let result = match scan.error {
            Some(error) => Err(format!("{error}: visits={work}")),
            None => Ok(Completed {
                words: scan.needed.finish(),
                height: scan.height,
            }),
        };
        (result, work)
    }
    pub(super) fn publish(&mut self, root: &Expr, completed: Completed) -> Result<(), String> {
        if self.failed {
            return Err("constructed observation retains a failed scan".into());
        }
        let slot = self
            .roots
            .get_mut(&DependencyKey(root.clone()))
            .ok_or("unregistered constructed observation root")?;
        if slot.is_none() && completed.words.len() <= self.bound.saturating_sub(self.retained_words)
        {
            self.retained_words += completed.words.len();
            *slot = Some(completed);
        }
        Ok(())
    }
}
fn filter_slot(hash: u32, words: usize) -> (usize, u64) {
    // The private constructor chooses 1..128 power-of-two words. Mix both
    // halves of the cached hash before projecting to that fixed bit range.
    let mixed = (hash ^ (hash >> 16)).wrapping_mul(0x9e37_79b9);
    let bit = mixed as usize & (words * 64 - 1);
    (bit >> 6, 1u64 << (bit & 63))
}
// DependencyKey requires identical immediate child Arc allocations. A retained
// key owns a CLONE of each such field, independently of the live query node.
// Therefore any singleton child proves only that this node cannot match a
// registered key. Shared children still require the exact existing lookup.
// All other shapes retain the old behavior if the lookup census expands.
fn registered_children_may_match(expression: &Expr) -> bool {
    match expression.kind() {
        clean_kernel::ExprKind::App(a, b)
        | clean_kernel::ExprKind::Lam(_, a, b)
        | clean_kernel::ExprKind::Pi(_, a, b) => {
            Arc::strong_count(a) > 1 && Arc::strong_count(b) > 1
        }
        clean_kernel::ExprKind::Let(_, a, b, c, _) => {
            Arc::strong_count(a) > 1 && Arc::strong_count(b) > 1 && Arc::strong_count(c) > 1
        }
        _ => true,
    }
}
struct Scan<'a> {
    memo: &'a Memo,
    seen: HashMap<usize, u32>,
    needed: Accumulator,
    work: usize,
    limit: usize,
    depth: u32,
    height: u32,
    error: Option<&'static str>,
    root: usize,
    root_lookup_avoided: bool,
}
impl Scan<'_> {
    fn charge(&mut self, amount: usize) -> bool {
        let Some(next) = self
            .work
            .checked_add(amount)
            .filter(|work| *work <= self.limit)
        else {
            self.error = Some("generated reference work limit");
            return false;
        };
        self.work = next;
        true
    }
    fn word(&mut self, word: u64, bits: u64) {
        if let Err(error) = self.needed.word(word, bits, &mut self.work, self.limit) {
            self.error = Some(error);
        }
    }
    fn include(&mut self, summary: &Completed) {
        if let Err(error) = self
            .needed
            .include(&summary.words, &mut self.work, self.limit)
        {
            self.error = Some(error);
        }
    }
    fn known_height(&mut self, height: u32) -> bool {
        if self
            .depth
            .checked_add(height)
            .is_none_or(|height| height > 16_384)
        {
            self.error = Some("generated reference depth limit");
            return false;
        }
        self.height = self.height.max(height);
        true
    }
    fn walk(&mut self, expression: &Expr, incoming: Option<&Arc<Expr>>) -> Option<Expr> {
        if self.error.is_some() || !self.charge(1) {
            return None;
        }
        if self.depth >= 16_384 {
            self.error = Some("generated reference depth limit");
            return None;
        }
        // Scalar leaves have complete height one and no graph children to
        // revisit. Avoid allocating temporary graph entries for these nodes.
        match expression.kind() {
            clean_kernel::ExprKind::FVar(id) => {
                let raw = id.as_u64();
                self.word(raw >> 6, 1 << (raw & 63));
                self.height = self.height.max(1);
                return None;
            }
            clean_kernel::ExprKind::BVar(_)
            | clean_kernel::ExprKind::Sort(_)
            | clean_kernel::ExprKind::Const(..)
            | clean_kernel::ExprKind::Lit(_)
            | clean_kernel::ExprKind::SProp
            | clean_kernel::ExprKind::CubicalInterval
            | clean_kernel::ExprKind::CubicalI0
            | clean_kernel::ExprKind::CubicalI1 => {
                self.height = self.height.max(1);
                return None;
            }
            _ => {}
        }
        // This is only a hint to decline temporary storage, never a subtree
        // certificate. Unique nodes still receive the complete walk. A changed
        // count can only cause extra visits, whose work and depth remain paid.
        let memoize =
            !self.memo.shared_query || incoming.is_some_and(|child| Arc::strong_count(child) > 1);
        // The immutable actual root pins every address until this query ends.
        let address = expression as *const Expr as usize;
        if memoize && let Some(height) = self.seen.get(&address).copied() {
            self.known_height(height);
            return None;
        }
        if self.memo.nested_reuse
            && address == self.root
            && matches!(
                expression.kind(),
                clean_kernel::ExprKind::App(..)
                    | clean_kernel::ExprKind::Lam(..)
                    | clean_kernel::ExprKind::Pi(..)
                    | clean_kernel::ExprKind::Let(..)
            )
        {
            self.root_lookup_avoided = true;
        }
        if self.memo.nested_reuse
            && address != self.root
            && (!self.memo.shared_probes || registered_children_may_match(expression))
            && matches!(
                expression.kind(),
                clean_kernel::ExprKind::App(..)
                    | clean_kernel::ExprKind::Lam(..)
                    | clean_kernel::ExprKind::Pi(..)
                    | clean_kernel::ExprKind::Let(..)
            )
        {
            if self.memo.hash_bits.is_none() && !self.charge(1) {
                return None;
            } // HashSet probe; the bitmap's O(1) guard uses the paid node visit
            if self.memo.may_have_hash(expression.hash_cached()) {
                if !self.charge(2) {
                    return None;
                } // exact graph probe/pin
                let known = self
                    .memo
                    .roots
                    .get(&DependencyKey(expression.clone()))
                    .and_then(|slot| slot.as_ref());
                if let Some(known) = known {
                    if !self.known_height(known.height) {
                        return None;
                    }
                    self.include(known);
                    if self.error.is_none() && memoize && self.charge(1) {
                        self.seen.insert(address, known.height);
                    }
                    return None;
                }
            }
        }
        let parent = std::mem::take(&mut self.height);
        self.depth += 1;
        Stack(self).fold_expr_opt(expression);
        self.depth -= 1;
        let height = self.height + 1;
        self.height = parent.max(height);
        if self.error.is_none() && memoize && self.charge(1) {
            self.seen.insert(address, height);
        }
        None
    }
}
struct Stack<'a, 'b>(&'a mut Scan<'b>);
impl ExprFolderOpt for Stack<'_, '_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(expression)
    }
}
impl ExprFolderOpt for Scan<'_> {
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        self.walk(expression, None)
    }
    fn fold_expr_arc_opt(&mut self, expression: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.walk(expression, Some(expression)).map(Arc::new)
    }
    fn fold_binder_body_arc_opt(&mut self, expression: &Arc<Expr>) -> Option<Arc<Expr>> {
        // Reference collection counts every syntactic FVar under binders;
        // there is no binder-dependent scope or index translation here.
        self.fold_expr_arc_opt(expression)
    }
    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        let raw = id.as_u64();
        self.word(raw >> 6, 1 << (raw & 63));
        None
    }
}

#[cfg(test)]
#[path = "proof_components_generated_hash_filter_tests.rs"]
mod hash_filter_tests;

#[cfg(test)]
mod tests {
    use super::*;
    fn shell(shape: usize, body: Expr) -> Expr {
        match shape {
            0 => Expr::app(Expr::const_str("Nat.succ"), body),
            1 => Expr::lam(
                clean_kernel::BinderInfo::Default,
                Expr::const_str("Nat"),
                body,
            ),
            2 => Expr::pi(
                clean_kernel::BinderInfo::Default,
                Expr::const_str("Nat"),
                body,
            ),
            3 => Expr::let_named(
                clean_kernel::Name::from_string("x"),
                Expr::const_str("Nat"),
                Expr::nat_lit(0),
                body,
                false,
            ),
            _ => unreachable!(),
        }
    }

    #[test]
    fn shared_children_guard_is_only_an_exact_registered_key_miss_condition() {
        for shape in 0..4 {
            let root = shell(shape, Expr::nat_lit(0));
            assert!(!registered_children_may_match(&root));
            let retained = root.clone();
            assert!(registered_children_may_match(&root));
            assert!(same_graph(&root, &retained));
            let separate = shell(shape, Expr::nat_lit(0));
            assert_eq!(root.hash_cached(), separate.hash_cached());
            assert!(!same_graph(&root, &separate));
            assert!(!registered_children_may_match(&separate));
            drop(retained);
            assert!(!registered_children_may_match(&root));
        }
    }

    #[test]
    fn shared_children_omits_provably_missed_census_without_losing_empty_root_hits() {
        let mut unique = Expr::fvar(FVarId::new(129));
        for _ in 0..128 {
            unique = Expr::app(Expr::const_str("Nat.succ"), unique);
        }
        let mut old = Memo::new(100_000);
        let mut guarded = Memo::shared_children(100_000);
        guarded.shared_query = false; // isolate only the census change
        old.register(&unique).unwrap();
        guarded.register(&unique).unwrap();
        let (old_result, old_work) = old.scan(&unique, 100_000);
        let (new_result, new_work) = guarded.scan(&unique, 100_000);
        let (old_result, new_result) = (old_result.unwrap(), new_result.unwrap());
        assert_eq!(old_result.words, new_result.words);
        assert_eq!(old_result.height, new_result.height);
        assert_eq!(old_work - new_work, 127);
        // Empty summaries had zero word adoptions in the rejected root-only
        // source run. They still save a full deep walk and MUST remain hits.
        for shape in 0..4 {
            let mut deep = Expr::nat_lit(0);
            for _ in 0..300 {
                deep = Expr::app(Expr::const_str("Nat.succ"), deep);
            }
            let child = shell(shape, deep);
            let root = Expr::app(Expr::const_str("wrapper"), child.clone());
            let mut old = Memo::new(100_000);
            let mut guarded = Memo::shared_children(100_000);
            let mut disabled = Memo::root_only(100_000);
            for memo in [&mut old, &mut guarded, &mut disabled] {
                memo.register(&child).unwrap();
                let result = memo.scan(&child, 100_000).0.unwrap();
                memo.publish(&child, result).unwrap();
                memo.register(&root).unwrap();
            }
            let (old_result, old_work) = old.scan(&root, 100_000);
            let (new_result, new_work) = guarded.scan(&root, 100_000);
            let (old_result, new_result) = (old_result.unwrap(), new_result.unwrap());
            assert!(old_result.words.is_empty() && new_result.words.is_empty());
            assert_eq!(old_result.height, 303);
            assert_eq!(old_result.height, new_result.height);
            assert!(new_work <= old_work && old_work < 20, "shape {shape}");
            assert!(disabled.scan(&root, 100_000).1 > 600);
        }
    }

    #[test]
    fn shared_children_every_query_cutoff_is_paid_without_root_publication() {
        let mut root = Expr::fvar(FVarId::new(129));
        for _ in 0..32 {
            root = Expr::app(Expr::const_str("Nat.succ"), root);
        }
        let mut memo = Memo::shared_children(1000);
        memo.register(&root).unwrap();
        let (complete, exact_work) = memo.scan(&root, 1000);
        assert_eq!(complete.unwrap().height, 33);
        for limit in 0..=exact_work {
            let (result, work) = memo.scan(&root, limit);
            assert!(work <= limit);
            assert_eq!(result.is_ok(), limit == exact_work, "cutoff {limit}");
            assert!(memo.roots.values().all(Option::is_none));
        }
    }

    #[test]
    fn shared_query_unique_chain_omits_only_unused_temporary_entries() {
        let mut root = Expr::fvar(FVarId::new(129));
        for _ in 0..128 {
            root = Expr::app(Expr::const_str("Nat.succ"), root);
        }
        let mut all = Memo::root_only(100_000);
        let mut shared = Memo::root_only_shared_query(100_000);
        all.register(&root).unwrap();
        shared.register(&root).unwrap();
        let (old, old_work) = all.scan(&root, 100_000);
        let (new, new_work) = shared.scan(&root, 100_000);
        let (old, new) = (old.unwrap(), new.unwrap());
        assert_eq!(old.words, new.words);
        assert_eq!(new.height, 129);
        assert_eq!(old.height, new.height);
        // Registered root clones share its immediate child; the other126
        // unique children and the non-Arc query root need no temporary entry.
        assert_eq!(old_work - new_work, 127);
        assert!(new.contains(FVarId::new(129)));
        shared.publish(&root, new).unwrap();
        assert_eq!(shared.scan(&root, 100_000).1, 2);
    }

    #[test]
    fn shared_query_real_binary_dag_remains_linear_and_complete() {
        let mut child = Arc::new(Expr::fvar(FVarId::new(129)));
        for _ in 0..100 {
            child = Arc::new(Expr::app_arc(child.clone(), child));
        }
        let root = child.as_ref().clone();
        let mut memo = Memo::root_only_shared_query(10_000);
        memo.register(&root).unwrap();
        let (result, work) = memo.scan(&root, 10_000);
        let result = result.unwrap();
        assert_eq!(result.height, 101);
        assert_eq!(result.words.len(), 1);
        assert!(result.contains(FVarId::new(129)));
        assert!(work < 1000, "shared paths must not expand exponentially");
    }

    #[test]
    fn shared_query_many_parent_fields_reuse_a_deep_otherwise_unique_chain() {
        let mut child = Expr::fvar(FVarId::new(129));
        for _ in 0..1024 {
            child = Expr::app(Expr::const_str("Nat.succ"), child);
        }
        let child = Arc::new(child);
        assert_eq!(
            child.as_ref() as *const Expr,
            Arc::as_ptr(&child),
            "the child hook sees the allocation, not the parent's Arc field"
        );
        for distinct_wrappers in [false, true] {
            let mut root = Expr::const_str("many");
            for _ in 0..128 {
                let argument = if distinct_wrappers {
                    Arc::new(child.as_ref().clone())
                } else {
                    child.clone()
                };
                root = Expr::app_arc(Arc::new(root), argument);
            }
            let mut memo = Memo::root_only_shared_query(10_000);
            memo.register(&root).unwrap();
            let (result, work) = memo.scan(&root, 10_000);
            let result = result.unwrap();
            assert_eq!(result.height, 1153);
            assert_eq!(result.words.len(), 1);
            assert!(result.contains(FVarId::new(129)));
            assert!(work < 5000, "wrapper clones={distinct_wrappers}");
            let mut scan = parts(&memo, 10_000);
            scan.root = &root as *const Expr as usize;
            scan.fold_expr_opt(&root);
            assert!(scan.error.is_none());
            let retained = if distinct_wrappers {
                let clean_kernel::ExprKind::App(_, tail) = child.kind() else {
                    unreachable!()
                };
                Arc::as_ptr(tail)
            } else {
                Arc::as_ptr(&child)
            };
            assert!(
                scan.seen.contains_key(&(retained as usize)),
                "the actual walk retains the shared allocation's complete height"
            );
        }
    }

    #[test]
    fn shared_query_second_use_checks_complete_height_at_the_deeper_edge() {
        let mut child = Expr::nat_lit(0);
        for _ in 0..300 {
            child = Expr::app(Expr::const_str("Nat.succ"), child);
        }
        let child = Arc::new(child);
        let mut deep = child.clone();
        for _ in 0..16_084 {
            deep = Arc::new(Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), deep));
        }
        let root = Expr::app_arc(child.clone(), deep);
        let mut memo = Memo::root_only_shared_query(100_000);
        memo.register(&root).unwrap();
        let mut scan = parts(&memo, 100_000);
        scan.root = &root as *const Expr as usize;
        scan.fold_expr_opt(&root);
        assert_eq!(
            scan.seen.get(&(Arc::as_ptr(&child) as usize)),
            Some(&301),
            "the shallow first use completed before the failing deeper edge"
        );
        assert_eq!(scan.error, Some("generated reference depth limit"));
        assert!(memo.roots.values().all(Option::is_none));
    }

    #[test]
    fn shared_query_every_work_cutoff_is_paid_without_partial_publication() {
        let mut root = Expr::fvar(FVarId::new(129));
        for _ in 0..32 {
            root = Expr::app(Expr::const_str("Nat.succ"), root);
        }
        let mut memo = Memo::root_only_shared_query(1000);
        memo.register(&root).unwrap();
        let (complete, exact_work) = memo.scan(&root, 1000);
        assert_eq!(complete.unwrap().height, 33);
        for limit in 0..=exact_work {
            let (result, work) = memo.scan(&root, limit);
            assert!(work <= limit);
            assert_eq!(result.is_ok(), limit == exact_work, "cutoff {limit}");
            assert!(memo.roots.values().all(Option::is_none));
        }
    }

    #[test]
    fn root_only_fresh_walk_omits_actual_nested_census_probes_and_keeps_exact_answer() {
        let mut root = Expr::fvar(FVarId::new(129));
        for _ in 0..128 {
            root = Expr::app(Expr::const_str("Nat.succ"), root);
        }
        let mut nested = Memo::new(100_000);
        let mut root_only = Memo::root_only(100_000);
        nested.register(&root).unwrap();
        root_only.register(&root).unwrap();
        assert!(root_only.hashes.is_empty());
        let (old, old_work) = nested.scan(&root, 100_000);
        let (new, new_work) = root_only.scan(&root, 100_000);
        let (old, new) = (old.unwrap(), new.unwrap());
        assert_eq!(old.height, new.height);
        assert_eq!(old.words, new.words);
        // Exactly127 proper compound children need no hash-census lookup.
        assert_eq!(old_work - new_work, 127);
        root_only.publish(&root, new).unwrap();
        let (_, hot) = root_only.scan(&root, 100_000);
        assert_eq!(hot, 2, "the exact registered root still reuses its summary");
    }

    #[test]
    fn root_only_and_nested_policies_retain_exact_refs_and_complete_child_height() {
        let mut child = Expr::fvar(FVarId::new(1));
        for _ in 0..300 {
            child = Expr::app(Expr::const_str("Nat.succ"), child);
        }
        let root = Expr::apps(
            Expr::const_str("Nat.add"),
            [child.clone(), Expr::fvar(FVarId::new(129))],
        );
        let mut nested = Memo::new(100_000);
        let mut root_only = Memo::root_only(100_000);
        for memo in [&mut nested, &mut root_only] {
            memo.register(&child).unwrap();
            let (summary, _) = memo.scan(&child, 100_000);
            memo.publish(&child, summary.unwrap()).unwrap();
            memo.register(&root).unwrap();
        }
        let (old, old_work) = nested.scan(&root, 100_000);
        let (new, new_work) = root_only.scan(&root, 100_000);
        let (old, new) = (old.unwrap(), new.unwrap());
        assert_eq!(old.words, new.words);
        assert_eq!(old.height, new.height);
        assert!(new.contains(FVarId::new(1)) && new.contains(FVarId::new(129)));
        assert!(
            old_work < new_work,
            "nested reuse remains useful when a child actually repeats"
        );
    }

    fn parts(memo: &Memo, limit: usize) -> Scan<'_> {
        Scan {
            memo,
            seen: HashMap::new(),
            needed: Accumulator::default(),
            work: 0,
            limit,
            depth: 0,
            height: 0,
            error: None,
            root: 0,
            root_lookup_avoided: false,
        }
    }
    #[test]
    fn generated_root_scalar_visits_need_no_temporary_graph_storage_and_keep_depth_guard() {
        let memo = Memo::new(100);
        let mut scan = parts(&memo, 100);
        for root in [
            Expr::nat_lit(0),
            Expr::const_str("Nat"),
            Expr::fvar(FVarId::new(129)),
            Expr::bvar(0),
        ] {
            scan.fold_expr_opt(&root);
        }
        assert!(scan.seen.is_empty());
        assert_eq!(scan.height, 1);
        assert!(scan.needed.get(&2).is_some_and(|bits| bits & 2 != 0));
        scan.depth = 16_384;
        scan.fold_expr_opt(&Expr::nat_lit(0));
        assert!(scan.error.unwrap().contains("depth limit"));
    }
    #[test]
    fn generated_root_existing_word_union_does_not_allocate_and_vacant_failure_is_paid() {
        let memo = Memo::new(100);
        let mut scan = parts(&memo, 5);
        scan.word(0, 1);
        assert_eq!(scan.work, 3);
        scan.word(0, 1);
        assert_eq!(scan.work, 4);
        scan.word(0, 2);
        assert_eq!(scan.work, 5);
        assert_eq!(scan.needed.get(&0), Some(&3));
        scan.word(1, 1);
        assert!(scan.error.is_some());
        assert_eq!(scan.needed.len(), 1);
    }
    #[test]
    fn generated_root_word_accumulator_matches_independent_multiword_union() {
        let mut seed = 0x5eed_u64;
        for _ in 0..1000 {
            let memo = Memo::new(1000);
            let mut scan = parts(&memo, 100_000);
            let mut expected = std::collections::BTreeMap::new();
            for _ in 0..4 {
                for word in 0..12u64 {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                    let bits = (seed >> 32) & 15;
                    if bits != 0 {
                        scan.word(word, bits);
                        *expected.entry(word).or_insert(0) |= bits;
                    }
                }
            }
            assert!(scan.error.is_none());
            assert_eq!(
                scan.needed
                    .iter()
                    .map(|(&word, &bits)| (word, bits))
                    .collect::<std::collections::BTreeMap<_, _>>(),
                expected
            );
        }
    }
    #[test]
    fn generated_root_first_walk_retains_only_registered_roots_and_checks_embedded_inputs() {
        let input = Expr::fvar(FVarId::new(9));
        let mut root = input.clone();
        for _ in 0..300 {
            root = Expr::app(Expr::const_str("Nat.succ"), root);
        }
        let mut memo = Memo::new(100_000);
        memo.register(&root).unwrap();
        let (cold, cold_work) = memo.scan(&root, 100_000);
        let cold = cold.unwrap();
        assert!(cold.contains(FVarId::new(9)));
        memo.publish(&root, cold).unwrap();
        assert_eq!(memo.roots.len(), 1);
        assert!(!memo.roots.contains_key(&DependencyKey(input)));
        let (hot, hot_work) = memo.scan(&root, 100_000);
        assert!(hot.unwrap().contains(FVarId::new(9)));
        assert!(hot_work > 0 && hot_work < cold_work);
    }
    #[test]
    fn generated_root_child_summaries_keep_every_reference_and_parent_height() {
        let mut left = Expr::fvar(FVarId::new(1));
        for _ in 0..300 {
            left = Expr::app(Expr::const_str("Nat.succ"), left);
        }
        let mut memo = Memo::new(100_000);
        memo.register(&left).unwrap();
        let known = memo.scan(&left, 100_000).0.unwrap();
        memo.publish(&left, known).unwrap();
        let root = Expr::apps(
            Expr::const_str("Nat.add"),
            [left, Expr::fvar(FVarId::new(129))],
        );
        memo.register(&root).unwrap();
        let result = memo.scan(&root, 100_000).0.unwrap();
        assert!(result.contains(FVarId::new(1)) && result.contains(FVarId::new(129)));
        assert!(result.height > 301);
        assert_eq!(memo.roots.len(), 2);
    }
    #[test]
    fn generated_root_word_failure_has_no_partial_storage_or_failed_publication() {
        let memo = Memo::new(1000);
        let mut scan = parts(&memo, 1);
        scan.word(0, 1);
        assert!(scan.needed.is_empty());
        assert_eq!(
            scan.work, 1,
            "pay the failed storage probe without inserting"
        );
        assert!(scan.error.is_some());
        let root = Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(FVarId::new(1)));
        let mut memo = Memo::new(1000);
        memo.register(&root).unwrap();
        assert!(memo.scan(&root, 3).0.is_err());
        assert!(memo.roots.values().all(Option::is_none));
        memo.poison();
        assert!(memo.scan(&root, 100_000).0.is_err());
    }

    #[test]
    fn fresh_root_probe_is_removed_without_skipping_its_visit_references_or_height() {
        let root = Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(FVarId::new(129)));
        let mut memo = Memo::new(1000);
        memo.register(&root).unwrap();
        let mut old = parts(&memo, 1000);
        old.fold_expr_opt(&root);
        let mut current = parts(&memo, 1000);
        current.root = &root as *const Expr as usize;
        current.fold_expr_opt(&root);
        assert!(old.error.is_none() && current.error.is_none());
        assert_eq!(old.height, current.height);
        assert_eq!(old.needed.words(), current.needed.words());
        assert_eq!(
            old.work,
            current.work + 3,
            "only the already-decided hash census and graph probe/pin disappear"
        );
    }
}
