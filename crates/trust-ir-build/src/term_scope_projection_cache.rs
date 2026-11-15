// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded candidate storage and exact, charged contextual/declaration guards.
//! Observations never validate, promote or re-probe a retained candidate.

use super::observations::{CandidateShape, DependencyRejection};
use super::*;

#[derive(Default)]
pub(super) struct ContextCandidates {
    primary: HashMap<usize, ContextEntry>,
    // No buckets for ordinary single-projection DAGs. Retain at most one
    // displaced, distinct projection per address, not every binder context.
    spare: HashMap<usize, ContextEntry>,
}

#[derive(Clone, Copy)]
pub(super) enum RebaseMode {
    Ordinary,
    NamedOnly,
}

impl ContextCandidates {
    pub(super) fn get(
        &self,
        address: usize,
        binder_depth: u32,
        ordinary_count: usize,
    ) -> Option<&ContextEntry> {
        let exact = |entry: &&ContextEntry| {
            entry.binder_depth == binder_depth && entry.ordinary_count == ordinary_count
        };
        let outward = |entry: &&ContextEntry| {
            entry
                .binder_depth
                .checked_sub(binder_depth)
                .is_some_and(|removed| {
                    usize::try_from(removed).ok()
                        == entry.ordinary_count.checked_sub(ordinary_count)
                })
        };
        let primary = self.primary.get(&address);
        if let Some(entry) = primary.filter(exact) {
            return Some(entry);
        }
        let spare = self.spare.get(&address);
        if let Some(entry) = spare.filter(exact) {
            return Some(entry);
        }
        primary.filter(outward).or_else(|| spare.filter(outward))
    }

    /// Called only after `get` returns None; never after a selected probe fails.
    /// These screens select at most one slot, not a dependency certificate.
    pub(super) fn named_only(
        &self,
        address: usize,
        binder_depth: u32,
        input: &Expr,
    ) -> Option<(&ContextEntry, TermScopeCacheRoute)> {
        if input.has_loose_bvars_quick() {
            return None;
        }
        let outward = |entry: &&ContextEntry| {
            entry.entry.declarations().is_none() && entry.binder_depth >= binder_depth
        };
        let inward = |entry: &&ContextEntry| {
            entry.entry.declarations().is_none() && entry.binder_depth < binder_depth
        };
        // Preserve the old primary/spare outward priority. Only an absent
        // outward projection may select one inward slot; a failed probe never
        // retries another candidate. The charged dependency walk, not this
        // shape screen, establishes identical relative named indices.
        let primary = self.primary.get(&address);
        let spare = self.spare.get(&address);
        primary
            .filter(outward)
            .map(|entry| (entry, TermScopeCacheRoute::PrimaryNamedOnly))
            .or_else(|| {
                spare
                    .filter(outward)
                    .map(|entry| (entry, TermScopeCacheRoute::SpareNamedOnly))
            })
            .or_else(|| {
                primary
                    .filter(inward)
                    .map(|entry| (entry, TermScopeCacheRoute::PrimaryNamedOnly))
                    .or_else(|| {
                        spare
                            .filter(inward)
                            .map(|entry| (entry, TermScopeCacheRoute::SpareNamedOnly))
                    })
            })
    }

    pub(super) fn insert(&mut self, address: usize, incoming: ContextEntry) {
        let projection = (incoming.binder_depth, incoming.ordinary_count);
        if let Some(previous) = self.primary.insert(address, incoming)
            && (previous.binder_depth, previous.ordinary_count) != projection
        {
            // A successful spare hit promotes it; a third projection
            // evicts the previous spare. Rebuilding the same projection
            // leaves the distinct spare intact, even after a failed probe.
            self.spare.insert(address, previous);
        }
    }

    /// Observe the unchanged selection and the other slot's shape only.
    /// This never reads dependencies, validates, promotes or probes a candidate.
    pub(super) fn observation(
        &self,
        address: usize,
        binder_depth: u32,
        ordinary_count: usize,
    ) -> CandidateShape {
        let primary = self.primary.get(&address);
        let spare = self.spare.get(&address);
        let selected = self.get(address, binder_depth, ordinary_count);
        let eligible = |entry: &&ContextEntry| {
            entry
                .binder_depth
                .checked_sub(binder_depth)
                .is_some_and(|removed| {
                    usize::try_from(removed).ok()
                        == entry.ordinary_count.checked_sub(ordinary_count)
                })
        };
        let is_primary =
            selected.is_some_and(|chosen| primary.is_some_and(|entry| std::ptr::eq(entry, chosen)));
        let route = selected.map(|entry| {
            match (
                is_primary,
                entry.binder_depth == binder_depth && entry.ordinary_count == ordinary_count,
            ) {
                (true, true) => TermScopeCacheRoute::PrimaryExact,
                (false, true) => TermScopeCacheRoute::SpareExact,
                (true, false) => TermScopeCacheRoute::PrimaryOutward,
                (false, false) => TermScopeCacheRoute::SpareOutward,
            }
        });
        CandidateShape {
            route,
            retained: primary.is_some() || spare.is_some(),
            alternate: selected.is_some()
                && if is_primary {
                    spare.filter(eligible).is_some()
                } else {
                    primary.filter(eligible).is_some()
                },
            binder_depth: selected.map(|entry| entry.binder_depth),
            ordinary_count: selected.map(|entry| entry.ordinary_count),
            declaration_free_depths: [primary, spare].map(|entry| {
                entry
                    .filter(|entry| entry.entry.declarations.is_none())
                    .map(|entry| entry.binder_depth)
            }),
        }
    }

    #[cfg(test)]
    pub(super) fn maps(&self) -> (&HashMap<usize, ContextEntry>, &HashMap<usize, ContextEntry>) {
        (&self.primary, &self.spare)
    }
}

impl<'a> Closer<'a> {
    pub(super) fn same_cached_dependencies(&mut self, cached: &ContextEntry) -> bool {
        if cached.context == self.context {
            return true;
        }
        let dependencies = cached.entry.dependencies();
        if dependencies.is_none() || !self.same_forest_lexical_context(cached.context) {
            return self.same_dependencies(dependencies);
        }
        // A complete lexical prefix fixes every outside named read and
        // ordinary coordinate. The forest only adds explicit externals
        // between roots; they stay FVars and never occupy binder depth.
        // This proves dependency equality only. The caller still checks the
        // declaration footprint against the newly visible externals.
        self.observe_phase(TermScopeStopPhase::ExactDependency);
        let accepted = self.visit();
        if accepted {
            self.stats.context_check_visits += 1;
        } else if self.error == Some(TermScopeError::VisitLimit) {
            self.observe_dependency_rejection(DependencyRejection::Budget);
        }
        self.observe_probe_result(true, accepted, usize::from(accepted), 0);
        accepted
    }

    pub(super) fn same_dependencies(&mut self, dependencies: Option<usize>) -> bool {
        self.observe_phase(TermScopeStopPhase::ExactDependency);
        let before = self.stats.context_check_visits;
        let result = self.same_dependencies_inner(dependencies);
        if !result && self.error == Some(TermScopeError::VisitLimit) {
            self.observe_dependency_rejection(DependencyRejection::Budget);
        }
        self.observe_probe_result(true, result, self.stats.context_check_visits - before, 0);
        result
    }

    fn same_dependencies_inner(&mut self, dependencies: Option<usize>) -> bool {
        let Some(root) = dependencies else {
            return true;
        };
        if self.known_named_prefix(root, self.binder_depth) {
            if !self.visit() {
                return false;
            }
            self.stats.context_check_visits += 1;
            self.observe_named_prefix_proof();
            return true;
        }
        self.probe_stack.clear();
        let stamp = self.stats.visits;
        if !matches!(self.dependencies[root].dependency, Dependency::Join(_, _)) {
            // A single leaf needs no traversal stack. Preserve the charge
            // before both the previous-probe and internal-read cutoffs.
            if !self.visit() {
                return false;
            }
            self.stats.context_check_visits += 1;
            let entry = &mut self.dependencies[root];
            if entry.last_probe == stamp || entry.min_depth >= self.binder_depth {
                return true;
            }
            entry.last_probe = stamp;
            let dependency = entry.dependency;
            return self.same_external_dependency(dependency);
        }
        self.probe_stack.push(root);
        while let Some(index) = self.probe_stack.pop() {
            if !self.visit() {
                return false;
            }
            self.stats.context_check_visits += 1;
            let entry = &mut self.dependencies[index];
            if entry.last_probe == stamp || entry.min_depth >= self.binder_depth {
                continue;
            }
            entry.last_probe = stamp;
            match entry.dependency {
                Dependency::Join(left, right) => {
                    // A mixed root can contain a subtree whose named reads
                    // share a proven lexical prefix. Its request is charged,
                    // and the remaining branches still check their own reads.
                    if self.known_named_prefix(index, self.binder_depth) {
                        self.observe_named_prefix_proof();
                    } else {
                        self.probe_stack.push(right);
                        self.probe_stack.push(left);
                    }
                }
                dependency => {
                    if !self.same_external_dependency(dependency) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Both exact paths validate already charged, non-internal leaves here.
    fn same_external_dependency(&mut self, dependency: Dependency) -> bool {
        let reason = match dependency {
            Dependency::Named(id, depth) => {
                let actual = self.active.get(&id);
                if actual == Some(&depth) {
                    return true;
                }
                if actual.is_none() {
                    DependencyRejection::NamedMissing
                } else {
                    DependencyRejection::NamedMoved
                }
            }
            Dependency::Ordinary(position, depth) => {
                let actual = self.ordinary.get(position);
                if actual == Some(&depth) {
                    return true;
                }
                if actual.is_none() {
                    DependencyRejection::OrdinaryMissing
                } else {
                    DependencyRejection::OrdinaryMoved
                }
            }
            Dependency::Join(_, _) => unreachable!("the caller selected an exact dependency leaf"),
        };
        self.observe_dependency_rejection(reason);
        false
    }

    /// The ordinary mode retains equal removed depth/count and exact external
    /// ordinary reads. Named-only mode additionally requires the original-input
    /// no-loose screen and no deferred declarations at selection, fully checks
    /// external Named reads, and refuses external Ordinary reads. Named-only
    /// projections may move inward as well: every external depth must increase
    /// by exactly the added parent depth. Internal reads are still pruned at
    /// cached depth. For local nesting r, oldD+r-d-1 == newD+r-new_d-1 keeps
    /// the output Arc unchanged in either direction.
    /// An exact completed-footprint minimum can reject either mode without a
    /// probe, deliberately changing a finite-budget prefix or refusal reason.
    /// Neither mode licenses proof admission; every performed probe is charged.
    pub(super) fn relative_dependencies(
        &mut self,
        cached: &ContextEntry,
        mode: RebaseMode,
    ) -> Option<Option<usize>> {
        self.observe_phase(TermScopeStopPhase::RelativeDependency);
        let before = self.stats.context_check_visits;
        let nodes = self.dependencies.len();
        let result = self.relative_dependencies_inner(cached, mode);
        if result.is_none() && self.error == Some(TermScopeError::VisitLimit) {
            self.observe_dependency_rejection(DependencyRejection::Budget);
        }
        self.observe_probe_result(
            true,
            result.is_some(),
            self.stats.context_check_visits - before,
            self.dependencies.len() - nodes,
        );
        result
    }

    fn relative_dependencies_inner(
        &mut self,
        cached: &ContextEntry,
        mode: RebaseMode,
    ) -> Option<Option<usize>> {
        let (removed, added) = match cached.binder_depth.checked_sub(self.binder_depth) {
            Some(removed) => (removed, 0),
            None if matches!(mode, RebaseMode::NamedOnly) => {
                (0, self.binder_depth.checked_sub(cached.binder_depth)?)
            }
            None => {
                self.observe_dependency_rejection(DependencyRejection::Shape);
                return None;
            }
        };
        let ordinary_removed = match mode {
            RebaseMode::Ordinary => {
                let count = cached
                    .ordinary_count
                    .checked_sub(self.ordinary.len())
                    .or_else(|| {
                        self.observe_dependency_rejection(DependencyRejection::Shape);
                        None
                    })?;
                if usize::try_from(removed).ok()? != count {
                    self.observe_dependency_rejection(DependencyRejection::Shape);
                    return None;
                }
                Some(count)
            }
            // Absence of deferred named declarations is load-bearing: input
            // metadata otherwise mistakes their binders for ordinary ones.
            RebaseMode::NamedOnly if cached.entry.declarations().is_none() => None,
            RebaseMode::NamedOnly => {
                self.observe_dependency_rejection(DependencyRejection::Shape);
                return None;
            }
        };
        let Some(root) = cached.entry.dependencies() else {
            return Some(None);
        };
        if self.dependencies[root].min_depth < removed {
            // This exact completed-footprint minimum reaches an external leaf:
            // removed <= cached depth, so the old internal-read cutoff cannot
            // hide its underflow.
            // Reject only the selected slot, before allocating or probing it.
            self.observe_dependency_rejection(match mode {
                RebaseMode::Ordinary => DependencyRejection::OrdinaryDepthScreen,
                RebaseMode::NamedOnly => DependencyRejection::NamedOnlyDepthScreen,
            });
            return None;
        }
        if matches!(mode, RebaseMode::NamedOnly)
            && self.known_named_prefix(root, cached.binder_depth)
        {
            if !self.visit() {
                return None;
            }
            self.stats.context_check_visits += 1;
            self.observe_named_prefix_proof();
            if removed == 0 && added == 0 {
                return Some(Some(root));
            }
            // The exact names retain their absolute depths. A nonzero parent
            // delta therefore cannot preserve their relative output indices.
            self.observe_dependency_rejection(DependencyRejection::NamedMoved);
            return None;
        }
        if !matches!(self.dependencies[root].dependency, Dependency::Join(_, _)) {
            // A single leaf needs neither a postorder stack nor a rebase map.
            // Its request, internal cutoff and exact checks remain identical
            // to a leaf reached by the charged Join walk below.
            if !self.visit() {
                return None;
            }
            self.stats.context_check_visits += 1;
            if self.dependencies[root].min_depth >= cached.binder_depth {
                return Some(None);
            }
            return self
                .rebase_external_leaf(root, removed, added, ordinary_removed, mode)
                .map(Some);
        }
        // No additional field/storage for callers that never move a context.
        // Each temporary memo entry and new arena node requires a charged
        // probe below; duplicate DAG edges are charged but do not expand it.
        let mut rebased = HashMap::new();
        let mut stack = vec![(root, false)];
        while let Some((index, finish)) = stack.pop() {
            if finish {
                let Dependency::Join(old_left, old_right) = self.dependencies[index].dependency
                else {
                    unreachable!("only dependency joins need postorder completion")
                };
                let output = match (rebased[&old_left], rebased[&old_right]) {
                    (Some(left), Some(right)) if left != right => {
                        if matches!(mode, RebaseMode::NamedOnly)
                            && left == old_left
                            && right == old_right
                        {
                            Some(index)
                        } else {
                            Some(self.union_dependencies(left, right))
                        }
                    }
                    (left, right) => left.or(right),
                };
                rebased.insert(index, output);
                continue;
            }
            if !self.visit() {
                return None;
            }
            self.stats.context_check_visits += 1;
            if rebased.contains_key(&index) {
                continue;
            }
            if self.dependencies[index].min_depth >= cached.binder_depth {
                // This read is bound inside the unchanged subtree, hence never
                // an external dependency of either its old or new parent.
                rebased.insert(index, None);
                continue;
            }
            let output = match self.dependencies[index].dependency {
                Dependency::Join(left, right) => {
                    stack.push((index, true));
                    stack.push((right, false));
                    stack.push((left, false));
                    continue;
                }
                _ => Some(self.rebase_external_leaf(
                    index,
                    removed,
                    added,
                    ordinary_removed,
                    mode,
                )?),
            };
            rebased.insert(index, output);
        }
        Some(rebased[&root])
    }

    /// Exact checks for one already charged, non-internal dependency leaf.
    /// Both the single-root path and Join walker use this same rebase rule.
    fn rebase_external_leaf(
        &mut self,
        index: usize,
        removed: u32,
        added: u32,
        ordinary_removed: Option<usize>,
        mode: RebaseMode,
    ) -> Option<usize> {
        match self.dependencies[index].dependency {
            Dependency::Named(id, depth) => {
                let depth = depth
                    .checked_sub(removed)
                    .and_then(|depth| depth.checked_add(added))
                    .or_else(|| {
                        self.observe_dependency_rejection(if added == 0 {
                            DependencyRejection::Underflow
                        } else {
                            DependencyRejection::Shape
                        });
                        None
                    })?;
                let actual = self.active.get(&id);
                if actual != Some(&depth) {
                    let reason = if actual.is_none() {
                        DependencyRejection::NamedMissing
                    } else {
                        DependencyRejection::NamedMoved
                    };
                    self.observe_dependency_rejection(reason);
                    return None;
                }
                if matches!(mode, RebaseMode::NamedOnly) && removed == 0 && added == 0 {
                    Some(index)
                } else {
                    Some(self.named_read_dependency(id, depth))
                }
            }
            Dependency::Ordinary(position, depth) => {
                let Some(ordinary_removed) = ordinary_removed else {
                    self.observe_dependency_rejection(DependencyRejection::UnexpectedOrdinary);
                    return None;
                };
                let position = position.checked_sub(ordinary_removed).or_else(|| {
                    self.observe_dependency_rejection(DependencyRejection::Underflow);
                    None
                })?;
                let depth = depth.checked_sub(removed).or_else(|| {
                    self.observe_dependency_rejection(DependencyRejection::Underflow);
                    None
                })?;
                let actual = self.ordinary.get(position);
                if actual != Some(&depth) {
                    let reason = if actual.is_none() {
                        DependencyRejection::OrdinaryMissing
                    } else {
                        DependencyRejection::OrdinaryMoved
                    };
                    self.observe_dependency_rejection(reason);
                    return None;
                }
                Some(self.dependency_node(Dependency::Ordinary(position, depth)))
            }
            Dependency::Join(_, _) => unreachable!("the caller selected a dependency leaf"),
        }
    }

    pub(super) fn reusable(&mut self, declarations: Option<usize>) -> bool {
        self.observe_phase(TermScopeStopPhase::Declaration);
        let before = self.stats.scope_check_visits;
        let result = self.reusable_inner(declarations);
        self.observe_probe_result(false, result, self.stats.scope_check_visits - before, 0);
        result
    }

    fn reusable_inner(&mut self, declarations: Option<usize>) -> bool {
        let Some(root) = declarations else {
            return true;
        };
        if self.active.is_empty() {
            return true;
        }
        let active_envelope = self.active_envelope;
        self.probe_stack.clear();
        self.probe_stack.push(root);
        // The enclosing expression request has already consumed a visit, so
        // this stamp is nonzero and distinct from every previous probe's stamp.
        let stamp = self.stats.visits;
        while let Some(index) = self.probe_stack.pop() {
            if !self.visit() {
                return false;
            }
            self.stats.scope_check_visits += 1;
            let entry = &mut self.footprints[index];
            if entry.last_probe == stamp {
                continue;
            }
            entry.last_probe = stamp;
            if active_envelope.is_some_and(|active| entry.envelope.is_disjoint(active)) {
                // Every declaration lies in this envelope. Disjointness is a
                // sufficient proof of no collision, not a heuristic verdict.
                // The request above is still charged before skipping children.
                continue;
            }
            match entry.declarations {
                Declarations::Local(id) => {
                    if self.active.contains_key(&id) {
                        self.observe_declaration_collision();
                        // Rewalk normally: preserve which scope error is seen
                        // first, including errors in types and let values.
                        return false;
                    }
                }
                Declarations::Join(left, right) => {
                    self.probe_stack.push(right);
                    self.probe_stack.push(left);
                }
            }
        }
        true
    }

    // The single production initializer is also used by internal storage and
    // partial-probe controls; there is no parallel test closer or cache.
    pub(super) fn new(scope: &'a TermScope, limits: TermScopeLimits, diagnose: bool) -> Self {
        Self {
            scope,
            full: None,
            ordinary_reuse: None,
            external: HashSet::new(),
            borrowed_external: None,
            strict_external: false,
            limits,
            stats: TermScopeStats::default(),
            error: None,
            memo: HashMap::new(),
            closed: HashSet::new(),
            named_closed: HashMap::new(),
            contextual: ContextCandidates::default(),
            shifted_outputs: HashMap::new(),
            named_outputs: HashMap::new(),
            shift_origins: HashMap::new(),
            output_nodes: output_nodes::OutputNodes::default(),
            dependencies: Vec::new(),
            dependency_nodes: HashMap::new(),
            dependency: None,
            footprints: Vec::new(),
            footprint: None,
            probe_stack: Vec::new(),
            contexts: HashMap::new(),
            context: 0,
            lexical_contexts: Vec::new(),
            context_stack: Vec::new(),
            active: NamedReads::default(),
            active_envelope: None,
            ordinary: Vec::new(),
            binder_depth: 0,
            walk_depth: 0,
            observations: diagnose.then(Box::default),
        }
    }
}
