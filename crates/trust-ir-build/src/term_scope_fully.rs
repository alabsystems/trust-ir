// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Complete materialization for an immediately following bounded substitution.
//! Canonical complete walks, with optional exact unchanged-ordinary reuse
//! under an ancestral owned external prefix. Heights are complete, never the
//! saturated approximate depth, and any deferred named binder excludes reuse.
use super::*;
use std::hash::{Hash, Hasher};

#[derive(Clone)]
struct Graph(Expr);
impl PartialEq for Graph {
    fn eq(&self, other: &Self) -> bool {
        crate::proof_assembly::normalize::same_graph(&self.0, &other.0)
    }
}
impl Eq for Graph {}
impl Hash for Graph {
    fn hash<H: Hasher>(&self, hash: &mut H) {
        crate::proof_assembly::normalize::hash_graph(&self.0, hash);
    }
}
#[derive(Clone, Copy)]
struct Ordinary {
    height: u32,
    // Highest actually read dynamic inventory position; initial facts use 0.
    prefix: usize,
    generation: u64,
    fvars: Option<IdEnvelope>,
}
#[derive(Clone, Copy)]
pub(crate) struct CompleteFVarEnvelope(Option<IdEnvelope>);
impl CompleteFVarEnvelope {
    pub(crate) fn may_contain(&self, id: FVarId) -> bool {
        self.0
            .is_some_and(|range| range.min <= id && id <= range.max)
    }
}
pub(crate) struct FullScopeCache {
    entries: HashMap<Graph, Ordinary>,
    bound: usize,
    failed: bool,
}
impl FullScopeCache {
    pub(crate) fn new(bound: usize) -> Self {
        Self {
            entries: HashMap::new(),
            bound,
            failed: false,
        }
    }
    pub(crate) fn poison(&mut self) {
        self.failed = true;
    }
    pub(crate) fn has_failed(&self) -> bool {
        self.failed
    }
    pub(crate) fn envelope(
        &self,
        expression: &Expr,
        generations: &[u64],
    ) -> Option<CompleteFVarEnvelope> {
        if self.failed {
            return None;
        }
        let known = self.entries.get(&Graph(expression.clone()))?;
        (generations.get(known.prefix) == Some(&known.generation))
            .then_some(CompleteFVarEnvelope(known.fvars))
    }
}
pub(crate) struct FullScopeReuse<'a> {
    pub(crate) cache: &'a mut FullScopeCache,
    pub(crate) generations: &'a [u64],
    pub(crate) positions: &'a HashMap<FVarId, usize>,
    pub(crate) initial_len: usize,
}

#[derive(Clone)]
struct Completed {
    replacement: Option<Arc<Expr>>,
    height: u32,
    deferred: bool,
    fvars: Option<IdEnvelope>,
    prefix: usize,
}

#[derive(Default)]
pub(super) struct FullTraversal {
    memo: HashMap<(usize, usize), Completed>,
    pub(super) height: u32,
    pub(super) deferred: bool,
    pub(super) prefix: usize,
    fvars: Option<IdEnvelope>,
}
impl FullTraversal {
    pub(super) fn include_fvars(&mut self, incoming: Option<IdEnvelope>) {
        self.fvars = match (self.fvars, incoming) {
            (Some(old), Some(new)) => Some(old.union(new)),
            (old, new) => old.or(new),
        };
    }
}

impl Closer<'_> {
    pub(super) fn fold_shared_fully(&mut self, expression: &Expr) -> Option<Arc<Expr>> {
        if self.error.is_some() || !self.visit() {
            return None;
        }
        if self.walk_depth >= self.limits.max_depth {
            self.fail(TermScopeError::DepthLimit);
            return None;
        }
        let candidate = self.ordinary_reuse.is_some()
            && !expression.has_loose_bvars()
            && matches!(
                expression.kind(),
                ExprKind::App(..) | ExprKind::Lam(..) | ExprKind::Pi(..) | ExprKind::Let(..)
            );
        let graph = if candidate {
            // Pay the graph probe/pin before consulting persistent state.
            if !self.visit() {
                return None;
            }
            let graph = Graph(expression.clone());
            let reuse = self.ordinary_reuse.as_ref().unwrap();
            if reuse.cache.failed {
                self.fail(TermScopeError::VisitLimit);
                return None;
            }
            if let Some(known) = reuse.cache.entries.get(&graph).copied()
                && reuse.generations.get(known.prefix) == Some(&known.generation)
            {
                if self
                    .walk_depth
                    .checked_add(known.height)
                    .is_none_or(|height| height > self.limits.max_depth)
                {
                    self.fail(TermScopeError::DepthLimit);
                    return None;
                }
                if let Some(full) = self.full.as_mut() {
                    full.height = full.height.max(known.height);
                    full.include_fvars(known.fvars);
                    // A reused child contributes its admitted external facts
                    // just as a fresh FVar visit does.
                    full.prefix = full.prefix.max(known.prefix);
                }
                self.stats.memo_hits += 1;
                return None;
            }
            Some(graph)
        } else {
            None
        };
        let key = (expression as *const Expr as usize, self.context);
        let cached = self
            .full
            .as_ref()
            .and_then(|full| full.memo.get(&key))
            .cloned();
        if let Some(cached) = cached {
            if self
                .walk_depth
                .checked_add(cached.height)
                .is_none_or(|depth| depth > self.limits.max_depth)
            {
                self.fail(TermScopeError::DepthLimit);
                return None;
            }
            if let Some(full) = self.full.as_mut() {
                full.height = full.height.max(cached.height);
                full.deferred |= cached.deferred;
                full.include_fvars(cached.fvars);
                full.prefix = full.prefix.max(cached.prefix);
            }
            self.stats.memo_hits += 1;
            return cached.replacement;
        }
        let Some(full) = self.full.as_mut() else {
            self.fail(TermScopeError::DepthLimit);
            return None;
        };
        let enclosing = std::mem::take(&mut full.height);
        let enclosing_deferred = std::mem::take(&mut full.deferred);
        let enclosing_fvars = full.fvars.take();
        let enclosing_prefix = std::mem::take(&mut full.prefix);
        let own_deferred = self.scope.component_binder_id(expression).is_some();
        let enclosing_footprint = self.footprint.take();
        let enclosing_dependency = self.dependency.take();
        self.walk_depth += 1;
        // Reuse the canonical named/ordinary binder and FVar translation.
        // Its child hooks return here, rather than the projection caches.
        let replacement = StackBoundary(self).fold_expr_opt(expression).map(Arc::new);
        self.walk_depth -= 1;
        // Exact-context entries need no scope-projection summaries. Keep
        // transient child summaries from accumulating across the forest.
        self.footprint = enclosing_footprint;
        self.dependency = enclosing_dependency;
        let Some(height) = self
            .full
            .as_ref()
            .and_then(|full| full.height.checked_add(1))
        else {
            self.fail(TermScopeError::DepthLimit);
            return None;
        };
        let deferred = own_deferred || self.full.as_ref().is_some_and(|full| full.deferred);
        let fvars = self.full.as_ref().and_then(|full| full.fvars);
        let prefix = self.full.as_ref().map_or(0, |full| full.prefix);
        if let Some(full) = self.full.as_mut() {
            full.height = enclosing.max(height);
            full.deferred = enclosing_deferred || deferred;
            full.fvars = enclosing_fvars;
            full.include_fvars(fvars);
            full.prefix = enclosing_prefix.max(prefix);
        }
        if self.error.is_some() {
            return replacement;
        }
        let replacement = replacement.map(|node| self.intern_output_node(node));
        if let Some(graph) = graph
            && replacement.is_none()
            && !deferred
            && height >= 8
            && self
                .ordinary_reuse
                .as_ref()
                .is_some_and(|reuse| reuse.cache.entries.len() < reuse.cache.bound)
        {
            // Prepay retained graph-key storage and map publication. Only the
            // unchanged, ordinary-closed, fully named-free input qualifies.
            if !self.visit() || !self.visit() {
                return None;
            }
            let Some(generation) = self
                .ordinary_reuse
                .as_ref()
                .and_then(|reuse| reuse.generations.get(prefix))
                .copied()
            else {
                self.fail(TermScopeError::VisitLimit);
                return None;
            };
            let reuse = self.ordinary_reuse.as_mut().unwrap();
            reuse.cache.entries.insert(
                graph,
                Ordinary {
                    height,
                    prefix,
                    generation,
                    fvars,
                },
            );
        }
        self.stats.transformed_nodes += 1;
        if let Some(full) = self.full.as_mut() {
            full.memo.insert(
                key,
                Completed {
                    replacement: replacement.clone(),
                    height,
                    deferred,
                    fvars,
                    prefix,
                },
            );
        }
        replacement
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::BinderInfo;

    #[test]
    fn full_materialization_matches_ordinary_closing_across_actual_contexts() {
        let mut scope = TermScope::new();
        let named = FVarId::new(1);
        let global = FVarId::new(9);
        let n = Expr::const_str("Nat");
        let shared = Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0));
        let roots = [
            shared.clone(),
            scope.lam(named, BinderInfo::Default, n.clone(), shared),
            scope.lam(named, BinderInfo::Default, n.clone(), Expr::fvar(named)),
            scope.pi(named, BinderInfo::Default, n.clone(), Expr::fvar(global)),
            scope.lam(named, BinderInfo::Default, n.clone(), Expr::nat_lit(3)),
        ];
        let (ordinary, _) =
            scope.close_external_forest(&roots, &[global], &[1; 5], TermScopeLimits::default());
        let (complete, stats) = scope.close_external_forest_fully(
            &roots,
            &[global],
            &[1; 5],
            TermScopeLimits::default(),
        );
        let complete = complete.unwrap();
        assert_eq!(complete, ordinary.unwrap());
        assert_eq!(stats.completed_roots, 5);
        assert_eq!(
            complete[1],
            Expr::lam(
                BinderInfo::Default,
                n,
                Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(1)),
            )
        );
        for root in &complete[1..] {
            assert!(scope.component_binder_id(root).is_none());
        }
    }

    #[test]
    fn full_materialization_keeps_forward_visibility_and_shadow_refusals() {
        let mut scope = TermScope::new();
        let global = FVarId::new(4);
        let roots = [Expr::fvar(global), Expr::fvar(global)];
        let (result, stats) = scope.close_external_forest_fully(
            &roots,
            &[global],
            &[0, 1],
            TermScopeLimits::default(),
        );
        assert_eq!(result.unwrap_err(), TermScopeError::OutOfScope(global));
        assert_eq!(stats.completed_roots, 0);
        assert!(stats.visits > 0);
        let shadow = scope.lam(
            global,
            BinderInfo::Default,
            Expr::const_str("Nat"),
            Expr::nat_lit(0),
        );
        let (result, _) = scope.close_external_forest_fully(
            &[shadow],
            &[global],
            &[1],
            TermScopeLimits::default(),
        );
        assert_eq!(result.unwrap_err(), TermScopeError::ShadowedLocal(global));
    }

    #[test]
    fn full_materialization_checks_saturated_depth_and_deeper_memo_hits() {
        let scope = TermScope::new();
        let mut shared = Expr::nat_lit(0);
        for _ in 0..300 {
            shared = Expr::app(Expr::const_str("Nat.succ"), shared);
        }
        let limits = TermScopeLimits {
            max_visits: 10_000,
            max_depth: 301,
        };
        let (admitted, _) = scope.close_external_forest_fully(&[shared.clone()], &[], &[0], limits);
        assert_eq!(admitted.unwrap(), vec![shared.clone()]);
        let deeper = Expr::app(Expr::const_str("Nat.succ"), shared.clone());
        let (refused, stats) =
            scope.close_external_forest_fully(&[shared, deeper], &[], &[0, 0], limits);
        assert_eq!(refused.unwrap_err(), TermScopeError::DepthLimit);
        assert_eq!(stats.completed_roots, 1);
        assert!(stats.memo_hits > 0);
        let (refused, stats) = scope.close_external_forest_fully(
            &[Expr::app(Expr::const_str("Nat.succ"), Expr::nat_lit(0))],
            &[],
            &[0],
            TermScopeLimits {
                max_visits: 1,
                max_depth: 10,
            },
        );
        assert_eq!(refused.unwrap_err(), TermScopeError::VisitLimit);
        assert_eq!(stats.visits, 1);
    }

    #[test]
    fn full_materialization_hit_cannot_hide_a_newly_external_binder() {
        let mut scope = TermScope::new();
        let a = FVarId::new(11);
        let b = FVarId::new(12);
        let body = Expr::apps(Expr::const_str("Nat.add"), [Expr::fvar(a), Expr::fvar(b)]);
        let named = scope.lam(b, BinderInfo::Default, Expr::const_str("Nat"), body);
        // Cloning the outer root retains the SAME named-child Arc. A cache
        // keyed only on the child address would hide the later shadowing.
        let shared = Expr::app(Expr::const_str("consume"), named);
        let (result, stats) = scope.close_external_forest_fully(
            &[shared.clone(), shared],
            &[a, b],
            &[1, 2],
            TermScopeLimits::default(),
        );
        assert_eq!(result.unwrap_err(), TermScopeError::ShadowedLocal(b));
        assert_eq!(stats.completed_roots, 1);
        assert!(stats.visits > 0);
    }
}
