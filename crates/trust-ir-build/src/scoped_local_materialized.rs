// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Bounded candidate abstraction over already-materialized ordinary terms.
//! This is not proof authority. Deferred named binders are refused, never erased.
use super::{LocalScope, LocalScopeOwner, ScopedLocal};
use clean_kernel::{
    BinderInfo, Expr,
    expr::{ExprFolderOpt, FVarId},
};
use std::{
    collections::{HashMap, HashSet},
    hash::{Hash, Hasher},
    rc::Rc,
};

#[derive(Clone)]
struct Key(Expr, u32, bool);
impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
            && self.2 == other.2
            && crate::proof_assembly::normalize::same_graph(&self.0, &other.0)
    }
}
impl Eq for Key {}
impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        crate::proof_assembly::normalize::hash_graph(&self.0, state);
        self.1.hash(state);
        self.2.hash(state);
    }
}
// A successful entry carries a conservative support inventory. Missing entries
// are unknown and must be walked. TermScope only registers fresh body Arcs, so
// existing ordinary nodes cannot acquire deferred metadata after validation.
#[derive(Clone)]
struct Cached {
    allowed: Rc<HashSet<FVarId>>,
    target: Option<FVarId>,
    allow_target: bool,
    traversal: Traversal,
}
#[derive(Clone)]
struct Traversal {
    result: Option<Expr>,
    // Number of nodes on the longest traversed path, including this node.
    // Reuse must respect the current structural nesting limit, too.
    height: u32,
}
#[derive(Default)]
pub(crate) struct MaterializedCache {
    owner: Option<LocalScopeOwner>,
    entries: HashMap<Key, Cached>,
    // A zero-depth key is only an index here, not evidence of closure. Entries
    // require a successful unchanged walk AND no incoming ordinary BVars.
    // Their conservative FVar inventory is still checked on every reuse.
    unchanged: HashMap<Key, Cached>,
}
// Pin the actual inventory allocation, not a reusable raw pointer. Each key
// owns an Rc so a later inventory cannot acquire an old memo identity by ABA.
#[derive(Clone)]
struct InventoryKey(Rc<HashSet<FVarId>>);
impl PartialEq for InventoryKey {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for InventoryKey {}
impl Hash for InventoryKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (Rc::as_ptr(&self.0) as usize).hash(state);
    }
}
enum InventoryPermissions<'a> {
    Fresh(HashMap<InventoryKey, bool>),
    Reused(&'a mut HashMap<InventoryKey, bool>),
}
impl InventoryPermissions<'_> {
    fn reused(&self) -> bool {
        matches!(self, Self::Reused(_))
    }
    fn get(&self, key: &InventoryKey) -> Option<bool> {
        match self {
            Self::Fresh(entries) => entries.get(key).copied(),
            Self::Reused(entries) => entries.get(key).copied(),
        }
    }
    fn insert(&mut self, key: InventoryKey, value: bool) {
        match self {
            Self::Fresh(entries) => {
                entries.insert(key, value);
            }
            Self::Reused(entries) => {
                entries.insert(key, value);
            }
        }
    }
}

/// Authenticated immutable inventory for validation in ONE replacement pass.
/// This is candidate-scope metadata, not normalization or proof authority.
/// Borrow the actual inventory so it cannot change or outlive that pass.
pub(crate) struct MaterializedValidationContext<'a> {
    scope: &'a LocalScope,
    _external: &'a [ScopedLocal],
    allowed: Rc<HashSet<FVarId>>,
    setup_visits: usize,
    inventories: HashMap<InventoryKey, bool>,
}
impl<'a> MaterializedValidationContext<'a> {
    pub(crate) fn new(
        scope: &'a LocalScope,
        external: &'a [ScopedLocal],
        work: &mut usize,
        limit: usize,
        cache: &mut MaterializedCache,
    ) -> Result<Self, String> {
        check_owner(scope, cache)?;
        let (allowed, setup_visits) = authenticate_inventory(scope, external, work, limit)?;
        Ok(Self {
            scope,
            _external: external,
            allowed,
            setup_visits,
            inventories: HashMap::new(),
        })
    }
}

struct Walk<'a> {
    scope: &'a LocalScope,
    allowed: Rc<HashSet<FVarId>>,
    target: Option<FVarId>,
    allow_target: bool,
    depth: u32,
    nesting: u32,
    height: u32,
    visits: usize,
    work: &'a mut usize,
    limit: usize,
    memo: HashMap<Key, Traversal>,
    error: Option<String>,
    cache: &'a mut MaterializedCache,
    inventories: InventoryPermissions<'a>,
}
struct Stack<'a, 'b>(&'a mut Walk<'b>);
impl ExprFolderOpt for Stack<'_, '_> {
    fn fold_expr_opt_inner(&mut self, expr: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(expr)
    }
}
impl Walk<'_> {
    fn charge(&mut self) -> bool {
        if *self.work >= self.limit {
            self.error = Some("projected case-context aggregate abstraction limit".into());
            return false;
        }
        if self.visits >= self.scope.closing_limits().max_visits {
            self.error = Some("materialized candidate owner visit limit".into());
            return false;
        }
        *self.work += 1;
        self.visits += 1;
        true
    }
    fn permits(&mut self, old: &Rc<HashSet<FVarId>>) -> bool {
        if self.inventories.reused() {
            // This probe is real work even when both inventories are identical.
            if !self.charge() {
                return false;
            }
            if Rc::ptr_eq(old, &self.allowed) {
                return true;
            }
        }
        let key = InventoryKey(old.clone());
        if let Some(ok) = self.inventories.get(&key) {
            return ok;
        }
        let mut ok = true;
        for id in old.iter() {
            if !self.charge() {
                return false;
            }
            if !self.allowed.contains(id) {
                ok = false;
                break;
            }
        }
        self.inventories.insert(key, ok);
        ok
    }
    fn reuse(&mut self, traversal: &Traversal) -> bool {
        if self
            .nesting
            .checked_add(traversal.height)
            .is_none_or(|end| end > self.scope.closing_limits().max_depth)
        {
            self.error = Some("materialized candidate traversal depth limit".into());
            return false;
        }
        self.height = self.height.max(traversal.height);
        true
    }
}
impl ExprFolderOpt for Walk<'_> {
    fn fold_bvar_opt(&mut self, index: u32) -> Option<Expr> {
        if index >= self.depth {
            self.error = Some("materialized candidate has loose bound variable".into());
        }
        None
    }
    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        if self.target == Some(id) {
            if self.allow_target {
                return Some(Expr::bvar(self.depth));
            }
            self.error = Some("materialized binder has self-dependent type".into());
        } else if !self.allowed.contains(&id) {
            self.error = Some("materialized candidate has unauthorized free variable".into());
        }
        None
    }
    fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
        let Some(depth) = self.depth.checked_add(1) else {
            self.error = Some("materialized binder depth overflow".into());
            return None;
        };
        self.depth = depth;
        let out = self.fold_expr_opt(expr);
        self.depth -= 1;
        out
    }
    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if self.error.is_some() {
            return None;
        }
        if !self.charge() {
            return None;
        }
        if self.nesting >= self.scope.closing_limits().max_depth {
            self.error = Some("materialized candidate traversal depth limit".into());
            return None;
        }
        if self.scope.named_binder_id(expr).is_some() {
            self.error = Some("materialized candidate contains deferred named binder".into());
            return None;
        }
        let key = Key(expr.clone(), self.depth, self.allow_target);
        if let Some(traversal) = self.memo.get(&key).cloned() {
            return self.reuse(&traversal).then_some(traversal.result).flatten();
        }
        let cache_key = Key(expr.clone(), self.depth, false);
        if let Some(old) = self.cache.entries.get(&cache_key).cloned() {
            if !self.charge() {
                return None;
            }
            let same_target = old.target == self.target && old.allow_target == self.allow_target;
            // An unchanged result contains no old target. If the new target is
            // outside the old authorized inventory, it cannot occur either.
            // Otherwise rewalk; never guess an exact empty dependency set.
            let independent = old.traversal.result.is_none()
                && self.target.is_none_or(|id| !old.allowed.contains(&id));
            if (same_target || independent) && self.permits(&old.allowed) {
                if self.reuse(&old.traversal) {
                    self.memo.insert(key, old.traversal.clone());
                    return old.traversal.result;
                }
                return None;
            }
            if self.error.is_some() {
                return None;
            }
        }
        let unchanged_key = Key(expr.clone(), 0, false);
        if let Some(old) = self.cache.unchanged.get(&unchanged_key).cloned() {
            if !self.charge() {
                return None;
            }
            // No abstraction took place in this entry. Its authorized FVars
            // include every actual dependency, so a new target outside that
            // inventory cannot occur. Scope owner was checked by walk(). No
            // definitions or normalization results are cached here.
            if self.target.is_none_or(|id| !old.allowed.contains(&id)) && self.permits(&old.allowed)
            {
                if self.reuse(&old.traversal) {
                    self.memo.insert(key, old.traversal);
                }
                return None;
            }
            if self.error.is_some() {
                return None;
            }
        }
        let enclosing_height = std::mem::take(&mut self.height);
        self.nesting += 1;
        let result = Stack(self).fold_expr_opt(expr);
        self.nesting -= 1;
        let height = self.height + 1;
        self.height = enclosing_height.max(height);
        if self.error.is_none() {
            let traversal = Traversal {
                result: result.clone(),
                height,
            };
            self.memo.insert(key, traversal.clone());
            let cached = Cached {
                allowed: self.allowed.clone(),
                target: self.target,
                allow_target: self.allow_target,
                traversal,
            };
            if result.is_none() && !expr.has_loose_bvars() {
                self.cache.unchanged.insert(unchanged_key, cached.clone());
            }
            self.cache.entries.insert(cache_key, cached);
        }
        result
    }
}
fn check_owner(scope: &LocalScope, cache: &mut MaterializedCache) -> Result<(), String> {
    let owner = scope.memo_owner();
    if cache.owner.as_ref().is_some_and(|old| !old.matches(&owner)) {
        return Err("foreign materialized cache owner".into());
    }
    cache.owner = Some(owner);
    Ok(())
}
fn authenticate_inventory(
    scope: &LocalScope,
    external: &[ScopedLocal],
    work: &mut usize,
    limit: usize,
) -> Result<(Rc<HashSet<FVarId>>, usize), String> {
    let mut allowed = HashSet::new();
    let mut visits = 0;
    for local in external {
        if *work >= limit || visits >= scope.closing_limits().max_visits {
            return Err("materialized external inventory work limit".into());
        }
        *work += 1;
        visits += 1;
        if !scope.owns(local) || !allowed.insert(local.id()) {
            return Err("foreign or duplicate materialized external local".into());
        }
    }
    Ok((Rc::new(allowed), visits))
}
fn walk<'a>(
    scope: &'a LocalScope,
    external: &[ScopedLocal],
    target: Option<&ScopedLocal>,
    work: &'a mut usize,
    limit: usize,
    cache: &'a mut MaterializedCache,
) -> Result<Walk<'a>, String> {
    check_owner(scope, cache)?;
    let (allowed, mut setup_visits) = authenticate_inventory(scope, external, work, limit)?;
    if let Some(target) = target {
        if *work >= limit || setup_visits >= scope.closing_limits().max_visits {
            return Err("materialized binder inventory work limit".into());
        }
        *work += 1;
        setup_visits += 1;
        if !scope.owns(target) || allowed.contains(&target.id()) {
            return Err("foreign or external materialized abstraction binder".into());
        }
    }
    Ok(Walk {
        scope,
        allowed,
        target: target.map(ScopedLocal::id),
        allow_target: false,
        depth: 0,
        nesting: 0,
        height: 0,
        visits: setup_visits,
        work,
        limit,
        memo: HashMap::new(),
        error: None,
        cache,
        inventories: InventoryPermissions::Fresh(HashMap::new()),
    })
}

/// Validate a new graph with a fixed authenticated inventory. Only inventory
/// authorization is reused; ordinary-node, relative-depth and height checks
/// still run before every existing expression-cache shortcut.
pub(crate) fn validate_materialized_in_context_cached(
    context: &mut MaterializedValidationContext<'_>,
    root: &Expr,
    work: &mut usize,
    limit: usize,
    cache: &mut MaterializedCache,
) -> Result<(), String> {
    check_owner(context.scope, cache)?;
    let mut walk = Walk {
        scope: context.scope,
        allowed: context.allowed.clone(),
        target: None,
        allow_target: false,
        depth: 0,
        nesting: 0,
        height: 0,
        // Preserve the old per-invocation owner visit floor even though the
        // same inventory authentication is charged only when actually done.
        visits: context.setup_visits,
        work,
        limit,
        memo: HashMap::new(),
        error: None,
        cache,
        inventories: InventoryPermissions::Reused(&mut context.inventories),
    };
    walk.fold_expr_opt(root);
    match walk.error {
        Some(error) => Err(error),
        None => Ok(()),
    }
}

#[cfg(test)]
#[path = "scoped_local_materialized_context_tests.rs"]
mod context_tests;
#[cfg(test)]
#[path = "scoped_local_materialized_depth_tests.rs"]
mod depth_tests;
pub(crate) fn abstract_materialized_cached(
    scope: &LocalScope,
    external: &[ScopedLocal],
    binder: &ScopedLocal,
    body: &Expr,
    work: &mut usize,
    limit: usize,
    cache: &mut MaterializedCache,
) -> Result<Expr, String> {
    let mut walk = walk(scope, external, Some(binder), work, limit, cache)?;
    let ty = walk
        .fold_expr_opt(binder.ty())
        .unwrap_or_else(|| binder.ty().clone());
    if let Some(error) = walk.error.take() {
        return Err(error);
    }
    walk.allow_target = true;
    let body = walk.fold_expr_opt(body).unwrap_or_else(|| body.clone());
    if let Some(error) = walk.error {
        return Err(error);
    }
    Ok(Expr::lam(BinderInfo::Default, ty, body))
}
pub(crate) fn validate_materialized_cached(
    scope: &LocalScope,
    external: &[ScopedLocal],
    root: &Expr,
    work: &mut usize,
    limit: usize,
    cache: &mut MaterializedCache,
) -> Result<(), String> {
    let mut walk = walk(scope, external, None, work, limit, cache)?;
    walk.fold_expr_opt(root);
    match walk.error {
        Some(error) => Err(error),
        None => Ok(()),
    }
}

#[cfg(test)]
fn abstract_materialized(
    scope: &LocalScope,
    external: &[ScopedLocal],
    binder: &ScopedLocal,
    body: &Expr,
    work: &mut usize,
    limit: usize,
) -> Result<Expr, String> {
    abstract_materialized_cached(
        scope,
        external,
        binder,
        body,
        work,
        limit,
        &mut MaterializedCache::default(),
    )
}
#[cfg(test)]
fn validate_materialized(
    scope: &LocalScope,
    external: &[ScopedLocal],
    root: &Expr,
    work: &mut usize,
    limit: usize,
) -> Result<(), String> {
    validate_materialized_cached(
        scope,
        external,
        root,
        work,
        limit,
        &mut MaterializedCache::default(),
    )
}
#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, TypeChecker};
    #[test]
    fn ordinary_abstraction_preserves_nested_binding_and_kernel_type() {
        let mut scope = LocalScope::new();
        let a = scope.try_local(Expr::type_()).unwrap();
        let x = scope.try_local(a.term().clone()).unwrap();
        let body = Expr::lam(BinderInfo::Default, a.term().clone(), x.term().clone());
        let mut work = 0;
        let lambda =
            abstract_materialized(&scope, &[a.clone()], &x, &body, &mut work, 100).unwrap();
        assert_eq!(
            lambda,
            Expr::lam(
                BinderInfo::Default,
                a.term().clone(),
                Expr::lam(BinderInfo::Default, a.term().clone(), Expr::bvar(1))
            )
        );
        let proof = scope.close(&a.lam(lambda)).unwrap();
        let claim = Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
            ),
        );
        TypeChecker::new(&Environment::new())
            .check_type(&proof, &claim)
            .unwrap();
    }
    #[test]
    fn materialized_guards_reject_deferred_loose_foreign_and_unknown() {
        let mut scope = LocalScope::new();
        let x = scope.try_local(Expr::type_()).unwrap();
        let y = scope.try_local(Expr::type_()).unwrap();
        let mut foreign = LocalScope::new();
        let foreign_x = foreign.try_local(Expr::type_()).unwrap();
        for input in [x.lam(x.term().clone()), Expr::bvar(0), y.term().clone()] {
            assert!(abstract_materialized(&scope, &[], &x, &input, &mut 0, 100).is_err());
        }
        assert!(abstract_materialized(&scope, &[], &foreign_x, x.term(), &mut 0, 100).is_err());
        assert!(validate_materialized(&scope, &[foreign_x], x.term(), &mut 0, 100).is_err());
        assert!(
            validate_materialized(&scope, &[x.clone(), x.clone()], x.term(), &mut 0, 100).is_err()
        );
        assert!(abstract_materialized(&scope, &[x.clone()], &x, x.term(), &mut 0, 100).is_err());
    }
    #[test]
    fn materialized_owner_caps_and_self_dependent_types_are_not_erased() {
        use super::super::{LocalScopeLimits, TermScopeLimits};
        for max_visits in [0, 1] {
            let scope = LocalScope::with_limits(LocalScopeLimits {
                closing: TermScopeLimits {
                    max_visits,
                    max_depth: 100,
                },
                ..LocalScopeLimits::default()
            });
            let mut work = 0;
            let root = Expr::app(Expr::type_(), Expr::type_());
            let error = validate_materialized(&scope, &[], &root, &mut work, 100).unwrap_err();
            assert!(error.contains("owner visit limit"));
            assert_eq!(work, max_visits);
        }
        let mut scope = LocalScope::new();
        let local = scope.try_local(Expr::fvar(FVarId::new(0))).unwrap();
        let error =
            abstract_materialized(&scope, &[], &local, local.term(), &mut 0, 100).unwrap_err();
        assert!(error.contains("self-dependent type"));
    }
    #[test]
    fn reused_materialized_support_keeps_actual_targets_and_inventory() {
        let mut scope = LocalScope::new();
        let x = scope.try_local(Expr::type_()).unwrap();
        let y = scope.try_local(Expr::type_()).unwrap();
        let mut cache = MaterializedCache::default();
        let mut work = 0;
        validate_materialized_cached(&scope, &[x.clone()], x.term(), &mut work, 1000, &mut cache)
            .unwrap();
        let lambda =
            abstract_materialized_cached(&scope, &[], &x, x.term(), &mut work, 1000, &mut cache)
                .unwrap();
        assert_eq!(
            lambda,
            Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))
        );
        assert!(
            validate_materialized_cached(&scope, &[], x.term(), &mut work, 1000, &mut cache)
                .is_err()
        );
        assert!(
            abstract_materialized_cached(&scope, &[], &y, x.term(), &mut work, 1000, &mut cache)
                .is_err()
        );
        let mut other = LocalScope::new();
        let other_x = other.try_local(Expr::type_()).unwrap();
        assert!(
            validate_materialized_cached(
                &other,
                &[other_x.clone()],
                other_x.term(),
                &mut work,
                1000,
                &mut cache
            )
            .unwrap_err()
            .contains("cache owner")
        );
    }
    #[test]
    fn reused_materialized_support_keeps_relative_ordinary_depth_and_unknown_refusal() {
        let scope = LocalScope::new();
        let mut cache = MaterializedCache::default();
        let mut work = 0;
        let inner = Expr::bvar(0);
        let bound = Expr::lam(BinderInfo::Default, Expr::type_(), inner.clone());
        validate_materialized_cached(&scope, &[], &bound, &mut work, 1000, &mut cache).unwrap();
        assert!(
            validate_materialized_cached(&scope, &[], &inner, &mut work, 1000, &mut cache)
                .unwrap_err()
                .contains("loose")
        );
        let invalid = Expr::app(Expr::type_(), Expr::bvar(7));
        for _ in 0..2 {
            assert!(
                validate_materialized_cached(&scope, &[], &invalid, &mut work, 1000, &mut cache)
                    .unwrap_err()
                    .contains("loose")
            );
        }
        let before = work;
        assert!(
            validate_materialized_cached(&scope, &[], &bound, &mut work, before, &mut cache)
                .is_err()
        );
        assert_eq!(work, before);
    }
    #[test]
    fn fresh_binder_reuse_reduces_walks_without_assuming_dependencies_empty() {
        let mut scope = LocalScope::new();
        let x = scope.try_local(Expr::type_()).unwrap();
        let y = scope.try_local(Expr::type_()).unwrap();
        let z = scope.try_local(Expr::type_()).unwrap();
        let mut body = x.term().clone();
        for _ in 0..100 {
            body = Expr::app(body, x.term().clone());
        }
        let mut cache = MaterializedCache::default();
        let mut work = 0;
        let _initial = abstract_materialized_cached(
            &scope,
            &[x.clone()],
            &y,
            &body,
            &mut work,
            10000,
            &mut cache,
        )
        .unwrap();
        let initial = work;
        let reused = abstract_materialized_cached(
            &scope,
            &[x.clone()],
            &z,
            &body,
            &mut work,
            10000,
            &mut cache,
        )
        .unwrap();
        assert!(work - initial < initial);
        let mut fresh_work = 0;
        let fresh = abstract_materialized(&scope, &[x], &z, &body, &mut fresh_work, 10000).unwrap();
        assert_eq!(reused, fresh);
        assert!(work - initial < fresh_work);
    }
    #[test]
    fn materialized_cache_keeps_high_free_ids_and_bound_depth_dependencies() {
        let mut scope = LocalScope::new();
        let locals = (0..135)
            .map(|_| scope.try_local(Expr::type_()).unwrap())
            .collect::<Vec<_>>();
        let high = &locals[132];
        let mut cache = MaterializedCache::default();
        let mut work = 0;
        validate_materialized_cached(
            &scope,
            &[high.clone()],
            high.term(),
            &mut work,
            10000,
            &mut cache,
        )
        .unwrap();
        assert!(
            validate_materialized_cached(&scope, &[], high.term(), &mut work, 10000, &mut cache)
                .is_err()
        );
        let retargeted = abstract_materialized_cached(
            &scope,
            &[],
            high,
            high.term(),
            &mut work,
            10000,
            &mut cache,
        )
        .unwrap();
        assert_eq!(
            retargeted,
            Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))
        );
        let inner = Expr::bvar(131);
        let mut body = inner.clone();
        let mut claim = Expr::type_();
        for _ in 0..132 {
            body = Expr::lam(BinderInfo::Default, Expr::type_(), body);
            claim = Expr::pi(BinderInfo::Default, Expr::type_(), claim);
        }
        validate_materialized_cached(&scope, &[], &body, &mut work, 10000, &mut cache).unwrap();
        TypeChecker::new(&Environment::new())
            .check_type(&body, &claim)
            .unwrap();
        assert!(
            validate_materialized_cached(&scope, &[], &inner, &mut work, 10000, &mut cache)
                .unwrap_err()
                .contains("loose")
        );
    }
    #[test]
    fn materialized_work_is_cumulative_and_refusal_does_not_reset_it() {
        let scope = LocalScope::new();
        let root = Expr::type_();
        let mut work = 0;
        validate_materialized(&scope, &[], &root, &mut work, 1).unwrap();
        assert_eq!(work, 1);
        for _ in 0..2 {
            assert!(validate_materialized(&scope, &[], &root, &mut work, 1).is_err());
            assert_eq!(work, 1);
        }
    }
}
