// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Conservative search support for one fixed replacement attempt. This is not
//! an input-admission, typing, closure or absence premise for kernel replay.
use super::*;

#[derive(Clone, Copy)]
struct Summary {
    possible: bool,
    height: usize,
}

pub(super) struct Support<'a, 'e> {
    checker: &'a TypeChecker<'e>,
    scope: &'a crate::scoped_local::LocalScope,
    target: &'a Expr,
    nodes: HashMap<Key, Summary>,
    bound: usize,
    max_app_args: usize,
    failed: bool,
}

impl<'a, 'e> Support<'a, 'e> {
    pub(super) fn new(
        checker: &'a TypeChecker<'e>,
        scope: &'a crate::scoped_local::LocalScope,
        target: &'a Expr,
        bound: usize,
        max_app_args: usize,
    ) -> Self {
        Self {
            checker,
            scope,
            target,
            nodes: HashMap::new(),
            bound,
            max_app_args,
            failed: false,
        }
    }

    pub(super) fn excludes(
        &mut self,
        expression: &Expr,
        work: &mut Work<'_>,
        remaining_depth: usize,
    ) -> Result<bool, String> {
        if self.failed {
            return Err("Case support retains a failed search".into());
        }
        if self.bound == 0 {
            return Ok(false);
        }
        if self.checker.heartbeat_spent() {
            self.failed = true;
            return Err("Case support kernel budget".into());
        }
        let mut scan = Scan {
            support: self,
            work,
            depth: 0,
            max_depth: remaining_depth,
            height: 0,
            possible: false,
            unknown: false,
            error: None,
        };
        let _unchanged = scan.fold_expr_opt(expression);
        if let Some(error) = scan.error {
            scan.support.failed = true;
            return Err(error);
        }
        Ok(!scan.unknown && !scan.possible)
    }
}

struct Scan<'a, 'b, 'c, 'e> {
    support: &'a mut Support<'b, 'e>,
    work: &'a mut Work<'c>,
    depth: usize,
    max_depth: usize,
    height: usize,
    possible: bool,
    unknown: bool,
    error: Option<String>,
}
impl Scan<'_, '_, '_, '_> {
    fn pay(&mut self, amount: usize) -> bool {
        match self.work.pay(amount) {
            Ok(()) => true,
            Err(error) => {
                self.error = Some(error);
                false
            }
        }
    }
    fn fits(&self, height: usize) -> bool {
        height
            .checked_sub(1)
            .and_then(|height| self.depth.checked_add(height))
            .is_some_and(|end| end <= self.max_depth)
    }
    fn root_possible(&mut self, expression: &Expr) -> Option<bool> {
        if expression.has_loose_bvars() {
            return Some(false);
        }
        if !self.pay(1) {
            return None;
        }
        let normalized = self.support.checker.whnf(expression);
        if self.support.checker.heartbeat_spent() {
            self.error = Some("Case support kernel budget".into());
            return None;
        }
        if normalized.hash_cached() == self.support.target.hash_cached() {
            return Some(true); // collisions only prevent pruning
        }
        if !crate::proof_assembly::normalize::same_graph(expression, &normalized) {
            match administrative_redex(expression, self.work, self.support.max_app_args) {
                Ok(true) => return Some(true),
                Ok(false) => {}
                Err(error) => {
                    self.error = Some(error);
                    return None;
                }
            }
        }
        Some(false)
    }
}
struct Stack<'a, 'b, 'c, 'd, 'e>(&'a mut Scan<'b, 'c, 'd, 'e>);
impl ExprFolderOpt for Stack<'_, '_, '_, '_, '_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(expression)
    }
}
impl ExprFolderOpt for Scan<'_, '_, '_, '_> {
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        if self.unknown || self.error.is_some() || !self.pay(1) {
            return None;
        }
        if self.depth > self.max_depth {
            self.unknown = true; // only the original walk decides depth refusal
            return None;
        }
        match expression.kind() {
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(..)
            | ExprKind::Lit(_)
            | ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => {
                if let Some(possible) = self.root_possible(expression) {
                    self.possible |= possible;
                    self.height = self.height.max(1);
                }
                return None;
            }
            ExprKind::Lam(..) | ExprKind::Pi(..) | ExprKind::Let(..) => {
                if !self.pay(1) {
                    return None;
                }
                if self.support.scope.named_binder_id(expression).is_some() {
                    self.unknown = true;
                    return None;
                }
            }
            _ => {}
        }
        if !self.pay(2) {
            return None;
        } // exact graph probe and pin, before any retained storage
        let key = Key(expression.clone());
        if let Some(known) = self.support.nodes.get(&key).copied() {
            if !self.fits(known.height) {
                self.unknown = true;
            } else {
                self.height = self.height.max(known.height);
                self.possible |= known.possible;
            }
            return None;
        }
        let parent_height = std::mem::take(&mut self.height);
        let parent_possible = std::mem::take(&mut self.possible);
        self.depth += 1;
        let _unchanged = Stack(self).fold_expr_opt(expression);
        self.depth -= 1;
        if self.unknown || self.error.is_some() {
            return None;
        }
        let Some(height) = self.height.checked_add(1) else {
            self.error = Some("Case support height overflow".into());
            return None;
        };
        if !self.possible {
            let Some(possible) = self.root_possible(expression) else {
                return None;
            };
            self.possible = possible;
        }
        let summary = Summary {
            possible: self.possible,
            height,
        };
        if self.support.nodes.len() < self.support.bound {
            if !self.pay(2) {
                return None;
            } // insertion probe and retained entry; key pin was already paid
            self.support.nodes.insert(key, summary);
        }
        self.height = parent_height.max(height);
        self.possible |= parent_possible;
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scoped_local::LocalScope;

    fn target() -> Expr {
        Expr::app(Expr::const_str("Support.stuck"), Expr::nat_lit(7))
    }
    fn chain(mut value: Expr, count: usize) -> Expr {
        for _ in 0..count {
            value = Expr::app(Expr::const_str("Nat.succ"), value);
        }
        value
    }
    fn parts(scope: &LocalScope) -> ProofComponents {
        let mut parts = ProofComponents::new("Case.support.control", Default::default());
        parts.set_base(scope, vec![]).unwrap();
        parts
    }
    fn ask(
        support: &mut Support<'_, '_>,
        parts: &mut ProofComponents,
        root: &Expr,
        depth: usize,
        limit: usize,
    ) -> (Result<bool, String>, usize) {
        let before = parts.counts().3;
        let mut used = 0;
        let result = support.excludes(
            root,
            &mut Work {
                components: parts,
                used: &mut used,
                limit,
            },
            depth,
        );
        assert!(used <= limit);
        assert_eq!(parts.counts().3 - before, used);
        assert_eq!(parts.counts().0, 0);
        (result, used)
    }

    #[test]
    fn target_support_rechecks_changed_graph_and_never_excludes_its_actual_target() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let checker = TypeChecker::new(&env);
        let scope = LocalScope::new();
        let target = target();
        let mut support = Support::new(&checker, &scope, &target, 1000, 256);
        let mut parts = parts(&scope);
        let ordinary = chain(Expr::nat_lit(0), 20);
        let (result, cold) = ask(&mut support, &mut parts, &ordinary, 50, 100_000);
        assert!(result.unwrap());
        let (result, hot) = ask(&mut support, &mut parts, &ordinary, 50, 100_000);
        assert!(result.unwrap());
        assert!(hot > 0 && hot < cold);
        assert!(
            !ask(&mut support, &mut parts, &target, 50, 100_000)
                .0
                .unwrap()
        );
        assert!(
            !ask(
                &mut support,
                &mut parts,
                &chain(target.clone(), 20),
                50,
                100_000
            )
            .0
            .unwrap()
        );
    }

    #[test]
    fn target_support_retains_complete_closed_input_height_before_deeper_reuse() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let checker = TypeChecker::new(&env);
        let scope = LocalScope::new();
        let target = target();
        let mut support = Support::new(&checker, &scope, &target, 1000, 256);
        let mut parts = parts(&scope);
        let closed = chain(Expr::nat_lit(0), 30);
        assert!(
            ask(&mut support, &mut parts, &closed, 40, 100_000)
                .0
                .unwrap()
        );
        assert_eq!(support.nodes[&Key(closed.clone())].height, 31);
        assert!(
            !ask(&mut support, &mut parts, &closed, 20, 100_000)
                .0
                .unwrap()
        );
        assert!(
            !ask(&mut support, &mut parts, &chain(closed, 15), 35, 100_000)
                .0
                .unwrap()
        );
    }

    #[test]
    fn target_support_leaves_named_and_administratively_created_matches_to_the_original_path() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let checker = TypeChecker::new(&env);
        let mut scope = LocalScope::new();
        let formal = scope.try_local(Expr::const_str("Nat")).unwrap();
        let target = target();
        let mut support = Support::new(&checker, &scope, &target, 1000, 256);
        let mut parts = parts(&scope);
        let named = formal.lam(Expr::nat_lit(0));
        assert!(
            !ask(&mut support, &mut parts, &named, 50, 100_000)
                .0
                .unwrap()
        );
        assert!(!support.nodes.contains_key(&Key(named)));
        // Beta creates the target as a descendant, rather than exposing it at
        // this root. A raw-child summary must not hide the canonical path.
        let created = Expr::app(
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                Expr::const_str("Nat"),
                Expr::app(
                    Expr::const_str("Support.pack"),
                    Expr::app(Expr::const_str("Support.stuck"), Expr::bvar(0)),
                ),
            ),
            Expr::nat_lit(7),
        );
        assert!(
            !ask(&mut support, &mut parts, &created, 50, 100_000)
                .0
                .unwrap()
        );
    }

    #[test]
    fn target_support_prepays_each_cutoff_and_failed_searches_cannot_be_reused() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let checker = TypeChecker::new(&env);
        let scope = LocalScope::new();
        let target = target();
        let root = chain(Expr::nat_lit(0), 12);
        let (mut passed, mut refused) = (0, 0);
        for limit in 0..256 {
            let mut support = Support::new(&checker, &scope, &target, 1000, 256);
            let mut parts = parts(&scope);
            match ask(&mut support, &mut parts, &root, 50, limit).0 {
                Ok(excluded) => {
                    assert!(excluded);
                    passed += 1;
                }
                Err(_) => {
                    refused += 1;
                    assert!(support.failed);
                    assert!(ask(&mut support, &mut parts, &root, 50, 100_000).0.is_err());
                }
            }
        }
        assert!(passed > 0 && refused > 0);
    }

    #[test]
    fn target_support_storage_bound_and_disabled_mode_do_not_expand_the_entry_cap() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let checker = TypeChecker::new(&env);
        let scope = LocalScope::new();
        let target = target();
        let root = chain(Expr::nat_lit(0), 30);
        let mut parts = parts(&scope);
        let mut disabled = Support::new(&checker, &scope, &target, 0, 256);
        assert!(
            !ask(&mut disabled, &mut parts, &root, 50, 100_000)
                .0
                .unwrap()
        );
        assert!(disabled.nodes.is_empty());
        let mut bounded = Support::new(&checker, &scope, &target, 4, 256);
        assert!(ask(&mut bounded, &mut parts, &root, 50, 100_000).0.unwrap());
        assert_eq!(bounded.nodes.len(), 4);
    }

    #[test]
    fn target_support_keeps_the_finite_kernel_budget_and_poisoned_failure() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let mut checker = TypeChecker::new(&env);
        checker.set_heartbeat_limit(1);
        let scope = LocalScope::new();
        let target = target();
        let mut support = Support::new(&checker, &scope, &target, 1000, 256);
        let mut parts = parts(&scope);
        let root = chain(Expr::nat_lit(0), 12);
        let error = ask(&mut support, &mut parts, &root, 50, 100_000)
            .0
            .unwrap_err();
        assert!(error.contains("kernel budget"), "{error}");
        assert!(support.failed);
    }
}
