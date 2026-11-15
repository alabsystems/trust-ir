// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Exact lexical-prefix proofs for all-Named dependency DAGs.
//! Lexical context IDs intern (parent, frame), so an equal ID names the same
//! ordered binder prefix. Forest externals are not lexical binders. No hashes
//! of expressions, copied footprints or new budgets.

use super::*;

#[derive(Clone, Copy)]
pub(super) struct NamedPrefix {
    depth: u32,
    context: usize,
}

impl Closer<'_> {
    fn prefix_matches(&self, prefix: NamedPrefix) -> bool {
        self.active.stack_consistent()
            && self.context_stack.len() == self.binder_depth as usize
            && prefix.depth != 0
            && self
                .context_stack
                .get(prefix.depth as usize - 1)
                .is_some_and(|(context, _)| *context == prefix.context)
    }

    pub(super) fn dependency_named_prefix(&self, dependency: Dependency) -> Option<NamedPrefix> {
        match dependency {
            Dependency::Named(id, depth) => {
                let (context, frame) = *self.context_stack.get(depth as usize)?;
                let prefix = NamedPrefix {
                    depth: depth.checked_add(1)?,
                    context,
                };
                (frame == Frame::Named(id)
                    && self.active.get(&id) == Some(&depth)
                    && self.prefix_matches(prefix))
                .then_some(prefix)
            }
            Dependency::Join(left, right) => {
                let left = self.dependencies[left].named_prefix?;
                let right = self.dependencies[right].named_prefix?;
                if !self.prefix_matches(left) || !self.prefix_matches(right) {
                    return None;
                }
                Some(if left.depth >= right.depth {
                    left
                } else {
                    right
                })
            }
            Dependency::Ordinary(_, _) => None,
        }
    }

    pub(super) fn refresh_named_prefix(&mut self, index: usize) {
        if let Some(prefix) = self.dependency_named_prefix(self.dependencies[index].dependency) {
            self.dependencies[index].named_prefix = Some(prefix);
        }
    }

    pub(super) fn known_named_prefix(&self, index: usize, cached_depth: u32) -> bool {
        self.dependencies[index]
            .named_prefix
            .is_some_and(|prefix| prefix.depth <= cached_depth && self.prefix_matches(prefix))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Environment, TypeChecker};

    fn id(value: u64) -> FVarId {
        FVarId::new(value)
    }
    fn nat() -> Expr {
        Expr::const_str("Nat")
    }
    fn sum(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Nat.add"), [a, b])
    }

    #[test]
    fn external_admission_does_not_alias_a_former_lexical_context() {
        let mut scope = TermScope::new();
        let local = id(1);
        let first = scope.lam(local, BinderInfo::Default, nat(), Expr::fvar(local));
        let ExprKind::Lam(_, _, body) = first.kind() else {
            unreachable!();
        };
        // Use the exact same input allocation once as a lexical read, then as
        // an explicitly admitted external. The two outputs have different scope.
        let successor = Expr::const_str("Nat.succ");
        let second = Expr::app_arc(Arc::new(successor.clone()), body.clone());
        let (result, _) = scope.close_external_forest(
            &[first, second],
            &[local],
            &[0, 1],
            TermScopeLimits::default(),
        );
        let closed = result.unwrap();
        assert_eq!(
            closed[0],
            Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0))
        );
        assert_eq!(closed[1], Expr::app(successor, Expr::fvar(local)));
    }

    #[test]
    fn external_prefix_growth_reuses_unchanged_lexical_dependencies() {
        let mut scope = TermScope::new();
        let mut term = Expr::fvar(id(100));
        for local in 101..164 {
            term = sum(term, Expr::fvar(id(local)));
        }
        for local in (100..164).rev() {
            term = scope.lam(id(local), BinderInfo::Default, nat(), term);
        }
        let (seed, baseline) = scope.close_external_forest(
            std::slice::from_ref(&term),
            &[],
            &[0],
            TermScopeLimits::default(),
        );
        let expected = seed.unwrap().pop().unwrap();
        let roots = [term.clone(), term];
        let (closed, stats) = scope.close_external_forest(
            &roots,
            &[id(1)],
            &[0, 1],
            TermScopeLimits {
                max_visits: baseline.visits + 16,
                ..TermScopeLimits::default()
            },
        );
        assert_eq!(
            closed.unwrap_or_else(|error| panic!("growing forest: {error}; {stats:?}")),
            [expected.clone(), expected.clone()]
        );
        eprintln!(
            "growing forest: seed visits={}, total visits={}, context checks={}, declaration checks={}",
            baseline.visits, stats.visits, stats.context_check_visits, stats.scope_check_visits
        );

        let mut env = Environment::new();
        env.init_nat().unwrap();
        let mut checker = TypeChecker::new(&env);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        let expected_type = (0..64).fold(nat(), |ty, _| Expr::arrow(nat(), ty));
        checker.check_type(&expected, &expected_type).unwrap();

        // An unchanged outside lexical stack is not permission to skip the
        // declaration footprint: the new external collides with an inner binder.
        let (shadow, _) =
            scope.close_external_forest(&roots, &[id(101)], &[0, 1], TermScopeLimits::default());
        assert_eq!(shadow.unwrap_err(), TermScopeError::ShadowedLocal(id(101)));
    }

    #[test]
    fn lexical_prefix_shortcut_keeps_the_exact_term_and_rejects_a_different_binder() {
        let mut scope = TermScope::new();
        let shared = Arc::new(sum(Expr::fvar(id(1)), Expr::fvar(id(2))));
        let first = Expr::app(
            Expr::lam_arc(BinderInfo::Default, Arc::new(nat()), shared.clone()),
            Expr::nat_lit(0u64),
        );
        let second = Expr::apps(
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam_arc(BinderInfo::Default, Arc::new(nat()), shared),
            ),
            [Expr::nat_lit(0u64), Expr::nat_lit(0u64)],
        );
        let body = scope.lam(id(2), BinderInfo::Default, nat(), sum(first, second));
        let open = scope.lam(id(1), BinderInfo::Default, nat(), body);
        let report = scope.close_with_diagnostics(&open, TermScopeLimits::default());
        assert!(report.diagnostics.cache.named_prefix_proofs > 0);
        let closed = report.result.unwrap();
        let first = Expr::app(
            Expr::lam(
                BinderInfo::Default,
                nat(),
                sum(Expr::bvar(2), Expr::bvar(1)),
            ),
            Expr::nat_lit(0u64),
        );
        let second = Expr::apps(
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam(
                    BinderInfo::Default,
                    nat(),
                    sum(Expr::bvar(3), Expr::bvar(2)),
                ),
            ),
            [Expr::nat_lit(0u64), Expr::nat_lit(0u64)],
        );
        let expected = Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(BinderInfo::Default, nat(), sum(first, second)),
        );
        assert_eq!(closed, expected);
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let mut checker = TypeChecker::new(&env);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker
            .check_type(&closed, &Expr::arrow(nat(), Expr::arrow(nat(), nat())))
            .unwrap();

        let shared = Arc::new(sum(Expr::fvar(id(1)), Expr::fvar(id(2))));
        let left = scope.lam(
            id(2),
            BinderInfo::Default,
            nat(),
            Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone()),
        );
        let right = scope.lam(
            id(3),
            BinderInfo::Default,
            nat(),
            Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared),
        );
        let bad = scope.lam(id(1), BinderInfo::Default, nat(), Expr::app(left, right));
        assert_eq!(scope.close(&bad), Err(TermScopeError::OutOfScope(id(2))));
    }

    #[test]
    fn mixed_dependency_checks_use_the_named_prefix_and_verify_ordinary_reads() {
        let scope = TermScope::new();
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        closer.ordinary.push(0);
        closer.context_stack.push((1, Frame::Ordinary));
        closer.binder_depth = 1;

        let mut named = None;
        for depth in 1..=32 {
            let local = id(u64::from(depth));
            closer.active.insert_scoped(local, depth);
            closer
                .context_stack
                .push((depth as usize + 1, Frame::Named(local)));
            closer.binder_depth += 1;
            let leaf = closer.named_read_dependency(local, depth);
            named = Some(match named {
                Some(previous) => closer.union_dependencies(previous, leaf),
                None => leaf,
            });
        }
        let ordinary = closer.dependency_node(Dependency::Ordinary(0, 0));
        let mixed = closer.union_dependencies(named.unwrap(), ordinary);
        assert!(closer.visit());
        closer.limits.max_visits = closer.stats.visits + 3;
        assert!(closer.same_dependencies(Some(mixed)));

        closer.ordinary.clear();
        closer.limits.max_visits += 3;
        assert!(!closer.same_dependencies(Some(mixed)));
        assert_eq!(closer.error, None);
    }

    #[test]
    fn prefix_proofs_never_cover_ordinary_reads_untracked_updates_or_spent_budgets() {
        let scope = TermScope::new();
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        closer.context = 1;
        closer.binder_depth = 1;
        closer.context_stack.push((1, Frame::Named(id(7))));
        closer.active.insert_scoped(id(7), 0);
        let named = closer.named_read_dependency(id(7), 0);
        assert!(closer.known_named_prefix(named, 1));
        let ordinary = closer.dependency_node(Dependency::Ordinary(0, 0));
        let mixed = closer.union_dependencies(named, ordinary);
        assert!(!closer.known_named_prefix(mixed, 1));
        assert!(!closer.known_named_prefix(named, 0));
        assert!(closer.visit()); // the enclosing expression request
        closer.limits.max_visits = closer.stats.visits;
        assert!(!closer.same_dependencies(Some(named)));
        assert_eq!(closer.error, Some(TermScopeError::VisitLimit));
        closer.error = None;
        closer.limits = TermScopeLimits::default();
        closer.active.insert(id(7), 1);
        assert!(!closer.known_named_prefix(named, 1));
        assert!(closer.visit());
        assert!(!closer.same_dependencies(Some(named)));
    }
}
