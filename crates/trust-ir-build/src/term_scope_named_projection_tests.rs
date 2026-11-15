// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

use super::*;
use clean_kernel::{BinderInfo, Environment, KernelTypeError, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn sum() -> Expr {
    Expr::apps(
        Expr::const_str("Nat.add"),
        [
            Expr::fvar(id(1)),
            Expr::apps(
                Expr::const_str("Nat.add"),
                [Expr::fvar(id(2)), Expr::bvar(0)],
            ),
        ],
    )
}
fn eq(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), left, right],
    )
}
fn inner_goal(wrong: bool) -> Expr {
    let value = sum();
    let right = if wrong {
        Expr::app(Expr::const_str("Nat.succ"), value.clone())
    } else {
        value.clone()
    };
    Expr::pi(BinderInfo::Default, nat(), eq(value, right))
}
fn wrap(scope: &mut TermScope, names: &[u64], shared: &Arc<Expr>) -> Expr {
    let mut term = Expr::app_arc(
        Arc::new(Expr::lam(
            BinderInfo::Default,
            inner_goal(false),
            Expr::bvar(0),
        )),
        shared.clone(),
    );
    for raw in names.iter().rev() {
        term = scope.lam(id(*raw), BinderInfo::Default, nat(), term);
    }
    term
}
fn reference(names: &[u64], shared: &Expr) -> Expr {
    let mut term = Expr::app(
        Expr::lam(BinderInfo::Default, inner_goal(false), Expr::bvar(0)),
        shared.clone(),
    );
    for raw in names.iter().rev() {
        term = Expr::lam(BinderInfo::Default, nat(), term.abstract_fvar(id(*raw)));
    }
    term
}
fn goal(names: &[u64], wrong: bool) -> Expr {
    let mut term = inner_goal(wrong);
    for raw in names.iter().rev() {
        term = Expr::pi(BinderInfo::Default, nat(), term.abstract_fvar(id(*raw)));
    }
    term
}

#[test]
fn nonuniform_projection_preserves_internal_binder_proofs_in_both_directions() {
    let shared = Arc::new(Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [nat(), sum()],
        ),
    ));
    for names in [
        [vec![1, 2, 3], vec![2, 1, 4, 3]],
        [vec![2, 1, 4, 3], vec![1, 2, 3]],
    ] {
        let mut scope = TermScope::new();
        let arms = names
            .iter()
            .map(|names| wrap(&mut scope, names, &shared))
            .collect::<Vec<_>>();
        let input = Expr::apps(Expr::const_str("structural"), arms);
        let report = scope.close_with_diagnostics(&input, TermScopeLimits::default());
        let closed = report.result.unwrap();
        assert!(report.diagnostics.cache.named_projection_contextual_hits > 0);
        assert!(report.diagnostics.cache.named_projection_output_visits > 0);
        let mut env = Environment::new();
        env.init_eq().unwrap();
        env.init_nat().unwrap();
        for (arm, names) in closed.get_app_args().iter().zip(&names) {
            assert_eq!(**arm, reference(names, &shared));
            let bytes = trust_ir::proof::encode_clean_expr_dag_v2(arm).unwrap();
            let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
            assert_eq!(decoded, **arm);
            assert_eq!(
                trust_ir::proof::encode_clean_expr_dag_v2(&decoded).unwrap(),
                bytes
            );
            for proof in [*arm, &decoded] {
                let mut checker = TypeChecker::new(&env);
                checker.set_heartbeat_limit(2_000_000);
                checker.set_allow_unsafe(false);
                checker.set_allow_partial(false);
                checker.check_type(proof, &goal(names, false)).unwrap();
                assert!(!checker.heartbeat_spent());
                let mut mutant = TypeChecker::new(&env);
                mutant.set_heartbeat_limit(2_000_000);
                mutant.set_allow_unsafe(false);
                mutant.set_allow_partial(false);
                assert!(matches!(
                    mutant.check_type(proof, &goal(names, true)),
                    Err(KernelTypeError::TypeMismatch { .. })
                ));
                assert!(!mutant.heartbeat_spent());
                assert!(
                    env.audit_certification(&goal(names, false), proof)
                        .is_certified()
                );
                assert!(
                    !env.audit_certification(&goal(names, true), proof)
                        .is_certified()
                );
            }
        }
        let cache = report.diagnostics.cache;
        assert_eq!(
            cache.successful_dependency_probe_visits + cache.rejected_dependency_probe_visits,
            report.stats.context_check_visits
        );
    }
}

fn candidate(closer: &mut Closer<'_>) -> ContextEntry {
    let left = closer.dependency_node(Dependency::Named(id(1), 0));
    let right = closer.dependency_node(Dependency::Named(id(2), 1));
    let root = closer.union_dependencies(left, right);
    ContextEntry {
        entry: MemoEntry {
            replacement: Some(Arc::new(Expr::app(Expr::bvar(2), Expr::bvar(1)))),
            declarations: None,
            dependencies: MemoEntry::compact(Some(root)),
        },
        context: 1,
        binder_depth: 3,
        ordinary_count: 0,
    }
}
fn setup(closer: &mut Closer<'_>) {
    closer.binder_depth = 4;
    closer.active.extend([(id(1), 0), (id(2), 2)]);
}

#[test]
fn every_finite_projection_cap_refuses_without_publishing_or_refunding() {
    let scope = TermScope::new();
    let input = Expr::app(Expr::fvar(id(1)), Expr::fvar(id(2)));
    let mut full = Closer::new(&scope, TermScopeLimits::default(), true);
    setup(&mut full);
    let cached = candidate(&mut full);
    let (entry, mapped) = full.named_output_projection(&cached, &input).unwrap();
    assert!(mapped);
    assert_eq!(
        *entry.replacement.unwrap(),
        Expr::app(Expr::bvar(3), Expr::bvar(1))
    );
    for cap in 0..full.stats.visits {
        let mut closer = Closer::new(
            &scope,
            TermScopeLimits {
                max_visits: cap,
                ..TermScopeLimits::default()
            },
            true,
        );
        setup(&mut closer);
        let cached = candidate(&mut closer);
        assert!(
            closer.named_output_projection(&cached, &input).is_none(),
            "cap={cap}"
        );
        assert_eq!(closer.error, Some(TermScopeError::VisitLimit));
        assert_eq!(closer.stats.visits, cap);
        assert!(closer.memo.is_empty() && closer.contextual.maps().0.is_empty());
        assert!(closer.shifted_outputs.is_empty());
        let cache = closer.diagnostic_report().cache;
        assert_eq!(
            cache.successful_dependency_probe_visits + cache.rejected_dependency_probe_visits,
            closer.stats.context_check_visits
        );
    }
}

#[test]
fn mapping_refuses_missing_ordinary_declarations_loose_and_incomplete_endpoints() {
    let scope = TermScope::new();
    let input = Expr::app(Expr::fvar(id(1)), Expr::fvar(id(2)));
    for mutation in 0..7 {
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        setup(&mut closer);
        let mut cached = candidate(&mut closer);
        let mut source = input.clone();
        match mutation {
            0 => {
                closer.active.remove(&id(2));
            }
            1 => {
                let leaf = closer.dependency_node(Dependency::Ordinary(0, 0));
                cached.entry.dependencies = MemoEntry::compact(Some(leaf));
            }
            2 => {
                cached.entry.declarations =
                    MemoEntry::compact(Some(closer.declarations(Declarations::Local(id(7)))));
            }
            3 => {
                source = Expr::app(source, Expr::bvar(0));
            }
            4 => {
                cached.entry.replacement = Some(Arc::new(Expr::bvar(0)));
            }
            5 => {
                closer.active.insert(id(2), 4);
            }
            6 => {
                let bad = closer.dependency_node(Dependency::Named(id(2), 0));
                let old = cached.entry.dependencies().unwrap();
                cached.entry.dependencies =
                    MemoEntry::compact(Some(closer.union_dependencies(old, bad)));
            }
            _ => unreachable!(),
        }
        assert!(
            closer.mapped_named_output(&cached, &source).is_none(),
            "mutation={mutation}"
        );
        assert_eq!(closer.error, None);
        assert!(closer.shifted_outputs.is_empty());
        assert!(closer.memo.is_empty() && closer.contextual.maps().0.is_empty());
    }
}

#[test]
fn mapped_visitor_preserves_cutoffs_and_never_reuses_uniform_cache() {
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    closer.binder_depth = 4;
    let child = Arc::new(Expr::app(Expr::bvar(0), Expr::bvar(1)));
    let input = Arc::new(Expr::app_arc(
        child.clone(),
        Arc::new(Expr::lam_arc(BinderInfo::Default, Arc::new(nat()), child)),
    ));
    let uniform = OutputShift {
        closer: &mut closer,
        delta: 9,
        renaming: None,
        refused: false,
        cutoff: 0,
        guard_extent: 0,
        named: NamedFootprint::default(),
        memo: HashMap::new(),
    }
    .shared_arc(&input)
    .unwrap();
    let retained = closer.shifted_outputs.len();
    let mut mapped = OutputShift {
        closer: &mut closer,
        delta: 9,
        renaming: Some(Arc::new(HashMap::from([(0, 2), (1, 0)]))),
        refused: false,
        cutoff: 0,
        guard_extent: 0,
        named: NamedFootprint::default(),
        memo: HashMap::new(),
    };
    let result = mapped.shared_arc(&input).unwrap();
    assert!(!mapped.refused);
    assert_eq!(mapped.closer.shifted_outputs.len(), retained);
    assert_ne!(*result, *uniform);
    assert_eq!(
        *result,
        Expr::app(
            Expr::app(Expr::bvar(2), Expr::bvar(0)),
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::app(Expr::bvar(0), Expr::bvar(3))
            )
        )
    );
    let before = closer
        .diagnostic_report()
        .cache
        .named_projection_output_changed_nodes;
    let mut identity = OutputShift {
        closer: &mut closer,
        delta: 0,
        renaming: Some(Arc::new(HashMap::from([(0, 0), (1, 1)]))),
        refused: false,
        cutoff: 0,
        guard_extent: 0,
        named: NamedFootprint::default(),
        memo: HashMap::new(),
    };
    assert!(identity.shared_arc(&input).is_none());
    assert!(!identity.refused);
    assert_eq!(
        identity
            .closer
            .diagnostic_report()
            .cache
            .named_projection_output_changed_nodes,
        before
    );
    let mut overflow = OutputShift {
        closer: &mut closer,
        delta: 0,
        renaming: Some(Arc::new(HashMap::from([(0, Expr::MAX_BVAR_INDEX)]))),
        refused: false,
        cutoff: 1,
        guard_extent: 0,
        named: NamedFootprint::default(),
        memo: HashMap::new(),
    };
    assert!(overflow.shared(&Expr::bvar(1)).is_none());
    assert_eq!(overflow.closer.error, Some(TermScopeError::IndexOverflow));
}

#[test]
fn mapped_subtree_reuse_checks_only_used_indices_and_replays_depth_guards() {
    fn project(
        closer: &mut Closer<'_>,
        input: &Arc<Expr>,
        pairs: &[(u32, u32)],
    ) -> (Option<Arc<Expr>>, bool) {
        let mut shift = OutputShift {
            closer,
            delta: 0,
            renaming: Some(Arc::new(pairs.iter().copied().collect())),
            refused: false,
            cutoff: 0,
            guard_extent: 0,
            named: NamedFootprint::default(),
            memo: HashMap::new(),
        };
        let result = shift.shared_arc(input);
        (result, shift.refused)
    }

    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let input = Arc::new(Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::app(Expr::bvar(0), Expr::app(Expr::bvar(1), Expr::bvar(1))),
    ));

    let baseline = project(&mut closer, &input, &[(0, 3), (2, 8)]).0.unwrap();
    let before = closer.stats.visits;
    let reused = project(&mut closer, &input, &[(0, 3), (2, 10)]).0.unwrap();
    assert!(Arc::ptr_eq(&baseline, &reused));
    assert_eq!(closer.stats.visits - before, 1);

    let different = project(&mut closer, &input, &[(0, 4)]).0.unwrap();
    assert_ne!(different, baseline);
    assert_eq!(project(&mut closer, &input, &[(2, 10)]), (None, true));
    assert_eq!(closer.error, None);

    closer.walk_depth = closer.limits.max_depth - 1;
    assert_eq!(project(&mut closer, &input, &[(0, 4)]).0, None);
    assert_eq!(closer.error, Some(TermScopeError::DepthLimit));

    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let nested = Arc::new(Expr::lam_arc(BinderInfo::Default, Arc::new(nat()), input));
    assert!(project(&mut closer, &nested, &[(0, 4)]).0.is_none());
    // The inner expression uses only the outer local binder under this cutoff.
    // A separate input with one external occurrence exercises the completed
    // cache's binder overflow guard.
    let nested = Arc::new(Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(2)),
    ));
    assert!(project(&mut closer, &nested, &[(0, 4)]).0.is_some());
    closer.binder_depth = Expr::MAX_BVAR_INDEX;
    assert_eq!(project(&mut closer, &nested, &[(0, 4)]).0, None);
    assert_eq!(closer.error, Some(TermScopeError::IndexOverflow));
}

#[test]
fn mapped_sparse_high_footprints_reuse_only_actual_indices_and_keep_one_budget() {
    fn project(
        closer: &mut Closer<'_>,
        input: &Arc<Expr>,
        pairs: &[(u32, u32)],
    ) -> Option<Arc<Expr>> {
        OutputShift {
            closer,
            delta: 0,
            renaming: Some(Arc::new(pairs.iter().copied().collect())),
            refused: false,
            cutoff: 0,
            guard_extent: 0,
            named: NamedFootprint::default(),
            memo: HashMap::new(),
        }
        .shared_arc(input)
    }
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    closer.binder_depth = 1500;
    let child = Arc::new(Expr::app(Expr::bvar(64), Expr::bvar(130)));
    let input = Arc::new(Expr::app_arc(child.clone(), child));
    let first = project(&mut closer, &input, &[(64, 65), (130, 131), (1000, 1001)]).unwrap();
    let before = closer.stats.visits;
    let repeated = project(&mut closer, &input, &[(64, 65), (130, 131), (1000, 1002)]).unwrap();
    assert!(
        Arc::ptr_eq(&first, &repeated),
        "unused high-map changes are irrelevant"
    );
    assert!(
        closer.stats.visits - before <= 4,
        "the actual two high-index probes are charged"
    );
    let changed = project(&mut closer, &input, &[(64, 65), (130, 132)]).unwrap();
    let expected_child = Expr::app(Expr::bvar(65), Expr::bvar(132));
    assert_eq!(*changed, Expr::app(expected_child.clone(), expected_child));
    assert_ne!(*changed, *first);
    // Missing a formerly observed high index cannot authorize an old output.
    assert!(project(&mut closer, &input, &[(64, 65)]).is_none());
    assert!(closer.error.is_none());
    closer.limits.max_visits = closer.stats.visits + 1;
    assert!(project(&mut closer, &input, &[(64, 65), (130, 132)]).is_none());
    assert_eq!(closer.error, Some(TermScopeError::VisitLimit));
}
