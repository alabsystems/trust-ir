// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Structural absorption is not cache authority. These exercise the production
//! union builder and charged guards; only the final ordinary proof is typed.

use super::*;
use clean_kernel::{BinderInfo, Environment, KernelTypeError, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn pair(closer: &mut Closer<'_>, ordinary: bool) -> (usize, usize, usize) {
    let left = closer.dependency_node(if ordinary {
        Dependency::Ordinary(0, 1)
    } else {
        Dependency::Named(id(1), 1)
    });
    let right = closer.dependency_node(if ordinary {
        Dependency::Ordinary(1, 2)
    } else {
        Dependency::Named(id(2), 2)
    });
    let root = closer.dependency_node(Dependency::Join(left, right));
    (left, right, root)
}

fn accounted(closer: &Closer<'_>) {
    let cache = closer.diagnostic_report().cache;
    assert_eq!(
        cache.successful_dependency_probe_visits + cache.rejected_dependency_probe_visits,
        closer.stats.context_check_visits
    );
    for (index, node) in closer.dependencies.iter().enumerate() {
        if let Dependency::Join(left, right) = node.dependency {
            assert!(left < index && right < index);
        }
    }
}

#[test]
fn immediate_child_absorption_uses_exact_values_in_either_union_order() {
    for ordinary in [false, true] {
        let scope = TermScope::new();
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let (left, right, root) = pair(&mut closer, ordinary);
        let same_left = closer.dependency_node(closer.dependencies[left].dependency);
        let same_right = closer.dependency_node(closer.dependencies[right].dependency);
        let reversed = closer.dependency_node(Dependency::Join(same_right, same_left));
        let duplicate = closer.dependency_node(Dependency::Join(same_left, same_left));
        let before = closer.dependencies.len();
        for incoming in [left, right, same_left, same_right, reversed, duplicate] {
            let checkpoint = closer.dependencies.len();
            assert_eq!(closer.union_dependencies(root, incoming), root);
            assert_eq!(closer.dependencies.len(), checkpoint);
            let output = closer.union_dependencies(incoming, root);
            if incoming == reversed {
                assert_eq!(output, reversed);
                assert_eq!(closer.dependencies.len(), checkpoint);
            } else {
                // A right-covering root must not reorder the first left read.
                assert_eq!(output, checkpoint);
                assert_eq!(closer.dependencies.len(), checkpoint + 1);
                assert!(matches!(closer.dependencies[output].dependency,
                    Dependency::Join(left, right) if left == incoming && right == root));
            }
            closer.dependency = Some(root);
            closer.include_dependency(Some(incoming));
            assert_eq!(closer.dependency, Some(root));
        }
        assert_eq!(closer.dependencies.len(), before + 5);
        assert_eq!(closer.dependencies[root].min_depth, 1);
        assert_eq!(closer.stats, TermScopeStats::default());
        accounted(&closer);
    }
}

#[test]
fn reverse_order_missing_or_moved_read_keeps_first_probe_and_all_finite_caps() {
    for missing in [false, true] {
        for constructed in [false, true] {
            for cap in 0..=3 {
                let scope = TermScope::new();
                let mut closer = Closer::new(
                    &scope,
                    TermScopeLimits {
                        max_visits: 1 + cap,
                        ..TermScopeLimits::default()
                    },
                    true,
                );
                let (left, right, root) = pair(&mut closer, false);
                let output = if constructed {
                    closer.union_dependencies(right, root)
                } else {
                    // Raw pre-absorption union is the structural order oracle.
                    closer.dependency_node(Dependency::Join(right, root))
                };
                assert!(matches!(closer.dependencies[output].dependency,
                    Dependency::Join(a, b) if a == right && b == root));
                closer.binder_depth = 4;
                closer.active.insert(id(1), 1);
                if !missing {
                    closer.active.insert(id(2), 1); // Original B depth2 moved.
                }
                assert!(closer.visit(), "charge the enclosing expression");
                assert!(!closer.same_dependencies(Some(output)));
                let needed = 2;
                assert_eq!(closer.stats.context_check_visits, cap.min(needed));
                assert_eq!(closer.stats.visits, 1 + cap.min(needed));
                assert_eq!(
                    closer.error,
                    (cap < needed).then_some(TermScopeError::VisitLimit)
                );
                // A and the right subtree are never probed before failing B.
                assert_eq!(closer.dependencies[left].last_probe, 0);
                assert_eq!(closer.dependencies[root].last_probe, 0);
                let cache = closer.diagnostic_report().cache;
                assert_eq!(
                    cache.dependency_budget_rejections,
                    usize::from(cap < needed)
                );
                assert_eq!(
                    cache.named_dependency_missing,
                    usize::from(missing && cap >= needed)
                );
                assert_eq!(
                    cache.named_dependency_moved,
                    usize::from(!missing && cap >= needed)
                );
                if cap >= needed {
                    assert_eq!(closer.dependencies[right].last_probe, 1);
                    assert!(closer.diagnostic_report().first_stop.is_none());
                }
                accounted(&closer);
            }
        }
    }
}

#[test]
fn absorption_never_conflates_distinct_names_positions_depths_or_read_kinds() {
    for ordinary in [false, true] {
        for incoming in [
            Dependency::Named(id(1), 2),
            Dependency::Named(id(2), 1),
            Dependency::Named(id(3), 1),
            Dependency::Ordinary(0, 2),
            Dependency::Ordinary(1, 1),
            Dependency::Ordinary(2, 1),
        ] {
            let scope = TermScope::new();
            let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
            let (_, _, root) = pair(&mut closer, ordinary);
            let incoming = closer.dependency_node(incoming);
            let before = closer.dependencies.len();
            let joined = closer.union_dependencies(root, incoming);
            assert_eq!(joined, before);
            assert_eq!(closer.dependencies.len(), before + 1);
            assert!(matches!(closer.dependencies[joined].dependency,
                Dependency::Join(left, right) if left == root && right == incoming));
            accounted(&closer);
        }
    }
}

#[test]
fn repeated_mixed_reads_reduce_real_exact_probe_requests_not_request_charges() {
    for ordinary in [false, true] {
        for moved in [false, true] {
            for normalized in [false, true] {
                let scope = TermScope::new();
                let repeats = 24;
                let needed = if normalized {
                    3
                } else if moved {
                    repeats + 3
                } else {
                    2 * repeats + 3
                };
                for cap in 0..=needed {
                    let mut closer = Closer::new(
                        &scope,
                        TermScopeLimits {
                            max_visits: 1 + cap,
                            ..TermScopeLimits::default()
                        },
                        true,
                    );
                    let (left, _, mut root) = pair(&mut closer, ordinary);
                    for _ in 0..repeats {
                        let next = closer.dependency_node(closer.dependencies[left].dependency);
                        root = if normalized {
                            closer.union_dependencies(root, next)
                        } else {
                            // Deliberately retain the exact pre-absorption
                            // dependency union as a structural work control.
                            closer.dependency_node(Dependency::Join(root, next))
                        };
                    }
                    closer.binder_depth = 4;
                    if ordinary {
                        closer.ordinary.extend([1, if moved { 1 } else { 2 }]);
                    } else {
                        closer
                            .active
                            .extend([(id(1), 1), (id(2), if moved { 1 } else { 2 })]);
                    }
                    assert!(closer.visit(), "charge the enclosing expression");
                    assert_eq!(
                        closer.same_dependencies(Some(root)),
                        !moved && cap == needed
                    );
                    assert_eq!(closer.stats.visits, 1 + cap);
                    assert_eq!(closer.stats.context_check_visits, cap);
                    assert_eq!(
                        closer.error,
                        (cap < needed).then_some(TermScopeError::VisitLimit)
                    );
                    let cache = closer.diagnostic_report().cache;
                    assert_eq!(
                        cache.dependency_budget_rejections,
                        usize::from(cap < needed)
                    );
                    assert_eq!(
                        cache.named_dependency_moved,
                        usize::from(!ordinary && moved && cap == needed)
                    );
                    assert_eq!(
                        cache.ordinary_dependency_moved,
                        usize::from(ordinary && moved && cap == needed)
                    );
                    accounted(&closer);
                }
            }
        }
    }
}

#[test]
fn absorbed_unions_still_validate_relative_reads_and_internal_cutoffs() {
    for ordinary in [false, true] {
        for named_only in [false, true] {
            for moved in [false, true] {
                let scope = TermScope::new();
                let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
                let (left, root) = if ordinary {
                    let left = closer.dependency_node(Dependency::Ordinary(1, 1));
                    let right = closer.dependency_node(Dependency::Ordinary(2, 2));
                    (left, closer.dependency_node(Dependency::Join(left, right)))
                } else {
                    let (left, _, root) = pair(&mut closer, false);
                    (left, root)
                };
                let same_left = closer.dependency_node(closer.dependencies[left].dependency);
                assert_eq!(closer.union_dependencies(root, same_left), root);
                closer.binder_depth = 3;
                if ordinary {
                    closer.ordinary.extend([0, if moved { 0 } else { 1 }]);
                } else {
                    closer
                        .active
                        .extend([(id(1), 0), (id(2), if moved { 0 } else { 1 })]);
                }
                let cached = ContextEntry {
                    entry: MemoEntry {
                        replacement: None,
                        declarations: None,
                        dependencies: MemoEntry::compact(Some(root)),
                    },
                    context: 99,
                    binder_depth: 4,
                    ordinary_count: closer.ordinary.len() + 1,
                };
                let before = closer.dependencies.len();
                assert!(closer.visit());
                let output = closer.relative_dependencies(
                    &cached,
                    if named_only {
                        RebaseMode::NamedOnly
                    } else {
                        RebaseMode::Ordinary
                    },
                );
                assert_eq!(output.is_some(), !moved && !(ordinary && named_only));
                assert_eq!(
                    closer.stats.context_check_visits,
                    if ordinary && named_only { 2 } else { 3 }
                );
                if let Some(Some(output)) = output {
                    assert_eq!(closer.dependencies[output].min_depth, 0);
                    assert_eq!(closer.dependencies.len(), before + 3);
                }
                assert!(closer.error.is_none());
                accounted(&closer);
            }
        }
    }

    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let external = closer.dependency_node(Dependency::Named(id(1), 0));
    let internal = closer.dependency_node(Dependency::Named(id(9), 5));
    let root = closer.dependency_node(Dependency::Join(external, internal));
    assert_eq!(closer.union_dependencies(root, external), root);
    closer.binder_depth = 5;
    closer.active.insert(id(1), 0);
    assert!(closer.visit());
    assert!(closer.same_dependencies(Some(root)));
    assert_eq!(closer.stats.context_check_visits, 3);
    assert_eq!(closer.dependencies[root].min_depth, 0);
    accounted(&closer);
}

#[test]
fn ordinary_mixed_read_proof_preserves_original_dag_and_semantic_refusal() {
    let sum = Expr::apps(
        Expr::const_str("Nat.add"),
        [
            Expr::apps(
                Expr::const_str("Nat.add"),
                [Expr::fvar(id(1)), Expr::fvar(id(2))],
            ),
            Expr::fvar(id(1)),
        ],
    );
    let eq = |left, right| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat(), left, right],
        )
    };
    let open_proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), sum.clone()],
    );
    let open_claim = eq(sum.clone(), sum.clone());
    let open_forged = eq(sum.clone(), Expr::app(Expr::const_str("Nat.succ"), sum));
    let mut scope = TermScope::new();
    let proof = scope.lam(id(2), BinderInfo::Default, nat(), open_proof.clone());
    let proof = scope.lam(id(1), BinderInfo::Default, nat(), proof);
    let claim = scope.pi(id(2), BinderInfo::Default, nat(), open_claim);
    let claim = scope.pi(id(1), BinderInfo::Default, nat(), claim);
    let forged = scope.pi(id(2), BinderInfo::Default, nat(), open_forged);
    let forged = scope.pi(id(1), BinderInfo::Default, nat(), forged);
    let oracle = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), open_proof.abstract_fvar(id(2))).abstract_fvar(id(1)),
    );
    let report = scope.close_with_diagnostics(&proof, TermScopeLimits::default());
    let actual = report.result.unwrap();
    assert_eq!(actual, oracle);
    let claim = scope.close(&claim).unwrap();
    let forged = scope.close(&forged).unwrap();
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&actual).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
    assert_eq!(decoded, actual);
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    for candidate in [&actual, &decoded] {
        let mut checker = TypeChecker::new(&env);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker.check_type(candidate, &claim).unwrap();
        assert!(!checker.heartbeat_spent());
        let audit = env.audit_certification(&claim, candidate);
        assert!(audit.is_certified(), "{audit:#?}");
        for name in &audit.dependencies {
            assert!(env.axiom_deps(name).unwrap().is_empty());
            assert!(env.trust_marker_deps(name).unwrap().is_empty());
        }
        let mut checker = TypeChecker::new(&env);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        assert!(matches!(
            checker.check_type(candidate, &forged),
            Err(KernelTypeError::TypeMismatch { .. })
        ));
        assert!(!checker.heartbeat_spent());
    }
    for cap in 0..=report.stats.visits {
        let limits = TermScopeLimits {
            max_visits: cap,
            ..TermScopeLimits::default()
        };
        let observed = scope.close_with_diagnostics(&proof, limits);
        let plain = scope.close_with_limits(&proof, limits);
        assert_eq!(
            plain.as_ref().map(|out| &out.term),
            observed.result.as_ref()
        );
        if let Ok(plain) = plain {
            assert_eq!(plain.stats, observed.stats);
            assert_eq!(plain.term, actual);
        } else {
            assert_eq!(observed.result, Err(TermScopeError::VisitLimit));
            assert_eq!(observed.stats.visits, cap);
        }
    }

    let escaped = scope.lam(id(3), BinderInfo::Default, nat(), Expr::fvar(id(1)));
    assert_eq!(
        scope.close(&escaped),
        Err(TermScopeError::OutOfScope(id(1)))
    );
    let inner = scope.lam(id(1), BinderInfo::Default, nat(), Expr::fvar(id(1)));
    let shadowed = scope.lam(id(1), BinderInfo::Default, nat(), inner);
    assert_eq!(
        scope.close(&shadowed),
        Err(TermScopeError::ShadowedLocal(id(1)))
    );
    let overflow = scope.lam(
        id(4),
        BinderInfo::Default,
        nat(),
        Expr::bvar(Expr::MAX_BVAR_INDEX),
    );
    assert_eq!(scope.close(&overflow), Err(TermScopeError::IndexOverflow));
}
