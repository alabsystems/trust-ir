// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Structural oracles are not proof authority; typed controls use strict Clean.

use super::*;
use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::{BinderInfo, Environment, KernelTypeError, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn eq(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), left, right],
    )
}
fn wrap(scope: &mut TermScope, names: &[u64], shared: &Arc<Expr>) -> Expr {
    let mut term = Expr::app_arc(
        Arc::new(Expr::lam(
            BinderInfo::Default,
            eq(Expr::fvar(id(1)), Expr::fvar(id(1))),
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
        Expr::lam(
            BinderInfo::Default,
            eq(Expr::fvar(id(1)), Expr::fvar(id(1))),
            Expr::bvar(0),
        ),
        shared.clone(),
    );
    for raw in names.iter().rev() {
        term = Expr::lam(BinderInfo::Default, nat(), term.abstract_fvar(id(*raw)));
    }
    term
}
fn goal(names: &[u64], wrong: bool) -> Expr {
    let local = Expr::fvar(id(1));
    let rhs = if wrong {
        Expr::app(Expr::const_str("Nat.succ"), local.clone())
    } else {
        local.clone()
    };
    let mut result = eq(local, rhs);
    for raw in names.iter().rev() {
        result = Expr::pi(BinderInfo::Default, nat(), result.abstract_fvar(id(*raw)));
    }
    result
}
fn assert_retained(closer: &Closer<'_>) {
    let valid = |entry: &MemoEntry| {
        assert!(
            entry
                .dependencies()
                .is_none_or(|index| index < closer.dependencies.len())
        );
        assert!(
            entry
                .declarations()
                .is_none_or(|index| index < closer.footprints.len())
        );
    };
    for entry in closer.memo.values() {
        valid(entry);
    }
    for entry in closer.named_closed.values() {
        valid(&entry.entry);
    }
    let (primary, spare) = closer.contextual.maps();
    for entry in primary.values().chain(spare.values()) {
        valid(&entry.entry);
    }
    assert!(spare.len() <= primary.len());
    for (index, node) in closer.dependencies.iter().enumerate() {
        if let Dependency::Join(left, right) = node.dependency {
            assert!(left < index && right < index);
        }
    }
    let cache = closer.diagnostic_report().cache;
    if closer.observations.is_some() {
        assert_eq!(
            cache.successful_dependency_probe_visits + cache.rejected_dependency_probe_visits,
            closer.stats.context_check_visits
        );
    } else {
        assert_eq!(cache, TermScopeCacheDiagnostics::default());
    }
}

#[test]
fn uniform_positive_and_negative_deltas_keep_exact_old_oracle_and_strict_proofs() {
    let shared = Arc::new(Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), Expr::fvar(id(1))],
    ));
    // A FIXED outer local changes its actual output index, unlike the existing
    // exact-relative route. Both signs must be observed, not inferred eligible.
    for names in [[vec![1, 2], vec![1, 2, 3]], [vec![1, 2, 3], vec![1, 2]]] {
        let mut scope = TermScope::new();
        let arms = names
            .iter()
            .map(|names| wrap(&mut scope, names, &shared))
            .collect::<Vec<_>>();
        let input = Expr::apps(Expr::const_str("structural"), arms);
        let report = scope.close_with_diagnostics(&input, TermScopeLimits::default());
        let closed = report.result.unwrap();
        assert!(report.diagnostics.cache.uniform_shift_contextual_hits > 0);
        assert!(report.diagnostics.cache.uniform_shift_output_visits > 0);
        assert!(report.diagnostics.cache.uniform_shift_dependency_visits > 0);
        let mut env = Environment::new();
        env.init_eq().unwrap();
        env.init_nat().unwrap();
        for (arm, names) in closed.get_app_args().iter().zip(&names) {
            assert_eq!(**arm, reference(names, &shared));
            let mut checker = TypeChecker::new(&env);
            checker.set_heartbeat_limit(2_000_000);
            checker.set_allow_unsafe(false);
            checker.set_allow_partial(false);
            checker.check_type(arm, &goal(names, false)).unwrap();
            assert!(!checker.heartbeat_spent());
            let mut mutant = TypeChecker::new(&env);
            mutant.set_heartbeat_limit(2_000_000);
            mutant.set_allow_unsafe(false);
            mutant.set_allow_partial(false);
            assert!(matches!(
                mutant.check_type(arm, &goal(names, true)),
                Err(KernelTypeError::TypeMismatch { .. })
            ));
            assert!(!mutant.heartbeat_spent());
            assert!(
                env.audit_certification(&goal(names, false), arm)
                    .is_certified()
            );
            assert!(
                !env.audit_certification(&goal(names, true), arm)
                    .is_certified()
            );
            let bytes = trust_ir::proof::encode_clean_expr_dag_v2(arm).unwrap();
            let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
            assert_eq!(&decoded, *arm);
            assert_eq!(
                trust_ir::proof::encode_clean_expr_dag_v2(&decoded).unwrap(),
                bytes
            );
            let mut checker = TypeChecker::new(&env);
            checker.set_heartbeat_limit(2_000_000);
            checker.set_allow_unsafe(false);
            checker.set_allow_partial(false);
            checker.check_type(&decoded, &goal(names, false)).unwrap();
            assert!(!checker.heartbeat_spent());
            let mut mutant = TypeChecker::new(&env);
            mutant.set_heartbeat_limit(2_000_000);
            mutant.set_allow_unsafe(false);
            mutant.set_allow_partial(false);
            assert!(matches!(
                mutant.check_type(&decoded, &goal(names, true)),
                Err(KernelTypeError::TypeMismatch { .. })
            ));
            assert!(!mutant.heartbeat_spent());
            assert!(
                !env.audit_certification(&goal(names, true), &decoded)
                    .is_certified()
            );
        }
    }
}

fn candidate(
    closer: &mut Closer<'_>,
    depth: u32,
    reads: &[(u64, u32)],
    output: Expr,
) -> ContextEntry {
    let mut root = None;
    for (raw, depth) in reads {
        let leaf = closer.dependency_node(Dependency::Named(id(*raw), *depth));
        root = Some(root.map_or(leaf, |old| closer.union_dependencies(old, leaf)));
    }
    ContextEntry {
        entry: MemoEntry {
            replacement: Some(Arc::new(output)),
            declarations: None,
            dependencies: MemoEntry::compact(root),
        },
        context: 1,
        binder_depth: depth,
        ordinary_count: 0,
    }
}

#[test]
fn all_live_external_named_reads_must_have_one_delta_and_original_screens_stay_load_bearing() {
    let scope = TermScope::new();
    let input = Expr::app(Expr::fvar(id(1)), Expr::fvar(id(2)));
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    closer.binder_depth = 4;
    closer.active.extend([(id(1), 0), (id(2), 1)]);
    let cached = candidate(
        &mut closer,
        3,
        &[(1, 0), (2, 1)],
        Expr::app(Expr::bvar(2), Expr::bvar(1)),
    );
    let accepted = closer.uniform_named_output(&cached, &input).unwrap();
    assert_eq!(
        *accepted.replacement.unwrap(),
        Expr::app(Expr::bvar(3), Expr::bvar(2))
    );
    assert!(closer.memo.is_empty() && closer.contextual.maps().0.is_empty());
    let checkpoint = closer.dependencies.len();
    closer.active.insert(id(2), 2);
    assert!(closer.uniform_named_output(&cached, &input).is_none());
    closer.dependencies.truncate(checkpoint); // same private-attempt rollback as caller
    assert_eq!(closer.error, None);
    closer.active.remove(&id(2));
    assert!(closer.uniform_named_output(&cached, &input).is_none());
    closer.dependencies.truncate(checkpoint);
    closer.active.insert(id(2), 1);
    let visits = closer.stats.visits;
    assert!(
        closer
            .uniform_named_output(&cached, &Expr::app(input.clone(), Expr::bvar(0)))
            .is_none()
    );
    let mut declared = cached.clone();
    declared.entry.declarations =
        MemoEntry::compact(Some(closer.declarations(Declarations::Local(id(7)))));
    assert!(closer.uniform_named_output(&declared, &input).is_none());
    assert_eq!(closer.stats.visits, visits);
    let mut ordinary = cached.clone();
    let leaf = closer.dependency_node(Dependency::Ordinary(0, 0));
    ordinary.entry.dependencies = MemoEntry::compact(Some(leaf));
    assert!(closer.uniform_named_output(&ordinary, &input).is_none());
    assert_eq!(closer.error, None);
    assert_retained(&closer);
}

fn shift(closer: &mut Closer<'_>, expression: &Expr, delta: i64) -> Option<Arc<Expr>> {
    OutputShift {
        closer,
        delta,
        renaming: None,
        refused: false,
        cutoff: 0,
        guard_extent: 0,
        named: NamedFootprint::default(),
        memo: HashMap::new(),
    }
    .shared(expression)
}

#[test]
fn exhaustive_binder_hooks_shift_types_values_and_external_reads_but_not_internal_reads() {
    let scope = TermScope::new();
    let body = Arc::new(Expr::app(Expr::bvar(0), Expr::bvar(1)));
    let domain = Arc::new(Expr::bvar(0));
    let expressions = [
        Expr::lam_arc(BinderInfo::StrictImplicit, domain.clone(), body.clone()),
        Expr::pi_arc(BinderInfo::Implicit, domain.clone(), body.clone()),
        Expr::let_named_arc(
            Name::from_string("retained"),
            domain.clone(),
            domain.clone(),
            body.clone(),
            true,
        ),
        Expr::from_kind(ExprKind::CubicalPathLam { body: body.clone() }),
        Expr::from_kind(ExprKind::ZFCComprehension {
            domain: domain.clone(),
            pred: body.clone(),
        }),
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
            set: domain.clone(),
            pred: body.clone(),
        })),
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
            set: domain,
            func: body,
        })),
    ];
    for original in expressions {
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        closer.binder_depth = 2;
        let lifted = shift(&mut closer, &original, 1).unwrap();
        assert_eq!(*lifted, original.lift(1)); // existing exhaustive independent structural oracle
        let lowered = shift(&mut closer, &lifted, -1).unwrap();
        assert_eq!(*lowered, original);
        assert_eq!(closer.error, None);
    }
    let outer = Arc::new(Expr::fvar(id(999)));
    let shared = Arc::new(Expr::app_arc(outer.clone(), Arc::new(Expr::bvar(0))));
    let input = Expr::app_arc(shared.clone(), shared);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let output = shift(&mut closer, &input, 1).unwrap();
    let ExprKind::App(left, right) = output.kind() else {
        panic!("App")
    };
    assert!(Arc::ptr_eq(left, right));
    let ExprKind::App(retained, _) = left.kind() else {
        panic!("App")
    };
    assert!(Arc::ptr_eq(retained, &outer));
    let cache = closer.diagnostic_report().cache;
    assert!(cache.uniform_shift_output_memo_hits > 0);
    assert_eq!(cache.uniform_shift_output_visits, closer.stats.visits);
    assert!(cache.uniform_shift_output_changed_nodes > 0);

    // One live node appears outside and inside an ordinary binder. Address-only
    // memoization would capture: cutoff is part of the key.
    let child = Arc::new(Expr::app(Expr::bvar(0), Expr::bvar(1)));
    let input = Expr::app_arc(
        child.clone(),
        Arc::new(Expr::lam_arc(BinderInfo::Default, Arc::new(nat()), child)),
    );
    let output = shift(&mut closer, &input, 1).unwrap();
    let ExprKind::App(left, right) = output.kind() else {
        panic!("App")
    };
    assert_eq!(**left, Expr::app(Expr::bvar(1), Expr::bvar(2)));
    let ExprKind::Lam(_, _, body) = right.kind() else {
        panic!("Lam")
    };
    assert_eq!(**body, Expr::app(Expr::bvar(0), Expr::bvar(2)));
    assert_eq!(closer.error, None);
}

#[test]
fn overflow_underflow_capture_depth_and_zero_visit_caps_never_publish_partial_outputs() {
    let scope = TermScope::new();
    for (input, delta) in [
        (Expr::bvar(Expr::MAX_BVAR_INDEX), 1),
        (Expr::bvar(0), -1),
        (Expr::lam(BinderInfo::Default, nat(), Expr::bvar(1)), -1),
    ] {
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        assert!(shift(&mut closer, &input, delta).is_none());
        assert_eq!(closer.error, Some(TermScopeError::IndexOverflow));
        assert!(closer.memo.is_empty() && closer.contextual.maps().0.is_empty());
    }
    for (limits, error) in [
        (
            TermScopeLimits {
                max_visits: 0,
                max_depth: 10,
            },
            TermScopeError::VisitLimit,
        ),
        (
            TermScopeLimits {
                max_visits: 100,
                max_depth: 0,
            },
            TermScopeError::DepthLimit,
        ),
    ] {
        let mut closer = Closer::new(&scope, limits, true);
        assert!(shift(&mut closer, &Expr::bvar(0), 1).is_none());
        assert_eq!(closer.error, Some(error));
        assert!(closer.stats.visits <= limits.max_visits);
        assert_eq!(
            closer.diagnostic_report().first_stop.unwrap().phase,
            TermScopeStopPhase::UniformIndexShiftOutput
        );
    }
}

fn uniform_leaf_fixture(closer: &mut Closer<'_>, joined: bool, delta: i64) -> ContextEntry {
    closer.binder_depth = u32::try_from(3 + delta).unwrap();
    closer.active.insert(id(1), 0);
    let mut cached = candidate(
        closer,
        3,
        &[(1, 0)],
        Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(2)),
    );
    if joined {
        let leaf = cached.entry.dependencies().unwrap();
        let internal = closer.dependency_node(Dependency::Ordinary(0, 3));
        let root = closer.dependency_node(Dependency::Join(leaf, internal));
        cached.entry.dependencies = MemoEntry::compact(Some(root));
    }
    cached
}

#[test]
fn uniform_single_leaf_and_join_keep_both_signs_zero_offset_and_every_cap_observed_plain_parity() {
    let scope = TermScope::new();
    let input = Expr::fvar(id(1));
    for delta in [-1, 0, 1] {
        for joined in [false, true] {
            let proof_visits = if joined { 3 } else { 1 };
            let output_visits = if delta == 0 { 0 } else { 3 };
            let required = proof_visits + output_visits;
            for cap in 0..=required {
                let limits = TermScopeLimits {
                    max_visits: cap,
                    ..TermScopeLimits::default()
                };
                let mut observed = Closer::new(&scope, limits, true);
                let mut plain = Closer::new(&scope, limits, false);
                let cached = uniform_leaf_fixture(&mut observed, joined, delta);
                let plain_cached = uniform_leaf_fixture(&mut plain, joined, delta);
                let actual = observed.uniform_named_output(&cached, &input);
                let expected = plain.uniform_named_output(&plain_cached, &input);
                assert_eq!(actual.is_some(), expected.is_some());
                assert_eq!(
                    actual
                        .as_ref()
                        .and_then(|entry| entry.replacement.as_deref()),
                    expected
                        .as_ref()
                        .and_then(|entry| entry.replacement.as_deref())
                );
                assert_eq!(
                    actual.as_ref().and_then(MemoEntry::dependencies),
                    expected.as_ref().and_then(MemoEntry::dependencies)
                );
                assert_eq!(observed.error, plain.error);
                assert_eq!(observed.stats, plain.stats);
                assert_eq!(observed.stats.visits, cap);
                assert!(plain.observations.is_none());
                assert_eq!(
                    plain.diagnostic_report().cache,
                    TermScopeCacheDiagnostics::default()
                );
                if cap < required {
                    assert!(actual.is_none());
                    assert_eq!(observed.error, Some(TermScopeError::VisitLimit));
                    let phase = if cap < proof_visits {
                        TermScopeStopPhase::RelativeDependency
                    } else {
                        TermScopeStopPhase::UniformIndexShiftOutput
                    };
                    assert_eq!(
                        observed.diagnostic_report().first_stop.unwrap().phase,
                        phase
                    );
                } else {
                    let actual = actual.unwrap();
                    assert_eq!(observed.error, None);
                    assert_eq!(
                        **actual.replacement.as_ref().unwrap(),
                        Expr::app(
                            Expr::const_str("Nat.succ"),
                            Expr::bvar(u32::try_from(2 + delta).unwrap())
                        )
                    );
                    if delta == 0 {
                        assert!(Arc::ptr_eq(
                            actual.replacement.as_ref().unwrap(),
                            cached.entry.replacement.as_ref().unwrap()
                        ));
                    }
                    let cache = observed.diagnostic_report().cache;
                    assert_eq!(cache.uniform_shift_dependency_visits, proof_visits);
                    assert_eq!(cache.uniform_shift_output_visits, output_visits);
                    assert_eq!(cache.uniform_shift_attempts, 1);
                    assert_eq!(cache.uniform_shift_refusals, 0);
                    assert_eq!(cache.uniform_shift_contextual_hits, 0); // only caller publishes
                }
                assert_retained(&observed);
                assert_retained(&plain);
                assert!(observed.memo.is_empty() && observed.contextual.maps().0.is_empty());
            }
        }
    }
}

#[test]
fn uniform_single_leaf_and_join_never_refund_the_original_failed_probe_or_private_suffix() {
    let scope = TermScope::new();
    let input = Expr::fvar(id(1));
    for joined in [false, true] {
        let old_visits = if joined { 2 } else { 1 };
        let new_visits = if joined { 6 } else { 4 };
        for remaining in 0..=new_visits {
            let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
            let cached = uniform_leaf_fixture(&mut closer, joined, 1);
            let checkpoint = closer.dependencies.len();
            assert!(
                closer
                    .relative_dependencies(&cached, RebaseMode::NamedOnly)
                    .is_none()
            );
            assert_eq!(closer.error, None);
            assert_eq!(closer.stats.visits, old_visits);
            closer.dependencies.truncate(checkpoint); // original caller's checkpoint, no refund
            closer.limits.max_visits = old_visits + remaining;
            let shifted = closer.uniform_named_output(&cached, &input);
            assert_eq!(closer.stats.visits, old_visits + remaining);
            if remaining < new_visits {
                assert!(shifted.is_none());
                assert_eq!(closer.error, Some(TermScopeError::VisitLimit));
                closer.dependencies.truncate(checkpoint); // same caller-owned refusal rollback
                assert_eq!(closer.dependencies.len(), checkpoint);
            } else {
                assert!(shifted.is_some());
                assert_eq!(closer.error, None);
                assert_eq!(
                    closer.stats.context_check_visits,
                    old_visits + if joined { 3 } else { 1 }
                );
            }
            assert_retained(&closer);
            assert!(closer.memo.is_empty() && closer.contextual.maps().0.is_empty());
        }
    }
}

#[test]
fn every_finite_refusal_prefix_keeps_arena_handles_valid_and_never_refunds_charged_work() {
    let shared = Arc::new(Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), Expr::fvar(id(1))],
    ));
    let mut scope = TermScope::new();
    let arms = [
        wrap(&mut scope, &[1, 2], &shared),
        wrap(&mut scope, &[1, 2, 3], &shared),
    ];
    let input = Expr::apps(Expr::const_str("structural"), arms);
    let complete = scope.close_with_diagnostics(&input, TermScopeLimits::default());
    assert!(complete.result.is_ok());
    let required = complete.stats.visits;
    assert!(complete.diagnostics.cache.uniform_shift_contextual_hits > 0);
    for cap in 0..=required {
        let limits = TermScopeLimits {
            max_visits: cap,
            ..TermScopeLimits::default()
        };
        let mut closer = Closer::new(&scope, limits, true);
        let output = closer.fold_shared(&input);
        assert_retained(&closer);
        assert!(closer.stats.visits <= cap);
        if cap < required {
            assert_eq!(closer.error, Some(TermScopeError::VisitLimit));
            assert_eq!(closer.stats.visits, cap);
            let address = &input as *const Expr as usize;
            assert!(!closer.memo.contains_key(&(address, 0)));
            assert!(!closer.contextual.maps().0.contains_key(&address));
            // The public API returns ONLY error even if the private visitor
            // has assembled part of a refused root.
            assert_eq!(
                scope.close_with_diagnostics(&input, limits).result,
                Err(TermScopeError::VisitLimit)
            );
            let _ = output;
        } else {
            assert_eq!(closer.error, None);
            assert_eq!(
                output.as_deref().unwrap_or(&input),
                complete.result.as_ref().unwrap()
            );
        }
    }
}

#[test]
fn missing_shadowed_and_own_binder_type_or_value_scope_errors_are_not_erased() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let first = wrap(&mut scope, &[1, 2], &shared);
    let missing = wrap(&mut scope, &[7, 8, 9], &shared);
    assert_eq!(
        scope.close(&Expr::apps(Expr::const_str("structural"), [first, missing])),
        Err(TermScopeError::OutOfScope(id(1)))
    );
    let shared = Arc::new(scope.lam(id(7), BinderInfo::Default, nat(), Expr::fvar(id(1))));
    let first = wrap(&mut scope, &[1, 2], &shared);
    let shadowed = wrap(&mut scope, &[1, 7, 3], &shared);
    assert_eq!(
        scope.close(&Expr::apps(
            Expr::const_str("structural"),
            [first, shadowed]
        )),
        Err(TermScopeError::ShadowedLocal(id(7)))
    );
    for type_read in [false, true] {
        let mut scope = TermScope::new();
        let ty = if type_read { Expr::fvar(id(11)) } else { nat() };
        let value = if type_read {
            Expr::nat_lit(0u64)
        } else {
            Expr::fvar(id(11))
        };
        let input = scope.let_named(
            id(11),
            Name::from_string("original"),
            ty,
            value,
            Expr::fvar(id(11)),
            false,
        );
        assert_eq!(scope.close(&input), Err(TermScopeError::OutOfScope(id(11))));
    }
}

#[test]
fn shared_output_translation_charges_dag_edges_without_unfolding_the_tree() {
    let scope = TermScope::new();
    for levels in [1usize, 32, 256] {
        let mut input = Arc::new(Expr::bvar(0));
        for _ in 0..levels {
            input = Arc::new(Expr::app_arc(input.clone(), input));
        }
        // The unfolded tree has exponentially many occurrences; the retained
        // DAG has levels + 1 nodes and exactly 2 * levels child edges.
        let required = 2 * levels + 1;
        let limits = TermScopeLimits {
            max_visits: required,
            ..TermScopeLimits::default()
        };
        let mut closer = Closer::new(&scope, limits, true);
        let (output, retained) = {
            let mut visitor = OutputShift {
                closer: &mut closer,
                delta: 1,
                renaming: None,
                refused: false,
                cutoff: 0,
                guard_extent: 0,
                named: NamedFootprint::default(),
                memo: HashMap::new(),
            };
            let output = visitor.shared(&input).unwrap();
            (output, visitor.memo.len())
        };
        assert_eq!(closer.error, None);
        assert_eq!(closer.stats.visits, required);
        assert_eq!(retained, levels + 1);
        let cache = closer.diagnostic_report().cache;
        assert_eq!(cache.uniform_shift_output_visits, required);
        assert_eq!(cache.uniform_shift_output_changed_nodes, levels + 1);
        assert_eq!(cache.uniform_shift_output_memo_hits, levels);
        assert!(closer.memo.is_empty());
        assert!(closer.contextual.maps().0.is_empty());
        let mut child = &output;
        for _ in 0..levels {
            let ExprKind::App(left, right) = child.kind() else {
                panic!("retained output DAG level")
            };
            assert!(Arc::ptr_eq(left, right));
            child = left;
        }
        assert_eq!(child.as_ref(), &Expr::bvar(1));
        let mut refused = Closer::new(
            &scope,
            TermScopeLimits {
                max_visits: required - 1,
                ..limits
            },
            true,
        );
        assert!(shift(&mut refused, &input, 1).is_none());
        assert_eq!(refused.error, Some(TermScopeError::VisitLimit));
        assert_eq!(refused.stats.visits, required - 1);
        assert!(refused.memo.is_empty());
        assert!(refused.contextual.maps().0.is_empty());
        eprintln!(
            "uniform-output-dag: levels={levels}, charged={required}, retained={retained}; structural control, not runtime/RSS or proof authority"
        );
    }
}

#[test]
fn completed_output_projection_reuses_owned_allocation_with_exact_shift_coordinates() {
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let input = Arc::new(Expr::app(Expr::bvar(0), Expr::bvar(1)));
    let shift = |closer: &mut Closer<'_>, input: &Arc<Expr>, delta, cutoff| {
        OutputShift {
            closer,
            delta,
            renaming: None,
            refused: false,
            cutoff,
            guard_extent: 0,
            named: NamedFootprint::default(),
            memo: HashMap::new(),
        }
        .shared_arc(input)
        .unwrap()
    };
    let first = shift(&mut closer, &input, 1, 0);
    assert_eq!(*first, Expr::app(Expr::bvar(1), Expr::bvar(2)));
    let visits = closer.stats.visits;
    let repeated = shift(&mut closer, &input, 1, 0);
    assert!(Arc::ptr_eq(&first, &repeated));
    assert_eq!(closer.stats.visits - visits, 1, "the root hit is charged");
    assert_eq!(
        *shift(&mut closer, &input, 2, 0),
        Expr::app(Expr::bvar(2), Expr::bvar(3))
    );
    assert_eq!(
        *shift(&mut closer, &input, 1, 1),
        Expr::app(Expr::bvar(0), Expr::bvar(2))
    );
    assert!(
        closer.shifted_outputs.len() <= closer.stats.visits,
        "every retained projection follows a charged completed request"
    );
    // Hash/structure equality alone is not a hit. The actual live allocation
    // is the key, and retaining it prevents a later address from impersonating it.
    let fresh = Arc::new(Expr::app(Expr::bvar(0), Expr::bvar(1)));
    let visits = closer.stats.visits;
    let separate = shift(&mut closer, &fresh, 1, 0);
    assert_eq!(*separate, *first);
    assert!(closer.stats.visits - visits > 1);
    let weak = Arc::downgrade(&fresh);
    drop(fresh);
    assert!(
        weak.upgrade().is_some(),
        "the exact input owner remains live"
    );
    assert_retained(&closer);
}

#[test]
fn completed_output_projection_does_not_bypass_parent_depth_or_request_caps() {
    let scope = TermScope::new();
    let input = Arc::new(Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(2)),
    ));
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    assert!(
        OutputShift {
            closer: &mut closer,
            delta: 1,
            renaming: None,
            refused: false,
            cutoff: 0,
            guard_extent: 0,
            named: NamedFootprint::default(),
            memo: HashMap::new()
        }
        .shared_arc(&input)
        .is_some()
    );
    closer.limits.max_visits = closer.stats.visits;
    assert!(
        OutputShift {
            closer: &mut closer,
            delta: 1,
            renaming: None,
            refused: false,
            cutoff: 0,
            guard_extent: 0,
            named: NamedFootprint::default(),
            memo: HashMap::new()
        }
        .shared_arc(&input)
        .is_none()
    );
    assert_eq!(closer.error, Some(TermScopeError::VisitLimit));

    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    assert!(
        OutputShift {
            closer: &mut closer,
            delta: 1,
            renaming: None,
            refused: false,
            cutoff: 0,
            guard_extent: 0,
            named: NamedFootprint::default(),
            memo: HashMap::new()
        }
        .shared_arc(&input)
        .is_some()
    );
    closer.binder_depth = Expr::MAX_BVAR_INDEX;
    assert!(
        OutputShift {
            closer: &mut closer,
            delta: 1,
            renaming: None,
            refused: false,
            cutoff: 0,
            guard_extent: 0,
            named: NamedFootprint::default(),
            memo: HashMap::new()
        }
        .shared_arc(&input)
        .is_none()
    );
    assert_eq!(closer.error, Some(TermScopeError::IndexOverflow));
    assert_retained(&closer);
}

#[test]
fn uniform_composition_preserves_cutoffs_sibling_deltas_and_overflow_guards() {
    fn shift(
        closer: &mut Closer<'_>,
        input: &Arc<Expr>,
        delta: i64,
        cutoff: u32,
    ) -> Option<Arc<Expr>> {
        OutputShift {
            closer,
            delta,
            renaming: None,
            refused: false,
            cutoff,
            guard_extent: 0,
            named: NamedFootprint::default(),
            memo: HashMap::new(),
        }
        .shared_arc(input)
    }
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let base = Arc::new(Expr::app(Expr::bvar(0), Expr::bvar(1)));
    let direct = shift(&mut closer, &base, 3, 0).unwrap();
    let first = shift(&mut closer, &base, 1, 0).unwrap();
    let visits = closer.stats.visits;
    let composed = shift(&mut closer, &first, 2, 0).unwrap();
    assert!(Arc::ptr_eq(&direct, &composed));
    assert_eq!(closer.stats.visits - visits, 1);
    assert!(
        closer
            .diagnostic_report()
            .cache
            .uniform_shift_composed_cache_hits
            > 0
    );

    let second = shift(&mut closer, &base, 2, 0).unwrap();
    let siblings = Arc::new(Expr::app_arc(first, second));
    assert_eq!(
        *shift(&mut closer, &siblings, 1, 0).unwrap(),
        Expr::app(
            Expr::app(Expr::bvar(2), Expr::bvar(3)),
            Expr::app(Expr::bvar(3), Expr::bvar(4))
        )
    );

    let base = Arc::new(Expr::app(Expr::bvar(0), Expr::bvar(2)));
    let moved = shift(&mut closer, &base, 2, 0).unwrap();
    assert_eq!(
        *shift(&mut closer, &moved, -1, 1).unwrap(),
        Expr::app(Expr::bvar(1), Expr::bvar(3))
    );

    let nested = Arc::new(Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(2)),
    ));
    let moved = shift(&mut closer, &nested, 1, 0).unwrap();
    assert!(shift(&mut closer, &moved, -1, 0).is_some());
    closer.binder_depth = Expr::MAX_BVAR_INDEX;
    assert!(shift(&mut closer, &moved, -1, 0).is_none());
    assert_eq!(closer.error, Some(TermScopeError::IndexOverflow));
}

#[test]
fn composed_output_guard_extent_reuses_safe_parents_and_inherits_cached_children() {
    fn shift(closer: &mut Closer<'_>, input: &Arc<Expr>) -> Option<Arc<Expr>> {
        OutputShift {
            closer,
            delta: 1,
            renaming: None,
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
    let child = Arc::new(Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(2)),
    ));
    let first = shift(&mut closer, &child).unwrap();
    closer.binder_depth = 17;
    let before = closer.stats.visits;
    assert!(Arc::ptr_eq(&first, &shift(&mut closer, &child).unwrap()));
    assert_eq!(closer.stats.visits - before, 1);
    let parent = Arc::new(Expr::app_arc(child, Arc::new(Expr::bvar(0))));
    assert!(shift(&mut closer, &parent).is_some());
    closer.binder_depth = Expr::MAX_BVAR_INDEX;
    assert!(shift(&mut closer, &parent).is_none());
    assert_eq!(closer.error, Some(TermScopeError::IndexOverflow));
}

#[test]
fn completed_inverse_shift_reuses_original_without_rewalking_shared_output() {
    fn shift(closer: &mut Closer<'_>, input: &Arc<Expr>, delta: i64) -> Option<Arc<Expr>> {
        OutputShift {
            closer,
            delta,
            renaming: None,
            refused: false,
            cutoff: 0,
            guard_extent: 0,
            named: NamedFootprint::default(),
            memo: HashMap::new(),
        }
        .shared_arc(input)
    }
    let scope = TermScope::new();
    for levels in [1, 32, 256] {
        let mut input = Arc::new(Expr::bvar(0));
        for _ in 0..levels {
            input = Arc::new(Expr::app_arc(input.clone(), input));
        }
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let moved = shift(&mut closer, &input, 7).unwrap();
        let before = closer.stats.visits;
        let restored = shift(&mut closer, &moved, -7).unwrap();
        assert_eq!(restored, input);
        assert_eq!(closer.stats.visits - before, 1, "levels={levels}");
        assert!(Arc::ptr_eq(&restored, &input));
        assert_retained(&closer);
    }
}

#[test]
fn inverse_shift_keeps_cutoff_mapping_and_charged_request_guards() {
    fn visitor<'a, 'scope>(
        closer: &'a mut Closer<'scope>,
        delta: i64,
        cutoff: u32,
    ) -> OutputShift<'a, 'scope> {
        OutputShift {
            closer,
            delta,
            cutoff,
            renaming: None,
            refused: false,
            guard_extent: 0,
            named: NamedFootprint::default(),
            memo: HashMap::new(),
        }
    }
    let scope = TermScope::new();
    let input = Arc::new(Expr::app(Expr::bvar(0), Expr::bvar(0)));
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let moved = visitor(&mut closer, 1, 0).shared_arc(&input).unwrap();
    let before = closer
        .diagnostic_report()
        .cache
        .uniform_shift_composed_cache_hits;
    let mut mapped = visitor(&mut closer, -1, 0);
    mapped.renaming = Some(Arc::new([(1, 4)].into_iter().collect()));
    assert_eq!(
        mapped.shared_arc(&moved).unwrap().as_ref(),
        &Expr::app(Expr::bvar(4), Expr::bvar(4))
    );
    assert_eq!(
        closer
            .diagnostic_report()
            .cache
            .uniform_shift_composed_cache_hits,
        before
    );
    // A different cutoff would capture the translated index; no origin reuse.
    assert!(visitor(&mut closer, -1, 1).shared_arc(&moved).is_none());
    assert_eq!(closer.error, Some(TermScopeError::IndexOverflow));
    for depth in [false, true] {
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let moved = visitor(&mut closer, 1, 0).shared_arc(&input).unwrap();
        if depth {
            closer.walk_depth = closer.limits.max_depth;
        } else {
            closer.limits.max_visits = closer.stats.visits;
        }
        assert!(visitor(&mut closer, -1, 0).shared_arc(&moved).is_none());
        assert_eq!(
            closer.error,
            Some(if depth {
                TermScopeError::DepthLimit
            } else {
                TermScopeError::VisitLimit
            })
        );
    }
}
