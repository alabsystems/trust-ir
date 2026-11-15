// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! A separate rejection policy, not the visit-preserving single-leaf refactor.
//! Immutable b7c18 charged the selected walk before reaching a low leaf (or
//! an earlier mismatch/budget refusal). These tests assert the new accounting;
//! they do not run a copied old closer or promise parent finite-cap parity.

use super::*;
use clean_kernel::{BinderInfo, Environment, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn add(left: Arc<Expr>, right: Arc<Expr>) -> Expr {
    Expr::app_arc(
        Arc::new(Expr::app_arc(Arc::new(Expr::const_str("Nat.add")), left)),
        right,
    )
}
fn eq(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), left, right],
    )
}
fn refl(value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), value],
    )
}
fn cached(root: Option<usize>, depth: u32, ordinary: usize) -> ContextEntry {
    ContextEntry {
        entry: MemoEntry {
            replacement: None,
            declarations: None,
            dependencies: MemoEntry::compact(root),
        },
        context: 99,
        binder_depth: depth,
        ordinary_count: ordinary,
    }
}
fn root(closer: &mut Closer<'_>, leaf: Dependency, joined: bool, old: u32) -> usize {
    let leaf = closer.dependency_node(leaf);
    if joined {
        let internal = closer.dependency_node(Dependency::Ordinary(0, old));
        closer.dependency_node(Dependency::Join(leaf, internal))
    } else {
        leaf
    }
}
fn retained(closer: &Closer<'_>) {
    let check = |entry: &MemoEntry| {
        assert!(
            entry
                .dependencies()
                .is_none_or(|i| i < closer.dependencies.len())
        );
        assert!(
            entry
                .declarations()
                .is_none_or(|i| i < closer.footprints.len())
        );
    };
    assert!(
        closer
            .dependency
            .is_none_or(|i| i < closer.dependencies.len())
    );
    for entry in closer.memo.values() {
        check(entry);
    }
    for entry in closer.named_closed.values() {
        check(&entry.entry);
    }
    let (primary, spare) = closer.contextual.maps();
    for entry in primary.values().chain(spare.values()) {
        check(&entry.entry);
    }
    for (index, node) in closer.dependencies.iter().enumerate() {
        if let Dependency::Join(left, right) = node.dependency {
            assert!(left < index && right < index);
        }
    }
    if closer.observations.is_some() {
        let cache = closer.diagnostic_report().cache;
        assert_eq!(
            cache.successful_dependency_probe_visits + cache.rejected_dependency_probe_visits,
            closer.stats.context_check_visits
        );
        assert_eq!(
            cache.successful_declaration_probe_visits + cache.rejected_declaration_probe_visits,
            closer.stats.scope_check_visits
        );
    }
}
fn spine(scope: &mut TermScope, frames: &[Frame], body: Expr) -> (Expr, Expr) {
    let mut actual = body.clone();
    let mut expected = body;
    for frame in frames.iter().rev() {
        match *frame {
            Frame::Named(local) => {
                actual = scope.lam(local, BinderInfo::Default, nat(), actual);
                // Independent kernel abstraction, not dependency metadata.
                expected = Expr::lam(BinderInfo::Default, nat(), expected.abstract_fvar(local));
            }
            Frame::Ordinary => {
                actual = Expr::lam(BinderInfo::Default, nat(), actual);
                expected = Expr::lam(BinderInfo::Default, nat(), expected);
            }
        }
    }
    (actual, expected)
}
fn arm(scope: &mut TermScope, frames: &[Frame], shared: &Arc<Expr>) -> (Expr, Expr) {
    spine(
        scope,
        frames,
        Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone()),
    )
}
fn proof_arm(
    scope: &mut TermScope,
    frames: &[Frame],
    shared: &Arc<Expr>,
    value: &Expr,
) -> (Expr, Expr) {
    let shell = Expr::lam(
        BinderInfo::Default,
        eq(value.clone(), value.clone()),
        Expr::bvar(0),
    );
    spine(
        scope,
        frames,
        Expr::app_arc(Arc::new(shell), shared.clone()),
    )
}
fn child(mut term: &Expr, depth: usize) -> &Arc<Expr> {
    for _ in 0..depth {
        let ExprKind::Lam(_, _, body) = term.kind() else {
            panic!("actual binder spine")
        };
        term = body;
    }
    let ExprKind::App(_, child) = term.kind() else {
        panic!("actual shared edge")
    };
    child
}
fn check_proof(arm: &Expr, count: usize, value: Expr) {
    let mut goal = eq(value.clone(), value.clone());
    let mut forged = eq(value.clone(), Expr::app(Expr::const_str("Nat.succ"), value));
    for _ in 0..count {
        goal = Expr::pi(BinderInfo::Default, nat(), goal);
        forged = Expr::pi(BinderInfo::Default, nat(), forged);
    }
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    let mut checker = TypeChecker::new(&env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.check_type(arm, &goal).unwrap();
    let inferred = checker.infer_type(arm).unwrap();
    assert!(!checker.is_def_eq(&inferred, &forged));
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(arm).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
    assert_eq!(&decoded, arm);
    assert_eq!(
        trust_ir::proof::encode_clean_expr_dag_v2(&decoded).unwrap(),
        bytes
    );
    assert!(env.audit_certification(&goal, &decoded).is_certified());
    assert!(!env.audit_certification(&forged, &decoded).is_certified());
}
fn low_frames() -> [Frame; 4] {
    [
        Frame::Named(id(2)),
        Frame::Ordinary,
        Frame::Ordinary,
        Frame::Named(id(1)),
    ]
}
fn last_frames() -> [Frame; 2] {
    [Frame::Named(id(2)), Frame::Named(id(1))]
}

#[test]
fn low_leaf_and_join_rejections_use_only_the_selected_mode_counter() {
    for ordinary in [false, true] {
        for named_leaf in [false, true] {
            for joined in [false, true] {
                let scope = TermScope::new();
                let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
                closer.binder_depth = 2;
                let dependency = if named_leaf {
                    Dependency::Named(id(1), 0)
                } else {
                    Dependency::Ordinary(0, 0)
                };
                let root = root(&mut closer, dependency, joined, 3);
                let mut entry = cached(Some(root), 3, usize::from(ordinary));
                if ordinary {
                    // Ordinary never acquired the NamedOnly declaration-free
                    // admission restriction; the later declaration guard stays.
                    let declaration = closer.declarations(Declarations::Local(id(9)));
                    entry.entry.declarations = MemoEntry::compact(Some(declaration));
                }
                let before = closer.stats;
                let nodes = closer.dependencies.len();
                let mode = if ordinary {
                    RebaseMode::Ordinary
                } else {
                    RebaseMode::NamedOnly
                };
                assert_eq!(closer.relative_dependencies(&entry, mode), None);
                assert_eq!(closer.stats, before);
                assert_eq!(closer.dependencies.len(), nodes);
                assert!(closer.error.is_none());
                let report = closer.diagnostic_report();
                assert!(report.first_stop.is_none());
                let cache = report.cache;
                assert_eq!(
                    cache.ordinary_depth_screen_rejections,
                    usize::from(ordinary)
                );
                assert_eq!(
                    cache.named_only_depth_screen_rejections,
                    usize::from(!ordinary)
                );
                assert_eq!(cache.dependency_rebase_underflow, 0);
                assert_eq!(cache.named_only_ordinary_rejections, 0);
                assert_eq!(cache.dependency_budget_rejections, 0);
                assert_eq!(cache.failed_rebase_dependency_nodes, 0);
                // The old leaf rule cannot succeed: Named depth subtraction
                // fails; Ordinary position/depth subtraction cannot both pass.
                assert!(
                    closer.dependencies[root]
                        .min_depth
                        .checked_sub(entry.binder_depth - closer.binder_depth)
                        .is_none()
                );
                retained(&closer);
            }
        }
    }
}

#[test]
fn shape_no_root_internal_and_old_cutoff_guards_precede_or_survive_the_screen() {
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    closer.binder_depth = 2;
    closer.ordinary.push(0);
    let low = closer.dependency_node(Dependency::Named(id(1), 0));
    for (old, count) in [(1, 0), (3, 0), (4, 2)] {
        assert_eq!(
            closer.relative_dependencies(&cached(Some(low), old, count), RebaseMode::Ordinary),
            None
        );
    }
    assert_eq!(closer.stats.visits, 0);
    assert_eq!(
        closer.diagnostic_report().cache.dependency_shape_rejections,
        3
    );
    assert_eq!(
        closer
            .diagnostic_report()
            .cache
            .ordinary_depth_screen_rejections,
        0
    );
    let declaration = closer.declarations(Declarations::Local(id(9)));
    let mut no_root = cached(None, 3, 2);
    no_root.entry.declarations = MemoEntry::compact(Some(declaration));
    assert_eq!(
        closer.relative_dependencies(&no_root, RebaseMode::Ordinary),
        Some(None)
    );
    assert_eq!(closer.stats.visits, 0);
    // NamedOnly still rejects this declaration shape before even no-root.
    assert_eq!(
        closer.relative_dependencies(&no_root, RebaseMode::NamedOnly),
        None
    );
    assert_eq!(
        closer.diagnostic_report().cache.dependency_shape_rejections,
        4
    );
    for dependency in [
        Dependency::Named(id(9), 3),
        Dependency::Ordinary(usize::MAX, 3),
    ] {
        let root = closer.dependency_node(dependency);
        let before = closer.stats.context_check_visits;
        assert_eq!(
            closer.relative_dependencies(&cached(Some(root), 3, 2), RebaseMode::Ordinary),
            Some(None)
        );
        assert_eq!(closer.stats.context_check_visits, before + 1);
    }
    // This external depth is >=newD but <oldD. It must not be pruned at newD.
    let external = closer.dependency_node(Dependency::Named(id(1), 2));
    let internal = closer.dependency_node(Dependency::Ordinary(usize::MAX, 3));
    let mixed = closer.dependency_node(Dependency::Join(external, internal));
    closer.active.insert(id(1), 1);
    let before = closer.stats.context_check_visits;
    let surviving = closer
        .relative_dependencies(&cached(Some(mixed), 3, 2), RebaseMode::Ordinary)
        .unwrap()
        .unwrap();
    assert!(
        matches!(closer.dependencies[surviving].dependency, Dependency::Named(local, 1) if local == id(1))
    );
    assert_eq!(closer.stats.context_check_visits, before + 3);
    closer.active.remove(&id(1));
    let before = closer.stats.context_check_visits;
    assert_eq!(
        closer.relative_dependencies(&cached(Some(mixed), 3, 2), RebaseMode::Ordinary),
        None
    );
    assert_eq!(closer.stats.context_check_visits, before + 2);
    assert_eq!(closer.diagnostic_report().cache.named_dependency_missing, 1);
    assert_eq!(
        closer
            .diagnostic_report()
            .cache
            .ordinary_depth_screen_rejections,
        0
    );
    retained(&closer);
}

#[test]
fn equality_zero_offset_and_private_arithmetic_extremes_keep_charges_and_new_ids() {
    // The MAX tuples are private arithmetic controls, not live giant contexts.
    // Existing production MAX_BVAR_INDEX/IndexOverflow tests remain unchanged.
    for (old, new, depth) in [
        (3, 2, 1),
        (2, 2, 0),
        (Expr::MAX_BVAR_INDEX + 1, 1, Expr::MAX_BVAR_INDEX),
        (u32::MAX, 1, u32::MAX - 1),
    ] {
        for named in [false, true] {
            let scope = TermScope::new();
            let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
            closer.binder_depth = new;
            let removed = usize::try_from(old - new).unwrap();
            let (dependency, count) = if named {
                closer.active.insert(id(1), 0);
                (Dependency::Named(id(1), depth), removed)
            } else {
                closer.ordinary.push(0);
                (Dependency::Ordinary(removed, depth), removed + 1)
            };
            let root = closer.dependency_node(dependency);
            let mut entry = cached(Some(root), old, count);
            let declaration = closer.declarations(Declarations::Local(id(9)));
            entry.entry.declarations = MemoEntry::compact(Some(declaration));
            let nodes = closer.dependencies.len();
            let result = closer
                .relative_dependencies(&entry, RebaseMode::Ordinary)
                .unwrap()
                .unwrap();
            assert_ne!(
                result, root,
                "Ordinary delta0 still appends a validated leaf"
            );
            assert_eq!(closer.dependencies.len(), nodes + 1);
            assert!(match closer.dependencies[result].dependency {
                Dependency::Named(local, 0) => named && local == id(1),
                Dependency::Ordinary(0, 0) => !named,
                _ => false,
            });
            assert_eq!(closer.stats.context_check_visits, 1);
            assert_eq!(closer.stats.visits, 1);
            let cache = closer.diagnostic_report().cache;
            assert_eq!(cache.ordinary_depth_screen_rejections, 0);
            assert_eq!(cache.named_only_depth_screen_rejections, 0);
            assert_eq!(cache.dependency_shape_rejections, 0);
            retained(&closer);
        }
    }
}

#[test]
fn actual_long_low_right_diamond_rejects_with_zero_probes_or_private_suffix() {
    let mut prefix = Arc::new(Expr::fvar(id(1)));
    for _ in 0..20 {
        // A real internal ordinary read keeps a distinct composite footprint.
        // It is pruned at the old subtree cutoff during an outward rebase;
        // the high named prefix remains valid before the low right leaf.
        let summand = Expr::app(
            Expr::lam(
                BinderInfo::Default,
                nat(),
                add(Arc::new(Expr::fvar(id(1))), Arc::new(Expr::bvar(0))),
            ),
            Expr::nat_lit(0_u64),
        );
        prefix = Arc::new(add(prefix, Arc::new(summand)));
    }
    let shared = Arc::new(add(
        prefix.clone(),
        Arc::new(add(prefix, Arc::new(Expr::fvar(id(2))))),
    ));
    let mut scope = TermScope::new();
    let (first, _) = arm(&mut scope, &low_frames(), &shared);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let _ = first.fold_opt_or_clone(&mut closer);
    assert!(closer.error.is_none());
    let address = shared.as_ref() as *const Expr as usize;
    let entry = closer.contextual.maps().0[&address].clone();
    let root = entry.entry.dependencies().unwrap();
    assert_eq!((entry.binder_depth, entry.ordinary_count), (4, 2));
    assert_eq!(closer.dependencies[root].min_depth, 0);
    assert!(closer.dependencies.len() > 40);
    assert!(
        closer
            .dependencies
            .iter()
            .any(|node| matches!(node.dependency,
        Dependency::Join(left, right) if matches!(closer.dependencies[right].dependency,
            Dependency::Join(shared_left, _) if left == shared_left))),
        "actual dependency diamond"
    );
    closer.binder_depth = 2;
    closer.active.extend([(id(2), 0), (id(1), 1)]);
    let selected = closer.contextual.get(address, 2, 0).unwrap();
    assert_eq!(selected.entry.dependencies(), Some(root));
    let before = closer.stats;
    let nodes = closer.dependencies.len();
    assert_eq!(
        closer.relative_dependencies(&entry, RebaseMode::Ordinary),
        None
    );
    assert_eq!(closer.stats, before);
    assert_eq!(closer.dependencies.len(), nodes);
    assert!(closer.error.is_none());
    let cache = closer.diagnostic_report().cache;
    assert_eq!(cache.ordinary_depth_screen_rejections, 1);
    assert_eq!(cache.named_only_depth_screen_rejections, 0);
    assert_eq!(cache.dependency_rebase_underflow, 0);
    assert_eq!(cache.failed_rebase_dependency_nodes, 0);
    assert!(closer.diagnostic_report().first_stop.is_none());
    // b7c18's left-first Join walk would charge/append this valid x prefix
    // before reaching the low y depth. We do not execute that parent walker.
    assert!(closer.dependencies.iter().any(|node| matches!(node.dependency,
        Dependency::Named(local, depth) if local == id(1) && depth.checked_sub(entry.binder_depth - closer.binder_depth) == Some(1))));
    assert!(
        closer.dependencies[root]
            .min_depth
            .checked_sub(entry.binder_depth - closer.binder_depth)
            .is_none()
    );
    retained(&closer);
}

#[test]
fn low_right_witness_can_replace_an_earlier_missing_or_moved_reason_without_budget_error() {
    for moved in [false, true] {
        for cap in [0, 3] {
            let scope = TermScope::new();
            let mut closer = Closer::new(
                &scope,
                TermScopeLimits {
                    max_visits: cap,
                    ..TermScopeLimits::default()
                },
                true,
            );
            closer.binder_depth = 2;
            if moved {
                closer.active.insert(id(9), 0);
            }
            let left = closer.dependency_node(Dependency::Named(id(9), 3));
            let right = closer.dependency_node(Dependency::Named(id(2), 0));
            let root = closer.dependency_node(Dependency::Join(left, right));
            let nodes = closer.dependencies.len();
            assert_eq!(
                closer.relative_dependencies(&cached(Some(root), 4, 2), RebaseMode::Ordinary),
                None
            );
            assert_eq!(closer.stats.visits, 0);
            assert_eq!(closer.stats.context_check_visits, 0);
            assert_eq!(closer.dependencies.len(), nodes);
            assert!(closer.error.is_none());
            let cache = closer.diagnostic_report().cache;
            assert_eq!(cache.ordinary_depth_screen_rejections, 1);
            assert_eq!(cache.named_dependency_missing, 0);
            assert_eq!(cache.named_dependency_moved, 0);
            assert_eq!(cache.dependency_rebase_underflow, 0);
            assert_eq!(cache.dependency_budget_rejections, 0);
            assert!(closer.diagnostic_report().first_stop.is_none());
            retained(&closer);
        }
    }
}

#[test]
fn charged_position_underflow_at_equality_remains_distinct_from_free_depth_screen() {
    for low_depth in [false, true] {
        for joined in [false, true] {
            for cap in 0..=3 {
                let scope = TermScope::new();
                let mut closer = Closer::new(
                    &scope,
                    TermScopeLimits {
                        max_visits: cap,
                        ..TermScopeLimits::default()
                    },
                    true,
                );
                closer.binder_depth = 2;
                closer.ordinary.push(0);
                let depth = u32::from(!low_depth);
                let position = usize::from(low_depth);
                let root = root(
                    &mut closer,
                    Dependency::Ordinary(position, depth),
                    joined,
                    3,
                );
                let nodes = closer.dependencies.len();
                assert_eq!(
                    closer.relative_dependencies(&cached(Some(root), 3, 2), RebaseMode::Ordinary),
                    None
                );
                let needed = if joined { 2 } else { 1 };
                let budget = !low_depth && cap < needed;
                assert_eq!(closer.error, budget.then_some(TermScopeError::VisitLimit));
                assert_eq!(
                    closer.stats.context_check_visits,
                    if low_depth { 0 } else { cap.min(needed) }
                );
                assert_eq!(closer.stats.visits, closer.stats.context_check_visits);
                assert_eq!(closer.dependencies.len(), nodes);
                let cache = closer.diagnostic_report().cache;
                assert_eq!(
                    cache.ordinary_depth_screen_rejections,
                    usize::from(low_depth)
                );
                assert_eq!(
                    cache.dependency_rebase_underflow,
                    usize::from(!low_depth && !budget)
                );
                assert_eq!(cache.dependency_budget_rejections, usize::from(budget));
                if budget {
                    let stop = closer.diagnostic_report().first_stop.unwrap();
                    assert_eq!(stop.phase, TermScopeStopPhase::RelativeDependency);
                    assert_eq!(stop.charged_visits, cap);
                } else {
                    assert!(closer.diagnostic_report().first_stop.is_none());
                }
                retained(&closer);
            }
        }
    }
    let scope = TermScope::new();
    let mut closer = Closer::new(
        &scope,
        TermScopeLimits {
            max_visits: 1,
            ..TermScopeLimits::default()
        },
        true,
    );
    closer.binder_depth = 2;
    let root = closer.dependency_node(Dependency::Named(id(1), 0));
    assert!(closer.visit());
    assert_eq!(
        closer.relative_dependencies(&cached(Some(root), 3, 1), RebaseMode::Ordinary),
        None
    );
    assert_eq!(
        closer.stats.visits, 1,
        "a precharged request is never refunded"
    );
    assert!(closer.error.is_none());
    retained(&closer);
}

#[test]
fn actual_typed_low_primary_rebuilds_and_never_retries_a_genuinely_valid_spare() {
    for with_spare in [false, true] {
        let value = add(Arc::new(Expr::fvar(id(2))), Arc::new(Expr::fvar(id(1))));
        let shared = Arc::new(refl(value.clone()));
        let mut scope = TermScope::new();
        let spare_frames = [
            Frame::Ordinary,
            Frame::Ordinary,
            Frame::Ordinary,
            Frame::Ordinary,
            Frame::Named(id(2)),
            Frame::Named(id(1)),
        ];
        let (first, first_expected) = proof_arm(&mut scope, &spare_frames, &shared, &value);
        let (middle, middle_expected) = proof_arm(&mut scope, &low_frames(), &shared, &value);
        let (last, last_expected) = proof_arm(&mut scope, &last_frames(), &shared, &value);
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let first_out = with_spare.then(|| first.fold_opt_or_clone(&mut closer));
        let middle_out = middle.fold_opt_or_clone(&mut closer);
        assert!(closer.error.is_none());
        assert_eq!(middle_out, middle_expected);
        let address = shared.as_ref() as *const Expr as usize;
        let (primary, spare) = closer.contextual.maps();
        let root = primary[&address].entry.dependencies().unwrap();
        assert_eq!(
            (
                primary[&address].binder_depth,
                primary[&address].ordinary_count
            ),
            (4, 2)
        );
        assert_eq!(closer.dependencies[root].min_depth, 0);
        assert!(std::ptr::eq(
            closer.contextual.get(address, 2, 0).unwrap(),
            &primary[&address]
        ));
        if with_spare {
            let spare = &spare[&address];
            assert_eq!((spare.binder_depth, spare.ordinary_count), (6, 4));
            assert_eq!(
                closer.dependencies[spare.entry.dependencies().unwrap()].min_depth,
                4
            );
            let Dependency::Join(left, right) =
                closer.dependencies[spare.entry.dependencies().unwrap()].dependency
            else {
                panic!("actual spare retains both named reads")
            };
            for (index, local, expected) in [(left, id(2), 0), (right, id(1), 1)] {
                assert!(matches!(closer.dependencies[index].dependency,
                    Dependency::Named(actual, depth) if actual == local && depth.checked_sub(spare.binder_depth - 2) == Some(expected)));
            }
        }
        let before = closer.diagnostic_report().cache;
        let last_out = last.fold_opt_or_clone(&mut closer);
        assert!(closer.error.is_none());
        assert_eq!(last_out, last_expected);
        assert_ne!(child(&middle_out, 4), child(&last_out, 2));
        assert!(!Arc::ptr_eq(child(&middle_out, 4), child(&last_out, 2)));
        let after = closer.diagnostic_report().cache;
        assert!(after.primary_outward_attempts > before.primary_outward_attempts);
        assert!(after.ordinary_depth_screen_rejections > before.ordinary_depth_screen_rejections);
        assert_eq!(after.spare_outward_attempts, before.spare_outward_attempts);
        assert_eq!(
            after.primary_named_only_attempts,
            before.primary_named_only_attempts
        );
        assert_eq!(
            after.spare_named_only_attempts,
            before.spare_named_only_attempts
        );
        if let Some(first_out) = first_out {
            assert_eq!(first_out, first_expected);
            assert_eq!(child(&first_out, 6), child(&last_out, 2));
            // Independent rebuilds now share completed output nodes. The original
            // spare-attempt/probe assertions below still prohibit a candidate retry.
            assert!(Arc::ptr_eq(child(&first_out, 6), child(&last_out, 2)));
            assert!(after.output_node_intern_hits > before.output_node_intern_hits);
            assert!(
                after.rejected_contextual_with_alternate_shape
                    > before.rejected_contextual_with_alternate_shape
            );
            check_proof(
                &first_out,
                6,
                add(Arc::new(Expr::bvar(1)), Arc::new(Expr::bvar(0))),
            );
        }
        check_proof(
            &middle_out,
            4,
            add(Arc::new(Expr::bvar(3)), Arc::new(Expr::bvar(0))),
        );
        check_proof(
            &last_out,
            2,
            add(Arc::new(Expr::bvar(1)), Arc::new(Expr::bvar(0))),
        );
        retained(&closer);
    }
}

#[test]
fn actual_equality_with_loose_input_keeps_strict_proof_arc_and_all_charged_checks() {
    let value = add(Arc::new(Expr::bvar(0)), Arc::new(Expr::fvar(id(1))));
    let shared = Arc::new(refl(value.clone()));
    assert!(
        shared.has_loose_bvars_quick(),
        "Ordinary requires no no-loose screen"
    );
    let mut scope = TermScope::new();
    let old_frames = [
        Frame::Ordinary,
        Frame::Ordinary,
        Frame::Ordinary,
        Frame::Named(id(1)),
    ];
    let new_frames = [Frame::Ordinary, Frame::Named(id(1))];
    let (first, first_expected) = proof_arm(&mut scope, &old_frames, &shared, &value);
    let (last, last_expected) = proof_arm(&mut scope, &new_frames, &shared, &value);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let first_out = first.fold_opt_or_clone(&mut closer);
    let address = shared.as_ref() as *const Expr as usize;
    let entry = closer.contextual.maps().0[&address].clone();
    assert_eq!((entry.binder_depth, entry.ordinary_count), (4, 3));
    let root = entry.entry.dependencies().unwrap();
    assert!(matches!(
        closer.dependencies[root].dependency,
        Dependency::Join(_, _)
    ));
    assert_eq!(closer.dependencies[root].min_depth, 2);
    assert!(
        closer
            .dependencies
            .iter()
            .any(|node| matches!(node.dependency, Dependency::Ordinary(2, 2)))
    );
    let before = closer.diagnostic_report().cache;
    let last_out = last.fold_opt_or_clone(&mut closer);
    assert!(closer.error.is_none());
    assert_eq!(first_out, first_expected);
    assert_eq!(last_out, last_expected);
    assert!(Arc::ptr_eq(child(&first_out, 4), child(&last_out, 2)));
    let after = closer.diagnostic_report().cache;
    assert!(after.primary_outward_attempts > before.primary_outward_attempts);
    assert!(after.contextual_hits > before.contextual_hits);
    assert!(
        after.successful_dependency_probe_visits >= before.successful_dependency_probe_visits + 3
    );
    assert_eq!(after.ordinary_depth_screen_rejections, 0);
    assert_eq!(after.primary_named_only_attempts, 0);
    assert_eq!(after.spare_named_only_attempts, 0);
    for (output, depth) in [(&first_out, 4), (&last_out, 2)] {
        check_proof(
            output,
            depth,
            add(Arc::new(Expr::bvar(1)), Arc::new(Expr::bvar(0))),
        );
    }
    retained(&closer);
}

#[test]
fn every_new_policy_cap_keeps_observed_plain_public_parity_and_owned_arena_ids() {
    let shared = Arc::new(add(
        Arc::new(Expr::fvar(id(2))),
        Arc::new(Expr::fvar(id(1))),
    ));
    let mut scope = TermScope::new();
    let (first, first_expected) = arm(&mut scope, &low_frames(), &shared);
    let (last, last_expected) = arm(&mut scope, &last_frames(), &shared);
    let input = Expr::apps(Expr::const_str("structural"), [first.clone(), last.clone()]);
    let full = scope.close_with_diagnostics(&input, TermScopeLimits::default());
    assert_eq!(
        full.result,
        Ok(Expr::apps(
            Expr::const_str("structural"),
            [first_expected, last_expected]
        ))
    );
    assert!(full.diagnostics.cache.ordinary_depth_screen_rejections > 0);
    for cap in 0..=full.stats.visits {
        let limits = TermScopeLimits {
            max_visits: cap,
            ..TermScopeLimits::default()
        };
        let mut observed = Closer::new(&scope, limits, true);
        let mut plain = Closer::new(&scope, limits, false);
        let actual = input.fold_opt_or_clone(&mut observed);
        let expected = input.fold_opt_or_clone(&mut plain);
        assert_eq!(actual, expected);
        assert_eq!(observed.error, plain.error);
        assert_eq!(observed.stats, plain.stats);
        assert_eq!(observed.stats.visits, cap);
        assert_eq!(
            observed.error,
            (cap < full.stats.visits).then_some(TermScopeError::VisitLimit)
        );
        assert!(plain.observations.is_none());
        assert_eq!(
            plain.diagnostic_report().cache,
            TermScopeCacheDiagnostics::default()
        );
        retained(&observed);
        retained(&plain);
        let public = scope.close_with_diagnostics(&input, limits);
        assert_eq!(public.stats, observed.stats);
        assert_eq!(
            public.result,
            observed.error.clone().map_or(Ok(actual), Err)
        );
        let legacy = scope.close_with_limits(&input, limits);
        assert_eq!(
            legacy.as_ref().map(|out| out.stats),
            public.result.as_ref().map(|_| public.stats)
        );
        assert_eq!(legacy.map(|out| out.term), public.result);
    }
    let mut complete = Closer::new(&scope, TermScopeLimits::default(), true);
    let _ = first.fold_opt_or_clone(&mut complete);
    let warm = complete.stats.visits;
    let _ = last.fold_opt_or_clone(&mut complete);
    let address = shared.as_ref() as *const Expr as usize;
    let mut earliest = false;
    for cap in warm..complete.stats.visits {
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let _ = first.fold_opt_or_clone(&mut closer);
        let nodes = closer.dependencies.len();
        let old = closer.contextual.maps().0[&address].clone();
        let before = closer
            .diagnostic_report()
            .cache
            .ordinary_depth_screen_rejections;
        closer.limits.max_visits = cap;
        let _ = last.fold_opt_or_clone(&mut closer);
        retained(&closer);
        let report = closer.diagnostic_report();
        if !earliest && report.cache.ordinary_depth_screen_rejections > before {
            assert_eq!(closer.error, Some(TermScopeError::VisitLimit));
            assert_eq!(closer.dependencies.len(), nodes);
            let retained = &closer.contextual.maps().0[&address];
            assert_eq!(retained.entry.dependencies, old.entry.dependencies);
            assert_eq!(retained.binder_depth, 4);
            let stop = report.first_stop.unwrap();
            assert_eq!(stop.phase, TermScopeStopPhase::Expression);
            assert!(!closer.memo.contains_key(&(address, stop.context)));
            earliest = true;
        }
        // Later rewalks may legitimately publish rebuilt child dependencies;
        // ownership/backward edges, not equality to the warm length, hold then.
    }
    assert!(earliest);
}

#[test]
fn last_remaining_fvar_request_can_now_report_scope_error_instead_of_old_probe_budget() {
    let shared = Arc::new(Expr::fvar(id(2)));
    let mut scope = TermScope::new();
    let old_frames = [Frame::Named(id(2)), Frame::Ordinary, Frame::Ordinary];
    let (first, _) = arm(&mut scope, &old_frames, &shared);
    let (last, _) = arm(&mut scope, &[Frame::Named(id(1))], &shared);
    let input = Expr::apps(Expr::const_str("structural"), [first, last]);
    let full = scope.close_with_diagnostics(&input, TermScopeLimits::default());
    assert_eq!(full.result, Err(TermScopeError::OutOfScope(id(2))));
    assert!(full.diagnostics.cache.ordinary_depth_screen_rejections > 0);
    assert_eq!(full.diagnostics.cache.dependency_rebase_underflow, 0);
    assert_eq!(full.diagnostics.cache.dependency_budget_rejections, 0);
    let last_charge = full.stats.visits;
    for cap in 0..=last_charge {
        let limits = TermScopeLimits {
            max_visits: cap,
            ..TermScopeLimits::default()
        };
        let report = scope.close_with_diagnostics(&input, limits);
        let plain = scope.close_with_limits(&input, limits);
        assert_eq!(plain.map(|out| out.term), report.result);
        assert_eq!(report.stats.visits, cap);
        assert_eq!(
            report.result,
            Err(if cap == last_charge {
                TermScopeError::OutOfScope(id(2))
            } else {
                TermScopeError::VisitLimit
            })
        );
        let stop = report.diagnostics.first_stop.unwrap();
        assert_eq!(stop.charged_visits, cap);
        if cap == last_charge {
            assert_eq!(stop.phase, TermScopeStopPhase::Expression);
            assert!(stop.candidate.is_none());
            assert!(report.diagnostics.cache.ordinary_depth_screen_rejections > 0);
            assert_eq!(report.diagnostics.cache.dependency_budget_rejections, 0);
            // The old guard would need another charged probe at this cap.
            // The new zero-probe refusal does not set an error or refund this
            // final expression request; the real registered FVar now refuses.
        }
    }
}
