// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Named-only screens never replace dependency checks or refund charged work.

use super::*;
use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::{BinderInfo, Environment, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn wrap(
    scope: &mut TermScope,
    names: &[u64],
    ordinary: usize,
    shared: &Arc<Expr>,
    ty: Option<&Expr>,
) -> Expr {
    let shell = ty.map_or_else(
        || Expr::const_str("Nat.succ"),
        |ty| Expr::lam(BinderInfo::Default, ty.clone(), Expr::bvar(0)),
    );
    let mut result = Expr::app_arc(Arc::new(shell), shared.clone());
    for raw in names.iter().rev() {
        result = scope.lam(id(*raw), BinderInfo::Default, nat(), result);
    }
    for _ in 0..ordinary {
        result = Expr::lam(BinderInfo::Default, nat(), result);
    }
    result
}
fn child(mut term: &Expr, depth: usize) -> &Arc<Expr> {
    for _ in 0..depth {
        let ExprKind::Lam(_, _, body) = term.kind() else {
            panic!("actual output binder")
        };
        term = body;
    }
    let ExprKind::App(_, child) = term.kind() else {
        panic!("actual shared output edge")
    };
    child
}
fn reference(names: &[u64], ordinary: usize, shared: &Expr, ty: Option<&Expr>) -> Expr {
    let shell = ty.map_or_else(
        || Expr::const_str("Nat.succ"),
        |ty| Expr::lam(BinderInfo::Default, ty.clone(), Expr::bvar(0)),
    );
    let mut term = Expr::app(shell, shared.clone());
    for raw in names.iter().rev() {
        term = Expr::lam(BinderInfo::Default, nat(), term.abstract_fvar(id(*raw)));
    }
    for _ in 0..ordinary {
        term = Expr::lam(BinderInfo::Default, nat(), term);
    }
    term
}
fn check_nat_arm(term: &Expr, depth: usize, result: Expr) {
    let mut ty = result;
    for _ in 0..depth {
        ty = Expr::arrow(nat(), ty);
    }
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    let mut checker = TypeChecker::new(&env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.check_type(term, &ty).unwrap();
}
fn retained_ids(closer: &Closer<'_>) {
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
}

#[test]
fn named_only_actual_same_depth_and_named_prefix_removal_reuse_typed_child_arcs() {
    for (first_names, first_o, last_names, last_o) in
        [(vec![9, 1], 0, vec![1], 1), (vec![9, 8, 1], 0, vec![1], 0)]
    {
        let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
        let mut scope = TermScope::new();
        let first = wrap(&mut scope, &first_names, first_o, &shared, None);
        let last = wrap(&mut scope, &last_names, last_o, &shared, None);
        let input = Expr::apps(Expr::const_str("structural"), [first, last]);
        let report = scope.close_with_diagnostics(&input, TermScopeLimits::default());
        let output = report.result.unwrap();
        let arms = output.get_app_args();
        assert_eq!(*arms[0], reference(&first_names, first_o, &shared, None));
        assert_eq!(*arms[1], reference(&last_names, last_o, &shared, None));
        assert!(Arc::ptr_eq(
            child(arms[0], first_names.len() + first_o),
            child(arms[1], last_names.len() + last_o),
        ));
        check_nat_arm(arms[0], first_names.len() + first_o, nat());
        check_nat_arm(arms[1], last_names.len() + last_o, nat());
        assert!(report.diagnostics.cache.primary_named_only_attempts > 0);
        assert!(report.diagnostics.cache.named_only_contextual_hits > 0);
        eprintln!("NAMED_ONLY_KERNEL typed_child_arc stats={:?}", report.stats);
    }
}

#[test]
fn named_only_internal_ordinary_lam_pi_let_and_mdata_keep_their_exact_indices() {
    let value = Expr::fvar(id(1));
    let local = Expr::app(
        Expr::lam(BinderInfo::Default, nat(), value.clone()),
        Expr::bvar(0),
    );
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), value.clone(), Expr::bvar(0)],
    );
    let lam = Expr::lam(BinderInfo::Default, nat(), local.clone());
    let forms = [
        (lam.clone(), Expr::arrow(nat(), nat())),
        (Expr::pi(BinderInfo::Default, nat(), eq), Expr::prop()),
        (
            Expr::let_named(Name::anon(), nat(), value, local, false),
            nat(),
        ),
        (Expr::mdata(Vec::new(), lam), Expr::arrow(nat(), nat())),
    ];
    for (shared, ty) in forms {
        assert!(!shared.has_loose_bvars_quick());
        let shared = Arc::new(shared);
        let mut scope = TermScope::new();
        let first = wrap(&mut scope, &[9, 8, 1], 0, &shared, Some(&ty));
        let last = wrap(&mut scope, &[1], 0, &shared, Some(&ty));
        let output = scope
            .close(&Expr::apps(Expr::const_str("structural"), [first, last]))
            .unwrap();
        let arms = output.get_app_args();
        assert_eq!(*arms[0], reference(&[9, 8, 1], 0, &shared, Some(&ty)));
        assert_eq!(*arms[1], reference(&[1], 0, &shared, Some(&ty)));
        assert!(Arc::ptr_eq(child(arms[0], 3), child(arms[1], 1)));
        check_nat_arm(arms[0], 3, ty.clone());
        check_nat_arm(arms[1], 1, ty);
    }
}

#[test]
fn named_only_extended_binders_preserve_structural_indices_and_actual_child_arcs() {
    // These are binder/metadata controls, not kernel certification of extensions.
    let body = Arc::new(Expr::app(Expr::fvar(id(1)), Expr::bvar(0)));
    let domain = Arc::new(Expr::const_str("set"));
    let forms = [
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
    for shared in forms {
        assert!(!shared.has_loose_bvars_quick());
        let shared = Arc::new(shared);
        let mut scope = TermScope::new();
        let first = wrap(&mut scope, &[9, 8, 1], 0, &shared, None);
        let last = wrap(&mut scope, &[1], 0, &shared, None);
        let report = scope.close_with_diagnostics(
            &Expr::apps(Expr::const_str("structural"), [first, last]),
            TermScopeLimits::default(),
        );
        let output = report.result.unwrap();
        let arms = output.get_app_args();
        assert_eq!(*arms[0], reference(&[9, 8, 1], 0, &shared, None));
        assert_eq!(*arms[1], reference(&[1], 0, &shared, None));
        assert!(Arc::ptr_eq(child(arms[0], 3), child(arms[1], 1)));
        assert!(report.diagnostics.cache.named_only_contextual_hits > 0);
    }
}

#[test]
fn named_only_actual_reflexivity_proof_replays_and_rejects_a_forged_endpoint() {
    let eq = |a, b| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat(), a, b],
        )
    };
    let value = Expr::fvar(id(1));
    let ty = eq(value.clone(), value.clone());
    let shared = Arc::new(Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), value],
    ));
    let mut scope = TermScope::new();
    let first = wrap(&mut scope, &[9, 8, 1], 0, &shared, Some(&ty));
    let last = wrap(&mut scope, &[1], 0, &shared, Some(&ty));
    let report = scope.close_with_diagnostics(
        &Expr::apps(Expr::const_str("structural"), [first, last]),
        TermScopeLimits::default(),
    );
    let output = report.result.unwrap();
    let arms = output.get_app_args();
    assert!(Arc::ptr_eq(child(arms[0], 3), child(arms[1], 1)));
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    for (arm, depth) in arms.into_iter().zip([3, 1]) {
        let mut expected = Expr::pi(BinderInfo::Default, nat(), eq(Expr::bvar(0), Expr::bvar(0)));
        let mut forged = Expr::pi(
            BinderInfo::Default,
            nat(),
            eq(
                Expr::bvar(0),
                Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
            ),
        );
        for _ in 1..depth {
            expected = Expr::arrow(nat(), expected);
            forged = Expr::arrow(nat(), forged);
        }
        let mut checker = TypeChecker::new(&env);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker.check_type(arm, &expected).unwrap();
        let inferred = checker.infer_type(arm).unwrap();
        assert!(!checker.is_def_eq(&inferred, &forged));
        assert!(env.audit_certification(&expected, arm).is_certified());
        assert!(!env.audit_certification(&forged, arm).is_certified());
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(arm).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
        assert_eq!(&decoded, arm);
        assert!(env.audit_certification(&expected, &decoded).is_certified());
        assert!(!env.audit_certification(&forged, &decoded).is_certified());
    }
    eprintln!(
        "NAMED_ONLY_KERNEL strict_refl forged_rejected DAG_replayed stats={:?}",
        report.stats
    );
}

#[test]
fn named_only_zero_offset_validates_but_retains_existing_dependency_ids() {
    let shared = Arc::new(Expr::app(Expr::fvar(id(1)), Expr::fvar(id(2))));
    let mut scope = TermScope::new();
    let first = wrap(&mut scope, &[9, 1, 2], 0, &shared, None);
    let last = wrap(&mut scope, &[1, 2], 1, &shared, None);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let first_out = first.fold_opt_or_clone(&mut closer);
    assert!(closer.error.is_none());
    let address = shared.as_ref() as *const Expr as usize;
    let prior = closer.contextual.maps().0[&address].entry.dependencies();
    let before = closer.dependencies.len();
    let probes = closer.stats.context_check_visits;
    let last_out = last.fold_opt_or_clone(&mut closer);
    assert!(closer.error.is_none());
    assert!(Arc::ptr_eq(child(&first_out, 3), child(&last_out, 3)));
    assert_eq!(closer.dependencies.len(), before);
    assert_eq!(
        closer.contextual.maps().0[&address].entry.dependencies(),
        prior
    );
    assert!(closer.stats.context_check_visits > probes);
    retained_ids(&closer);
}

#[test]
fn named_only_missing_moved_underflow_and_external_ordinary_are_not_authority() {
    for case in 0..4 {
        let scope = TermScope::new();
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        closer.binder_depth = 2;
        closer.ordinary.push(0);
        if case == 1 {
            closer.active.insert(id(1), 1);
        }
        if case == 2 {
            closer.active.insert(id(1), 0);
        }
        let dependency = if case == 3 {
            // Equal to the removed depth: the metadata screen must not
            // replace the actual charged unexpected-ordinary check.
            Dependency::Ordinary(0, 1)
        } else {
            Dependency::Named(id(1), u32::from(case != 2))
        };
        let root = closer.dependency_node(dependency);
        let cached = ContextEntry {
            entry: MemoEntry {
                replacement: Some(Arc::new(Expr::bvar(0))),
                declarations: None,
                dependencies: MemoEntry::compact(Some(root)),
            },
            context: 99,
            binder_depth: 3,
            ordinary_count: 1,
        };
        assert_eq!(
            closer.relative_dependencies(&cached, RebaseMode::NamedOnly),
            None
        );
        assert!(closer.error.is_none());
        let cache = closer.diagnostic_report().cache;
        assert_eq!(
            [
                cache.named_dependency_missing,
                cache.named_dependency_moved,
                cache.named_only_depth_screen_rejections,
                cache.named_only_ordinary_rejections
            ][case],
            1
        );
        assert_eq!(cache.dependency_rebase_underflow, 0);
        assert_eq!(
            cache.named_only_depth_screen_rejections,
            usize::from(case == 2)
        );
        assert_eq!(closer.stats.context_check_visits, usize::from(case != 2));
        assert!(closer.memo.is_empty());
        retained_ids(&closer);
    }
}

#[test]
fn named_only_partial_caps_rollback_every_unpublished_suffix_and_never_alias() {
    for last_o in [0, 1] {
        let shared = Arc::new(Expr::app(Expr::fvar(id(1)), Expr::fvar(id(2))));
        let mut scope = TermScope::new();
        let first = wrap(&mut scope, &[9, 1, 2], 0, &shared, None);
        let last = wrap(&mut scope, &[1, 2], last_o, &shared, None);
        let mut complete = Closer::new(&scope, TermScopeLimits::default(), true);
        let _ = first.fold_opt_or_clone(&mut complete);
        let seed_visits = complete.stats.visits;
        let _ = last.fold_opt_or_clone(&mut complete);
        assert!(complete.error.is_none());
        let address = shared.as_ref() as *const Expr as usize;
        let mut partial = 0;
        let mut stopped = 0;
        for cap in seed_visits..=complete.stats.visits {
            let limits = TermScopeLimits {
                max_visits: cap,
                ..TermScopeLimits::default()
            };
            let mut observed = Closer::new(&scope, limits, true);
            let mut plain = Closer::new(&scope, limits, false);
            let _ = first.fold_opt_or_clone(&mut observed);
            let _ = first.fold_opt_or_clone(&mut plain);
            let checkpoint = observed.dependencies.len();
            let prior = observed.contextual.maps().0[&address].clone();
            let result = last.fold_opt_or_clone(&mut observed);
            let plain_result = last.fold_opt_or_clone(&mut plain);
            assert_eq!(result, plain_result);
            assert_eq!(observed.error, plain.error);
            assert_eq!(observed.stats, plain.stats);
            retained_ids(&observed);
            retained_ids(&plain);
            let report = observed.diagnostic_report();
            if let Some(stop) = report.first_stop {
                assert_eq!(stop.charged_visits, cap);
                if stop.phase == TermScopeStopPhase::RelativeDependency
                    && stop.candidate == Some(TermScopeCacheRoute::PrimaryNamedOnly)
                {
                    assert_eq!(observed.dependencies.len(), checkpoint);
                    assert!(!observed.memo.contains_key(&(address, stop.context)));
                    let cached = &observed.contextual.maps().0[&address];
                    assert_eq!(cached.context, prior.context);
                    assert_eq!(cached.entry.dependencies(), prior.entry.dependencies());
                    assert!(Arc::ptr_eq(
                        cached.entry.replacement.as_ref().unwrap(),
                        prior.entry.replacement.as_ref().unwrap()
                    ));
                    stopped += 1;
                    partial += usize::from(report.cache.failed_rebase_dependency_nodes > 0);
                }
            }
        }
        assert!(stopped > 0);
        if last_o == 0 {
            assert!(
                partial > 0,
                "at least one first validated leaf was rolled back"
            );
        } else {
            assert_eq!(partial, 0, "zero-offset mode appends no dependency nodes");
        }
        eprintln!(
            "NAMED_ONLY_BUDGET ordinary={last_o} full_visits={} seed_visits={} partial_suffix_stops={partial}; no refunds or parent-prefix parity claim",
            complete.stats.visits, seed_visits
        );
    }
}

#[test]
fn named_only_semantic_rejection_rolls_back_a_valid_prefix_before_budgeted_rewalk() {
    let shared = Arc::new(Expr::app(Expr::fvar(id(1)), Expr::fvar(id(2))));
    let mut scope = TermScope::new();
    let first = wrap(&mut scope, &[9, 1, 2], 0, &shared, None);
    let last = wrap(&mut scope, &[1, 8], 0, &shared, None);
    let address = shared.as_ref() as *const Expr as usize;
    let mut full = Closer::new(&scope, TermScopeLimits::default(), true);
    let _ = first.fold_opt_or_clone(&mut full);
    let seed = full.stats.visits;
    let _ = last.fold_opt_or_clone(&mut full);
    assert_eq!(full.error, Some(TermScopeError::OutOfScope(id(2))));
    let mut rejected_then_capped = 0;
    for cap in seed..=full.stats.visits {
        let mut closer = Closer::new(
            &scope,
            TermScopeLimits {
                max_visits: cap,
                ..TermScopeLimits::default()
            },
            true,
        );
        let _ = first.fold_opt_or_clone(&mut closer);
        let checkpoint = closer.dependencies.len();
        let _ = last.fold_opt_or_clone(&mut closer);
        retained_ids(&closer);
        let report = closer.diagnostic_report();
        if report.cache.failed_rebase_dependency_nodes > 0
            && report.cache.named_dependency_missing > 0
            && closer.error == Some(TermScopeError::VisitLimit)
        {
            let stop = report.first_stop.unwrap();
            assert_eq!(stop.charged_visits, cap);
            assert!(!closer.memo.contains_key(&(address, stop.context)));
            assert_eq!(closer.contextual.maps().0[&address].binder_depth, 3);
            if rejected_then_capped == 0 {
                // The same candidate now pays a uniform-index proof before
                // rewalking. Its first request stops with the old private
                // suffix discarded, and no shifted output can be published.
                assert_eq!(stop.phase, TermScopeStopPhase::RelativeDependency);
                assert_eq!(stop.candidate, Some(TermScopeCacheRoute::PrimaryNamedOnly));
                assert_eq!(report.cache.uniform_shift_attempts, 1);
                assert_eq!(report.cache.uniform_shift_output_visits, 0);
                assert_eq!(report.cache.uniform_shift_contextual_hits, 0);
                assert_eq!(closer.dependencies.len(), checkpoint);
            }
            // Later rewalks may retain independently rebuilt child entries.
            rejected_then_capped += 1;
        }
    }
    assert!(rejected_then_capped > 0);
}

#[test]
fn named_only_actual_spare_hit_reuses_typed_child_and_promotes_only_after_validation() {
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let mut scope = TermScope::new();
    let first = wrap(&mut scope, &[9, 8, 7, 1], 0, &shared, None);
    let middle = wrap(&mut scope, &[1], 0, &shared, None);
    let last = wrap(&mut scope, &[8, 1], 0, &shared, None);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let first_out = first.fold_opt_or_clone(&mut closer);
    let middle_out = middle.fold_opt_or_clone(&mut closer);
    assert!(closer.error.is_none());
    let address = shared.as_ref() as *const Expr as usize;
    let (primary, spare) = closer.contextual.maps();
    assert_eq!(
        (primary[&address].binder_depth, spare[&address].binder_depth),
        (1, 4)
    );
    assert!(closer.contextual.get(address, 2, 0).is_none());
    let (selected, route) = closer.contextual.named_only(address, 2, &shared).unwrap();
    assert_eq!(route, TermScopeCacheRoute::SpareNamedOnly);
    assert_eq!(selected.binder_depth, 4);
    // The shallow primary is ineligible, not a selected semantic rejection.
    // Selection observes one slot; only the actual fold validates/promotes it.
    assert_eq!(closer.contextual.maps().0[&address].binder_depth, 1);
    let before = closer.diagnostic_report().cache;
    let probes = closer.stats.context_check_visits;
    let last_out = last.fold_opt_or_clone(&mut closer);
    assert!(closer.error.is_none());
    let after = closer.diagnostic_report().cache;
    assert_eq!(
        after.primary_named_only_attempts,
        before.primary_named_only_attempts
    );
    assert_eq!(
        after.spare_named_only_attempts,
        before.spare_named_only_attempts + 1
    );
    assert_eq!(
        after.named_only_contextual_hits,
        before.named_only_contextual_hits + 1
    );
    assert!(closer.stats.context_check_visits > probes);
    for (arm, names) in [
        (&first_out, &[9, 8, 7, 1][..]),
        (&middle_out, &[1][..]),
        (&last_out, &[8, 1][..]),
    ] {
        assert_eq!(*arm, reference(names, 0, &shared, None));
        check_nat_arm(arm, names.len(), nat());
        assert!(Arc::ptr_eq(child(&first_out, 4), child(arm, names.len())));
    }
    let (primary, spare) = closer.contextual.maps();
    assert_eq!(
        (primary[&address].binder_depth, spare[&address].binder_depth),
        (2, 1)
    );
    retained_ids(&closer);
}

#[test]
fn named_only_one_primary_refusal_does_not_retry_a_valid_spare() {
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let mut scope = TermScope::new();
    let first = wrap(&mut scope, &[9, 8, 7, 1], 0, &shared, None);
    let middle = wrap(&mut scope, &[1, 9, 8], 0, &shared, None);
    let last = wrap(&mut scope, &[8, 1], 0, &shared, None);
    let report = scope.close_with_diagnostics(
        &Expr::apps(Expr::const_str("structural"), [first, middle, last]),
        TermScopeLimits::default(),
    );
    let output = report.result.unwrap();
    let arms = output.get_app_args();
    assert_eq!(child(arms[0], 4), child(arms[2], 2));
    // The completed inverse restores the original output directly. The original
    // spare-attempt/probe assertions below still prohibit a candidate retry.
    assert!(Arc::ptr_eq(child(arms[0], 4), child(arms[2], 2)));
    assert!(report.diagnostics.cache.primary_named_only_attempts > 0);
    assert_eq!(report.diagnostics.cache.spare_named_only_attempts, 0);
    assert!(report.diagnostics.cache.named_only_depth_screen_rejections > 0);
    assert_eq!(report.diagnostics.cache.dependency_rebase_underflow, 0);
}

#[test]
fn named_only_never_retries_original_rejection_but_now_probes_inward() {
    for old_selected in [false, true] {
        let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
        let mut scope = TermScope::new();
        let arms = if old_selected {
            let first = wrap(&mut scope, &[1], 5, &shared, None);
            let middle_body = wrap(&mut scope, &[], 3, &shared, None);
            let middle = scope.lam(id(1), BinderInfo::Default, nat(), middle_body);
            let last = wrap(&mut scope, &[1], 1, &shared, None);
            vec![first, middle, last]
        } else {
            vec![
                wrap(&mut scope, &[1], 0, &shared, None),
                wrap(&mut scope, &[9, 8, 1], 0, &shared, None),
            ]
        };
        let report = scope.close_with_diagnostics(
            &Expr::apps(Expr::const_str("structural"), arms),
            TermScopeLimits::default(),
        );
        assert!(report.result.is_ok());
        if old_selected {
            assert_eq!(report.diagnostics.cache.primary_named_only_attempts, 0);
        } else {
            assert!(report.diagnostics.cache.primary_named_only_attempts > 0);
            assert!(report.diagnostics.cache.named_only_contextual_hits > 0);
        }
        assert_eq!(report.diagnostics.cache.spare_named_only_attempts, 0);
        if old_selected {
            assert!(
                report
                    .diagnostics
                    .cache
                    .rejected_contextual_with_alternate_shape
                    > 0
            );
        }
    }
}

#[test]
fn named_only_original_loose_types_values_and_hidden_named_declarations_are_excluded() {
    let mut scope = TermScope::new();
    let fv = Expr::fvar(id(1));
    let hidden = [
        scope.lam(
            id(11),
            BinderInfo::Default,
            nat(),
            Expr::app(Expr::bvar(0), fv.clone()),
        ),
        scope.pi(
            id(12),
            BinderInfo::Default,
            nat(),
            Expr::app(Expr::bvar(0), fv.clone()),
        ),
        scope.let_named(
            id(13),
            Name::anon(),
            nat(),
            Expr::nat_lit(0u64),
            Expr::app(Expr::bvar(0), fv.clone()),
            false,
        ),
    ];
    for body in hidden {
        for input in [body.clone(), Expr::mdata(Vec::new(), body.clone())] {
            assert!(!input.has_loose_bvars_quick());
            let shared = Arc::new(input);
            let first = wrap(&mut scope, &[1, 2], 1, &shared, None);
            let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
            let _ = first.fold_opt_or_clone(&mut closer);
            assert!(closer.error.is_none());
            let address = shared.as_ref() as *const Expr as usize;
            let cached = &closer.contextual.maps().0[&address];
            assert!(cached.entry.declarations().is_some());
            assert!(closer.contextual.get(address, 1, 0).is_none());
            assert!(closer.contextual.named_only(address, 1, &shared).is_none());
        }
    }
    let mut candidates = ContextCandidates::default();
    candidates.insert(
        7,
        ContextEntry {
            entry: MemoEntry {
                replacement: None,
                declarations: None,
                dependencies: None,
            },
            context: 1,
            binder_depth: 3,
            ordinary_count: 0,
        },
    );
    let loose = [
        Expr::bvar(Expr::MAX_BVAR_INDEX),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), fv.clone()),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), fv.clone()),
        Expr::let_named(
            Name::anon(),
            Expr::bvar(0),
            Expr::nat_lit(0u64),
            fv.clone(),
            false,
        ),
        Expr::let_named(Name::anon(), nat(), Expr::bvar(0), fv, false),
        Expr::mdata(Vec::new(), Expr::bvar(0)),
    ];
    for input in loose {
        assert!(input.has_loose_bvars_quick());
        assert!(candidates.get(7, 1, 0).is_none());
        assert!(candidates.named_only(7, 1, &input).is_none());
    }
}

#[test]
fn named_only_original_max_loose_index_keeps_actual_overflow_error() {
    let shared = Arc::new(Expr::app(
        Expr::const_str("Nat.succ"),
        Expr::bvar(Expr::MAX_BVAR_INDEX),
    ));
    let mut scope = TermScope::new();
    let first = wrap(&mut scope, &[], 1, &shared, None);
    let last = wrap(&mut scope, &[1], 0, &shared, None);
    let report = scope.close_with_diagnostics(
        &Expr::apps(Expr::const_str("structural"), [first, last]),
        TermScopeLimits::default(),
    );
    assert_eq!(report.result, Err(TermScopeError::IndexOverflow));
    assert_eq!(report.diagnostics.cache.primary_named_only_attempts, 0);
    assert_eq!(report.diagnostics.cache.spare_named_only_attempts, 0);
}
