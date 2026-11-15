// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Ordinary-context removal preserves exact syntax and scope, not proof credit.

use super::*;
use clean_kernel::{BinderInfo, Environment, KernelTypeError, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn ordinary(body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, nat(), body)
}

fn successors(mut node: Arc<Expr>, count: usize) -> Arc<Expr> {
    for _ in 0..count {
        node = Arc::new(Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), node));
    }
    node
}

fn arm(scope: &mut TermScope, shared: &Arc<Expr>, ordinary_count: usize) -> Expr {
    let body = Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
    let mut arm = Expr::app(
        scope.lam(id(1), BinderInfo::Default, nat(), body),
        Expr::nat_lit(0u64),
    );
    for _ in 0..ordinary_count {
        arm = Expr::app(ordinary(arm), Expr::nat_lit(0u64));
    }
    arm
}

fn oracle_arm(shared: &Expr, ordinary_count: usize) -> Expr {
    let mut arm = Expr::app(
        ordinary(Expr::app(Expr::const_str("Nat.succ"), shared.clone())),
        Expr::nat_lit(0u64),
    );
    for _ in 0..ordinary_count {
        arm = Expr::app(ordinary(arm), Expr::nat_lit(0u64));
    }
    arm
}

fn child(mut arm: &Expr, ordinary_count: usize) -> &Arc<Expr> {
    for _ in 0..=ordinary_count {
        let ExprKind::App(function, _) = arm.kind() else {
            panic!("expected actual lambda application")
        };
        let ExprKind::Lam(_, _, body) = function.kind() else {
            panic!("expected retained lambda")
        };
        arm = body;
    }
    let ExprKind::App(_, child) = arm.kind() else {
        panic!("expected actual shared successor child")
    };
    child
}

fn kernel_nat(term: &Expr) {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let mut checker = TypeChecker::new(&env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(2_000_000);
    checker.check_type(term, &nat()).unwrap();
    assert!(!checker.heartbeat_spent());
}

#[test]
fn outward_ordinary_prefixes_share_exact_typed_open_output() {
    let mut scope = TermScope::new();
    // This internal ordinary binder contributes a dependency that must not
    // become an external assumption when the surrounding prefix is removed.
    let inner = Expr::app(
        ordinary(Expr::apps(
            Expr::const_str("Nat.add"),
            [Expr::bvar(0), Expr::fvar(id(1))],
        )),
        Expr::nat_lit(0u64),
    );
    let shared = successors(Arc::new(inner), 64);
    let oracle = shared.abstract_fvar(id(1));
    let mut open = Expr::nat_lit(0u64);
    let mut expected = open.clone();
    for ordinary_count in 1..=8 {
        open = Expr::apps(
            Expr::const_str("Nat.add"),
            [arm(&mut scope, &shared, ordinary_count), open],
        );
        expected = Expr::apps(
            Expr::const_str("Nat.add"),
            [oracle_arm(&oracle, ordinary_count), expected],
        );
    }
    // Prepending arms visits the deepest first, then removes one ordinary
    // prefix at a time; the independent oracle never uses the candidate cache.
    kernel_nat(&expected);
    let report = scope.close_with_diagnostics(&open, TermScopeLimits::default());
    let closed = report.result.unwrap();
    assert_eq!(closed, expected);
    kernel_nat(&closed);
    let mut cursor = &closed;
    let mut retained = None;
    for ordinary_count in (1..=8).rev() {
        let ExprKind::App(function, tail) = cursor.kind() else {
            panic!("sum")
        };
        let ExprKind::App(_, arm) = function.kind() else {
            panic!("sum argument")
        };
        let shared = child(arm, ordinary_count);
        if let Some(previous) = &retained {
            assert!(Arc::ptr_eq(previous, shared));
        } else {
            retained = Some(shared.clone());
        }
        cursor = tail;
    }
    assert!(report.stats.transformed_nodes < 500, "{:?}", report.stats);
    assert!(report.stats.context_check_visits > 0);
}

#[test]
fn outward_cache_rebases_external_ordinary_positions_and_keeps_loose_bvars() {
    let scope = TermScope::new();
    let shared = successors(
        Arc::new(Expr::apps(
            Expr::const_str("Nat.add"),
            [Expr::bvar(0), Expr::bvar(9)],
        )),
        32,
    );
    let wrap = |count: usize| {
        let mut term = Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
        for _ in 0..count {
            term = ordinary(term);
        }
        term
    };
    let deeper = wrap(4);
    let shallower = wrap(2);
    let open = Expr::app(deeper.clone(), shallower.clone());
    let report = scope.close_with_diagnostics(&open, TermScopeLimits::default());
    assert_eq!(report.result.unwrap(), Expr::app(deeper, shallower));
    assert!(report.stats.context_check_visits > 0);
    // Transformation-only: this intentionally has outer loose indices and is
    // not submitted as a closed theorem or a well-typed kernel claim.
    assert!(report.stats.transformed_nodes < 100, "{:?}", report.stats);
}

#[test]
fn rebased_dependencies_reject_changed_parent_named_binding() {
    let mut scope = TermScope::new();
    let shared = successors(
        Arc::new(Expr::app(
            ordinary(Expr::apps(
                Expr::const_str("Nat.add"),
                [Expr::bvar(0), Expr::fvar(id(1))],
            )),
            Expr::nat_lit(0u64),
        )),
        16,
    );
    let deep = arm(&mut scope, &shared, 3);
    // This distinct ordinary parent is first built AFTER its child has an
    // outward hit. Its footprint combines the surviving external named read
    // with the internal ordinary read, which must be pruned, then re-probed.
    let parent = Arc::new(Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared));
    let wrap_parent = || Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), parent.clone());
    let good = ordinary(scope.lam(id(1), BinderInfo::Default, nat(), wrap_parent()));
    let bad = ordinary(scope.lam(id(3), BinderInfo::Default, nat(), wrap_parent()));
    let positive = Expr::app(deep.clone(), good.clone());
    let report = scope.close_with_diagnostics(&positive, TermScopeLimits::default());
    let closed = report.result.unwrap();
    let ExprKind::App(deep_closed, good_closed) = closed.kind() else {
        panic!("positive pair")
    };
    let ExprKind::Lam(_, _, good_closed) = good_closed.kind() else {
        panic!("ordinary prefix")
    };
    let ExprKind::Lam(_, _, good_closed) = good_closed.kind() else {
        panic!("named prefix")
    };
    let ExprKind::App(_, parent_closed) = good_closed.kind() else {
        panic!("new parent")
    };
    let ExprKind::App(_, rebound) = parent_closed.kind() else {
        panic!("rebased parent's actual child")
    };
    assert!(
        Arc::ptr_eq(child(deep_closed, 3), rebound),
        "child must actually reuse outward"
    );
    assert!(report.stats.context_check_visits > 0);
    let open = Expr::app(deep, Expr::app(good, bad));
    assert_eq!(scope.close(&open), Err(TermScopeError::OutOfScope(id(1))));
}

#[test]
fn outward_candidates_do_not_conflate_named_relative_depths_or_inward_capture() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(Expr::fvar(id(1)), Expr::bvar(0)));
    let high = scope.lam(id(2), BinderInfo::Default, nat(), shared.as_ref().clone());
    let high = scope.lam(id(1), BinderInfo::Default, nat(), high);
    let high = ordinary(high);
    let low = scope.lam(id(1), BinderInfo::Default, nat(), shared.as_ref().clone());
    let low = scope.lam(id(2), BinderInfo::Default, nat(), low);
    let wanted_high = ordinary(ordinary(ordinary(Expr::app(Expr::bvar(1), Expr::bvar(2)))));
    let wanted_low = ordinary(ordinary(Expr::app(Expr::bvar(0), Expr::bvar(2))));
    assert_eq!(
        scope.close(&Expr::app(high, low)).unwrap(),
        Expr::app(wanted_high, wanted_low)
    );

    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::bvar(0));
    let small = scope.lam(id(1), BinderInfo::Default, nat(), shared.as_ref().clone());
    let large = ordinary(scope.lam(id(1), BinderInfo::Default, nat(), shared.as_ref().clone()));
    assert_eq!(
        scope.close(&Expr::app(small, large)).unwrap(),
        Expr::app(ordinary(Expr::bvar(1)), ordinary(ordinary(Expr::bvar(1))),)
    );
}

#[test]
fn outward_hits_keep_hidden_declarations_and_original_error_order() {
    let mut scope = TermScope::new();
    let helper = Arc::new(scope.lam(id(8), BinderInfo::Default, nat(), Expr::fvar(id(1))));
    let wrap_helper = || Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), helper.clone());
    let shadow = scope.lam(id(8), BinderInfo::Default, nat(), wrap_helper());
    let shadow = scope.lam(id(1), BinderInfo::Default, nat(), shadow);
    let shadow = ordinary(shadow);
    let prime = scope.lam(id(2), BinderInfo::Default, nat(), wrap_helper());
    let mut prime = scope.lam(id(1), BinderInfo::Default, nat(), prime);
    for _ in 0..3 {
        prime = ordinary(prime);
    }
    assert_eq!(
        scope.close(&Expr::app(prime, shadow)),
        Err(TermScopeError::ShadowedLocal(id(8)))
    );

    // A declaration collision must fall back to the actual traversal. Its
    // first binder type fails before the inner shadowing declaration is read.
    let typed = Arc::new(scope.lam(
        id(8),
        BinderInfo::Default,
        Expr::fvar(id(1)),
        Expr::fvar(id(1)),
    ));
    let wrap_typed = || Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), typed.clone());
    let prime = scope.lam(id(2), BinderInfo::Default, nat(), wrap_typed());
    let mut prime = scope.lam(id(1), BinderInfo::Default, nat(), prime);
    for _ in 0..3 {
        prime = ordinary(prime);
    }
    let bad = scope.lam(id(8), BinderInfo::Default, nat(), wrap_typed());
    let bad = ordinary(scope.lam(id(3), BinderInfo::Default, nat(), bad));
    assert_eq!(
        scope.close(&Expr::app(prime, bad)),
        Err(TermScopeError::OutOfScope(id(1)))
    );
}

#[test]
fn outward_dependency_probe_caps_never_publish_partial_reuse() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(Expr::fvar(id(1)), Expr::fvar(id(2))));
    // Keep the actual App root shared: cloning it into each named body only
    // exercises separate leaf probes, never the three-node dependency join.
    let wrapped = || Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
    let deep = scope.lam(id(2), BinderInfo::Default, nat(), wrapped());
    let deep = ordinary(scope.lam(id(1), BinderInfo::Default, nat(), deep));
    let low = scope.lam(id(2), BinderInfo::Default, nat(), wrapped());
    let low = scope.lam(id(1), BinderInfo::Default, nat(), low);
    let open = Expr::app(deep, low);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let closed = closer.fold_shared(&open).expect("named input is closed");
    assert!(closer.error.is_none());
    fn joined_child(mut term: &Expr, binders: usize) -> &Arc<Expr> {
        for _ in 0..binders {
            let ExprKind::Lam(_, _, body) = term.kind() else {
                panic!("actual binder prefix")
            };
            term = body;
        }
        let ExprKind::App(_, child) = term.kind() else {
            panic!("actual shared dependency root")
        };
        child
    }
    let ExprKind::App(deep, low) = closed.kind() else {
        panic!("both original contexts")
    };
    assert!(Arc::ptr_eq(joined_child(deep, 3), joined_child(low, 2)));
    let complete = closer.stats.visits;
    assert!(closer.stats.context_check_visits >= 3);
    eprintln!("outward-scope exact budget work={:?}", closer.stats);
    for max_visits in 0..complete {
        let report = scope.close_with_diagnostics(
            &open,
            TermScopeLimits {
                max_visits,
                ..TermScopeLimits::default()
            },
        );
        assert_eq!(report.result, Err(TermScopeError::VisitLimit));
        assert_eq!(report.stats.visits, max_visits);
    }
    let report = scope.close_with_diagnostics(
        &open,
        TermScopeLimits {
            max_visits: complete,
            ..TermScopeLimits::default()
        },
    );
    assert!(report.result.is_ok());
    assert_eq!(report.stats.visits, complete);
}

#[test]
fn mixed_lambda_pi_let_proof_replays_strictly_after_lossless_dag_transport() {
    let mut scope = TermScope::new();
    let eq = |left: Expr, right: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat(), left, right],
        )
    };
    let shared = Arc::new(Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), Expr::fvar(id(1))],
    ));
    let build_body = || {
        Expr::let_named(
            Name::from_string("retained_proof"),
            Expr::pi(
                BinderInfo::Default,
                nat(),
                eq(Expr::fvar(id(1)), Expr::fvar(id(1))),
            ),
            Expr::lam_arc(BinderInfo::Default, Arc::new(nat()), shared.clone()),
            Expr::app(Expr::bvar(0), Expr::nat_lit(0u64)),
            false,
        )
    };
    let mut open_arms = Vec::new();
    let mut oracle_arms = Vec::new();
    for count in [3, 1] {
        let body = build_body();
        let mut oracle = Expr::app(ordinary(body.abstract_fvar(id(1))), Expr::nat_lit(0u64));
        let mut arm = Expr::app(
            scope.lam(id(1), BinderInfo::Default, nat(), body),
            Expr::nat_lit(0u64),
        );
        for _ in 0..count {
            arm = Expr::app(ordinary(arm), Expr::nat_lit(0u64));
            oracle = Expr::app(ordinary(oracle), Expr::nat_lit(0u64));
        }
        open_arms.push(arm);
        oracle_arms.push(oracle);
    }
    let trans = |arms: Vec<Expr>| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            ),
            [
                vec![
                    nat(),
                    Expr::nat_lit(0u64),
                    Expr::nat_lit(0u64),
                    Expr::nat_lit(0u64),
                ],
                arms,
            ]
            .concat(),
        )
    };
    let report = scope.close_with_diagnostics(&trans(open_arms), TermScopeLimits::default());
    let proof = report.result.unwrap();
    assert_eq!(proof, trans(oracle_arms));
    assert!(report.stats.context_check_visits > 0);
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars_quick());
    let claim = eq(Expr::nat_lit(0u64), Expr::nat_lit(0u64));
    let wrong = eq(Expr::nat_lit(0u64), Expr::nat_lit(1u64));
    let roundtrip = |term: &Expr| {
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
        assert_eq!(&decoded, term);
        assert_eq!(
            trust_ir::proof::encode_clean_expr_dag_v2(&decoded).unwrap(),
            bytes
        );
        decoded
    };
    let decoded_proof = roundtrip(&proof);
    let decoded_claim = roundtrip(&claim);
    let decoded_wrong = roundtrip(&wrong);
    let mut env = Environment::default();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    for (proof, claim, wrong) in [
        (proof, claim, wrong),
        (decoded_proof, decoded_claim, decoded_wrong),
    ] {
        for (goal, accepted) in [(&claim, true), (&wrong, false)] {
            let mut checker = TypeChecker::new(&env);
            checker.set_allow_unsafe(false);
            checker.set_allow_partial(false);
            checker.set_heartbeat_limit(2_000_000);
            checker
                .check_type(goal, &Expr::sort(Level::zero()))
                .unwrap();
            let result = checker.check_type(&proof, goal);
            if accepted {
                result.unwrap();
                let audit = env.audit_certification(goal, &proof);
                assert!(audit.is_certified(), "{audit:#?}");
                for dependency in &audit.dependencies {
                    assert!(env.axiom_deps(dependency).unwrap().is_empty());
                    assert!(env.trust_marker_deps(dependency).unwrap().is_empty());
                }
            } else {
                assert!(matches!(
                    result.unwrap_err(),
                    KernelTypeError::TypeMismatch { .. }
                ));
            }
            assert!(!checker.heartbeat_spent());
        }
    }
}
