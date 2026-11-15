// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{
    proof_assembly::{ProofAssembly, ProofLimits},
    scoped_local::{LocalScope, LocalScopeLimits},
    term_scope::TermScopeLimits,
};
use clean_kernel::{BinderInfo, Environment, Level, Name, TypeChecker, expr::MDataValue};

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn fresh_logic() -> ProofAssembly {
    ProofAssembly::new(ProofLimits::default()).unwrap()
}

fn body(expr: &Expr) -> &Arc<Expr> {
    let ExprKind::Lam(_, _, body) = expr.kind() else {
        panic!("expected lambda")
    };
    body
}

#[test]
fn success_reuses_normalized_dag_and_charges_every_hit() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(nat()).unwrap();
    let input = x.lam(Expr::app(Expr::const_str("Nat.succ"), x.term().clone()));
    let mut logic = ProofAssembly::new(ProofLimits {
        operations: 2,
        ..ProofLimits::default()
    })
    .unwrap();
    let first = logic.normalize_open(&scope, [], &input).unwrap();
    let second = logic.normalize_open(&scope, [], &input.clone()).unwrap();
    assert!(Arc::ptr_eq(body(&first), body(&second)));
    assert_eq!(logic.operations, 2);
    assert_eq!(
        logic
            .normalized
            .buckets
            .values()
            .map(Vec::len)
            .sum::<usize>(),
        1
    );
    assert!(logic.normalized.retained > 0);
    assert_eq!(
        logic.normalize_open(&scope, [], &input).unwrap_err(),
        "proof assembly operation limit"
    );
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let expected = Expr::pi(BinderInfo::Default, nat(), nat());
    TypeChecker::new(&env)
        .check_type(&first, &expected)
        .unwrap();
    TypeChecker::new(&env)
        .check_type(&second, &expected)
        .unwrap();
}

#[test]
fn dependent_capture_order_owner_and_current_limits_are_checked_before_reuse() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(Expr::type_()).unwrap();
    let x = scope.try_local(a.term().clone()).unwrap();
    let y = scope.try_local(a.term().clone()).unwrap();
    let input = y.lam(x.term().clone());
    let mut logic = fresh_logic();
    let first = logic.normalize_open(&scope, [&a, &x], &input).unwrap();
    let second = logic.normalize_open(&scope, [&a, &x], &input).unwrap();
    assert!(Arc::ptr_eq(body(&first), body(&second)));
    assert!(logic.normalize_open(&scope, [&x, &a], &input).is_err());
    assert!(logic.normalize_open(&scope, [&a, &a, &x], &input).is_err());
    assert!(logic.normalize_open(&scope, [&a], &input).is_err());
    let mut foreign = LocalScope::new();
    let foreign_a = foreign.try_local(Expr::type_()).unwrap();
    assert_eq!(a.id(), foreign_a.id());
    assert_eq!(
        logic
            .normalize_open(&scope, [&foreign_a, &x], &input)
            .unwrap_err(),
        "capture belongs to another local owner"
    );
    logic.limits.captures = 1;
    assert_eq!(
        logic.normalize_open(&scope, [&a, &x], &input).unwrap_err(),
        "proof capture limit"
    );
    assert_eq!(
        logic.operations, 7,
        "errors also consume their original operation charge"
    );
}

#[test]
fn exact_scope_identity_and_named_body_identity_are_not_structural_equality() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(nat()).unwrap();
    let named = x.lam(Expr::bvar(0));
    let ordinary = Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0));
    assert_eq!(named, ordinary, "raw syntax deliberately collides");
    assert!(!same_graph(&named, &ordinary));
    let mut logic = fresh_logic();
    let first = logic.normalize_open(&scope, [], &named).unwrap();
    let second = logic.normalize_open(&scope, [], &ordinary).unwrap();
    assert_eq!(**body(&first), Expr::bvar(1));
    assert_eq!(**body(&second), Expr::bvar(0));
    // Identical retained input in another scope has no named-body annotation.
    let foreign = LocalScope::new();
    let third = logic.normalize_open(&foreign, [], &named).unwrap();
    assert_eq!(third, second);
    assert_ne!(first, third);
    assert_eq!(
        logic
            .normalized
            .buckets
            .values()
            .map(Vec::len)
            .sum::<usize>(),
        3
    );
}

#[test]
fn successful_keys_survive_only_immutable_input_and_append_only_scope_growth() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(nat()).unwrap();
    let input = x.lam(Expr::app(Expr::const_str("Nat.succ"), x.term().clone()));
    let mut logic = fresh_logic();
    let first = logic.normalize_open(&scope, [], &input).unwrap();
    for _ in 0..8 {
        let unrelated = scope.try_local(nat()).unwrap();
        let _binding = unrelated.let_(Expr::nat_lit(1u64), unrelated.term().clone());
    }
    let second = logic.normalize_open(&scope, [], &input).unwrap();
    assert!(Arc::ptr_eq(body(&first), body(&second)));
    let changed = x.lam(Expr::app(Expr::const_str("Nat.succ"), Expr::nat_lit(2u64)));
    let third = logic.normalize_open(&scope, [], &changed).unwrap();
    assert_ne!(third, first);
    let mut other_producer = fresh_logic();
    let independent = other_producer.normalize_open(&scope, [], &input).unwrap();
    assert_eq!(independent, first);
    assert!(
        !Arc::ptr_eq(body(&independent), body(&first)),
        "no cache shared across producers"
    );
}

#[test]
fn failed_unknown_shadowed_and_limited_closes_are_never_cached() {
    let mut scope = LocalScope::new();
    let input = Expr::fvar(clean_kernel::expr::FVarId::new(0));
    let mut logic = fresh_logic();
    assert!(logic.normalize_open(&scope, [], &input).is_err());
    assert_eq!(logic.normalized.retained, 0);
    let x = scope.try_local(nat()).unwrap();
    let good = logic.normalize_open(&scope, [&x], &input).unwrap();
    assert_eq!(good, input);
    let retained = logic.normalized.retained;
    let escaped = logic.normalize_open(&scope, [], &input).unwrap_err();
    assert!(escaped.contains("outside its binder scope"));
    let shadowed = x.lam(x.lam(x.term().clone()));
    assert!(
        logic
            .normalize_open(&scope, [], &shadowed)
            .unwrap_err()
            .contains("bound twice")
    );
    assert_eq!(logic.normalized.retained, retained);
    for closing in [
        TermScopeLimits {
            max_visits: 0,
            ..TermScopeLimits::default()
        },
        TermScopeLimits {
            max_depth: 0,
            ..TermScopeLimits::default()
        },
    ] {
        let limited = LocalScope::with_limits(LocalScopeLimits {
            closing,
            ..LocalScopeLimits::default()
        });
        let error = logic.normalize_open(&limited, [], &nat()).unwrap_err();
        assert!(error.contains("limit"), "{error}");
        assert_eq!(logic.normalized.retained, retained);
    }
}

#[test]
fn hash_collisions_and_changed_capture_types_cannot_select_a_cached_result() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(nat()).unwrap();
    let b = scope.try_local(Expr::type_()).unwrap();
    let shared = Arc::new(Expr::nat_lit(0u64));
    let left = Expr::from_kind(ExprKind::MData(
        vec![(Name::from_string("memo"), MDataValue::Bool(false))],
        shared.clone(),
    ));
    let right = Expr::from_kind(ExprKind::MData(
        vec![(Name::from_string("memo"), MDataValue::Bool(true))],
        shared,
    ));
    let owner = scope.memo_owner();
    let hash = key_hash(&owner, [].into_iter(), &left);
    assert_eq!(
        hash,
        key_hash(&owner, [].into_iter(), &right),
        "MData ignores tags in cached hash"
    );
    let mut memo = NormalizeMemo::default();
    let first = Expr::nat_lit(1u64);
    let second = Expr::nat_lit(2u64);
    memo.insert(hash, owner.clone(), [].into_iter(), &left, &first, 16);
    assert!(memo.get(hash, &owner, [].into_iter(), &right).is_none());
    memo.insert(hash, owner.clone(), [].into_iter(), &right, &second, 16);
    assert_eq!(
        memo.get(hash, &owner, [].into_iter(), &left).unwrap(),
        first
    );
    assert_eq!(
        memo.get(hash, &owner, [].into_iter(), &right).unwrap(),
        second
    );
    // Force the same index to exercise the exact ordered capture predicate,
    // independently of its normal hash prefilter.
    memo.insert(hash, owner.clone(), [&a, &b].into_iter(), &left, &first, 16);
    assert!(
        memo.get(hash, &owner, [&b, &a].into_iter(), &left)
            .is_none()
    );
    assert!(
        memo.get(hash, &owner, [&a, &a].into_iter(), &left)
            .is_none()
    );
}

#[test]
fn retention_eviction_bounds_entries_and_handles_without_changing_results() {
    let scope = LocalScope::new();
    let mut logic = ProofAssembly::new(ProofLimits {
        captures: 8,
        ..ProofLimits::default()
    })
    .unwrap();
    for n in 0u64..8 {
        let input = Expr::nat_lit(n);
        assert_eq!(logic.normalize_open(&scope, [], &input).unwrap(), input);
        assert!(logic.normalized.retained <= 8);
    }
    assert_eq!(
        logic
            .normalize_open(&scope, [], &Expr::nat_lit(0u64))
            .unwrap(),
        Expr::nat_lit(0u64)
    );
    let mut scope = LocalScope::new();
    let captures: Vec<_> = (0..8).map(|_| scope.try_local(nat()).unwrap()).collect();
    // Captures at the admissible limit still normalize when the entry's
    // graph/root-copy weight would exceed the retention budget.
    let before = logic.normalized.retained;
    assert_eq!(
        logic
            .normalize_open(&scope, captures.iter(), captures[0].term())
            .unwrap(),
        *captures[0].term()
    );
    assert_eq!(logic.normalized.retained, before);
}

#[test]
fn cached_entries_do_not_retain_their_whole_local_scope_owner() {
    let mut logic = fresh_logic();
    let identity;
    {
        let mut scope = LocalScope::new();
        let x = scope.try_local(nat()).unwrap();
        identity = scope.memo_owner();
        assert!(identity.is_alive());
        for _ in 0..32 {
            let unrelated = scope.try_local(nat()).unwrap();
            let _binding = unrelated.lam(Expr::app(nat(), unrelated.term().clone()));
        }
        assert_eq!(
            logic.normalize_open(&scope, [&x], x.term()).unwrap(),
            *x.term()
        );
        assert!(logic.normalized.retained > 0);
    }
    // Both the owner token and stored capture snapshots must be non-owning.
    assert!(
        !identity.is_alive(),
        "cache retained the unrelated binder registry"
    );
    assert!(
        !logic
            .normalized
            .buckets
            .values()
            .flatten()
            .next()
            .unwrap()
            .owner
            .is_alive()
    );
    let new_scope = LocalScope::new();
    assert!(!identity.matches(&new_scope.memo_owner()));
}

#[test]
fn oversized_output_is_not_retained_and_does_not_evict_a_small_entry() {
    let scope = LocalScope::new();
    let owner = scope.memo_owner();
    let input = Expr::nat_lit(0u64);
    let small = Expr::nat_lit(1u64);
    let mut output = Arc::new(Expr::nat_lit(2u64));
    for _ in 0..32 {
        output = Arc::new(Expr::app_arc(output.clone(), output));
    }
    let mut memo = NormalizeMemo::default();
    memo.insert(1, owner.clone(), [].into_iter(), &input, &small, 16);
    assert_eq!(memo.retained, 3, "entry plus two scalar Expr root copies");
    memo.insert(2, owner.clone(), [].into_iter(), &input, &output, 16);
    assert_eq!(memo.retained, 3);
    assert!(memo.get(2, &owner, [].into_iter(), &input).is_none());
    assert_eq!(memo.get(1, &owner, [].into_iter(), &input).unwrap(), small);
}

#[test]
fn shared_dag_weight_is_physical_and_aggregate_eviction_is_bounded() {
    let mut dag = Arc::new(Expr::nat_lit(0u64));
    for _ in 0..32 {
        dag = Arc::new(Expr::app_arc(dag.clone(), dag));
    }
    let input = (*dag).clone();
    // Two root copies + one entry + exactly 32 shared child allocations, not
    // the exponentially expanded tree. Aliased supplied roots still count twice.
    assert_eq!(
        retained_weight([].into_iter(), &input, &input, 35),
        Some(35)
    );
    assert_eq!(retained_weight([].into_iter(), &input, &input, 34), None);
    let scope = LocalScope::new();
    let owner = scope.memo_owner();
    let mut memo = NormalizeMemo::default();
    memo.insert(1, owner.clone(), [].into_iter(), &input, &input, 35);
    assert_eq!(memo.retained, 35);
    let small = Expr::nat_lit(1u64);
    memo.insert(2, owner.clone(), [].into_iter(), &small, &small, 35);
    assert_eq!(
        memo.retained, 3,
        "old graph evicted before aggregate budget overflow"
    );
    assert!(memo.get(1, &owner, [].into_iter(), &input).is_none());
    assert_eq!(memo.get(2, &owner, [].into_iter(), &small).unwrap(), small);
}

#[test]
fn every_constructor_keeps_exact_children_and_scalar_identity() {
    fn cases(a: Arc<Expr>, b: Arc<Expr>, c: Arc<Expr>, d: Arc<Expr>) -> Vec<Expr> {
        let kinds = vec![
            ExprKind::BVar(0),
            ExprKind::FVar(clean_kernel::expr::FVarId::new(0)),
            ExprKind::Sort(Level::zero()),
            ExprKind::Const(Name::from_string("Nat"), Default::default()),
            ExprKind::App(a.clone(), b.clone()),
            ExprKind::Lam(BinderInfo::Default.into(), a.clone(), b.clone()),
            ExprKind::Pi(BinderInfo::Default.into(), a.clone(), b.clone()),
            ExprKind::Let(Name::anon(), a.clone(), b.clone(), c.clone(), false),
            Expr::nat_lit(0u64).kind().clone(),
            ExprKind::Proj(Name::from_string("Prod"), 0, a.clone()),
            ExprKind::MData(Vec::new(), a.clone()),
            ExprKind::SProp,
            ExprKind::Squash(a.clone()),
            ExprKind::CubicalInterval,
            ExprKind::CubicalI0,
            ExprKind::CubicalI1,
            ExprKind::CubicalPath {
                ty: a.clone(),
                left: b.clone(),
                right: c.clone(),
            },
            ExprKind::CubicalPathLam { body: a.clone() },
            ExprKind::CubicalPathApp {
                path: a.clone(),
                arg: b.clone(),
            },
            ExprKind::CubicalHComp {
                ty: a.clone(),
                phi: b.clone(),
                u: c.clone(),
                base: d.clone(),
            },
            ExprKind::CubicalTransp {
                ty: a.clone(),
                phi: b.clone(),
                base: c.clone(),
            },
            ExprKind::CubicalCoe {
                ty: a.clone(),
                r: b.clone(),
                s: c.clone(),
                base: d.clone(),
            },
            ExprKind::ZFCSet(ZFCSetExpr::Empty),
            ExprKind::ZFCSet(ZFCSetExpr::Infinity),
            ExprKind::ZFCSet(ZFCSetExpr::Singleton(a.clone())),
            ExprKind::ZFCSet(ZFCSetExpr::Pair(a.clone(), b.clone())),
            ExprKind::ZFCSet(ZFCSetExpr::Union(a.clone())),
            ExprKind::ZFCSet(ZFCSetExpr::PowerSet(a.clone())),
            ExprKind::ZFCSet(ZFCSetExpr::Separation {
                set: a.clone(),
                pred: b.clone(),
            }),
            ExprKind::ZFCSet(ZFCSetExpr::Replacement {
                set: a.clone(),
                func: b.clone(),
            }),
            ExprKind::ZFCSet(ZFCSetExpr::Choice(a.clone())),
            ExprKind::ZFCMem {
                element: a.clone(),
                set: b.clone(),
            },
            ExprKind::ZFCComprehension { domain: a, pred: b },
        ];
        kinds.into_iter().map(Expr::from_kind).collect()
    }
    let leaves = std::array::from_fn::<_, 4, _>(|n| Arc::new(Expr::nat_lit(n as u64)));
    let original = cases(
        leaves[0].clone(),
        leaves[1].clone(),
        leaves[2].clone(),
        leaves[3].clone(),
    );
    // Independent fixture census: do not derive an affected edge from the
    // children() implementation under test, where an omission could mask it.
    let arities = [
        0, 0, 0, 0, 2, 2, 2, 3, 0, 1, 1, 0, 1, 0, 0, 0, 3, 1, 2, 4, 3, 4, 0, 0, 1, 2, 1, 1, 2, 2,
        1, 2, 2,
    ];
    assert_eq!(original.len(), arities.len());
    for input in &original {
        assert!(same_graph(input, &input.clone()));
    }
    for position in 0..4 {
        let mut replaced = leaves.clone();
        replaced[position] = Arc::new((*replaced[position]).clone());
        let mutants = cases(
            replaced[0].clone(),
            replaced[1].clone(),
            replaced[2].clone(),
            replaced[3].clone(),
        );
        for ((input, mutant), arity) in original.iter().zip(&mutants).zip(arities) {
            assert_eq!(input, mutant, "same syntax, changed allocation");
            let affected = position < arity;
            assert_eq!(same_graph(input, mutant), !affected);
        }
    }
    for (a, b) in [
        (Expr::bvar(0), Expr::bvar(1)),
        (Expr::const_str("Nat"), Expr::const_str("Bool")),
        (Expr::nat_lit(0u64), Expr::nat_lit(1u64)),
    ] {
        assert_eq!(child_ids(&a), child_ids(&b));
        assert!(!same_graph(&a, &b));
    }
}
