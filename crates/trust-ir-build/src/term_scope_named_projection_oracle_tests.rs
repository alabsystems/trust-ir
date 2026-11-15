// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Seeded shared-edge controls; ordinary abstraction is the independent oracle.

use super::*;
use clean_kernel::{BinderInfo, Environment, TypeChecker};

struct Cases(u64);

impl Cases {
    fn choose(&mut self, bound: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        usize::try_from(self.0 >> 32).unwrap() % bound
    }

    fn frames(&mut self, count: usize, base: u64) -> Vec<Frame> {
        let mut frames: Vec<_> = (0..count)
            .map(|index| {
                if self.choose(2) == 0 {
                    Frame::Ordinary
                } else {
                    Frame::Named(FVarId::new(base + u64::try_from(index).unwrap()))
                }
            })
            .collect();
        frames.push(Frame::Named(FVarId::new(1)));
        frames
    }
}

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn ordinary_count(frames: &[Frame]) -> usize {
    frames
        .iter()
        .filter(|frame| matches!(frame, Frame::Ordinary))
        .count()
}

fn shape(kind: usize) -> Expr {
    let add = || {
        Expr::apps(
            Expr::const_str("Nat.add"),
            [Expr::bvar(0), Expr::fvar(FVarId::new(1))],
        )
    };
    match kind {
        0 => Expr::fvar(FVarId::new(1)),
        1 => Expr::app(
            Expr::lam(BinderInfo::Default, nat(), add()),
            Expr::nat_lit(0u64),
        ),
        2 => Expr::let_named(Name::anon(), nat(), Expr::nat_lit(0u64), add(), false),
        3 => Expr::mdata(Default::default(), shape(1)),
        _ => unreachable!("four fixed source shapes"),
    }
}

fn input_arm(scope: &mut TermScope, shared: &Arc<Expr>, frames: &[Frame]) -> Expr {
    let mut body = Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
    for frame in frames.iter().rev() {
        let function = match *frame {
            Frame::Ordinary => Expr::lam(BinderInfo::Default, nat(), body),
            Frame::Named(id) => scope.lam(id, BinderInfo::Default, nat(), body),
        };
        body = Expr::app(function, Expr::nat_lit(0u64));
    }
    body
}

fn oracle_arm(closed_child: &Expr, depth: usize) -> Expr {
    let mut body = Expr::app(Expr::const_str("Nat.succ"), closed_child.clone());
    for _ in 0..depth {
        body = Expr::app(
            Expr::lam(BinderInfo::Default, nat(), body),
            Expr::nat_lit(0u64),
        );
    }
    body
}

fn child(mut arm: &Expr, depth: usize) -> &Arc<Expr> {
    for _ in 0..depth {
        let ExprKind::App(function, _) = arm.kind() else {
            panic!("actual frame application")
        };
        let ExprKind::Lam(_, _, body) = function.kind() else {
            panic!("actual frame lambda")
        };
        arm = body;
    }
    let ExprKind::App(_, shared) = arm.kind() else {
        panic!("actual shared child edge")
    };
    shared
}

fn workload(cases: &mut Cases, ordinal: usize, kind: usize) -> (TermScope, Expr, Expr, [usize; 2]) {
    let old_prefix = 3 + cases.choose(7);
    let removed = ordinal % 3;
    let old = cases.frames(old_prefix, 100);
    let mut new = cases.frames(old_prefix - removed, 200);
    if ordinary_count(&old).checked_sub(ordinary_count(&new)) == Some(removed) {
        // Force an original-selector shape miss, without editing the shared
        // expression or its metadata. There is always a prefix frame here.
        new[0] = match new[0] {
            Frame::Ordinary => Frame::Named(FVarId::new(300)),
            Frame::Named(_) => Frame::Ordinary,
        };
    }
    assert_ne!(
        ordinary_count(&old).checked_sub(ordinary_count(&new)),
        Some(removed)
    );
    let mut shared = Arc::new(shape(kind));
    for _ in 0..1 + cases.choose(12) {
        shared = Arc::new(Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared));
    }
    assert!(!shared.has_loose_bvars_quick());
    // This ordinary constructor is independent of TermScope's closing/cache.
    let oracle = shared.abstract_fvar(FVarId::new(1));
    let mut scope = TermScope::new();
    let arms = [
        input_arm(&mut scope, &shared, &old),
        input_arm(&mut scope, &shared, &new),
    ];
    let expected = Expr::apps(
        Expr::const_str("Nat.add"),
        [
            oracle_arm(&oracle, old.len()),
            oracle_arm(&oracle, new.len()),
        ],
    );
    (
        scope,
        Expr::apps(Expr::const_str("Nat.add"), arms),
        expected,
        [old.len(), new.len()],
    )
}

#[test]
fn seeded_mixed_contexts_preserve_typed_outputs_and_actual_child_sharing() {
    let mut cases = Cases(20_261_009);
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let mut hits = 0;
    let mut probes = 0;
    for ordinal in 0..48 {
        for kind in 0..4 {
            let (scope, open, expected, depths) = workload(&mut cases, ordinal, kind);
            let mut checker = TypeChecker::new(&env);
            checker.set_allow_unsafe(false);
            checker.set_allow_partial(false);
            checker.set_heartbeat_limit(2_000_000);
            checker.check_type(&expected, &nat()).unwrap();
            let report = scope.close_with_diagnostics(&open, TermScopeLimits::default());
            let closed = report.result.unwrap();
            assert_eq!(closed, expected, "ordinal={ordinal}, kind={kind}");
            checker.check_type(&closed, &nat()).unwrap();
            assert!(!checker.heartbeat_spent());
            let ExprKind::App(function, right) = closed.kind() else {
                panic!("actual Nat.add second arm")
            };
            let ExprKind::App(_, left) = function.kind() else {
                panic!("actual Nat.add first arm")
            };
            assert!(Arc::ptr_eq(child(left, depths[0]), child(right, depths[1])));
            assert!(report.diagnostics.cache.named_only_contextual_hits > 0);
            assert!(report.stats.context_check_visits > 0);
            hits += report.diagnostics.cache.named_only_contextual_hits;
            probes += report.stats.context_check_visits;
        }
    }
    eprintln!(
        "seed20261009: 192 typed mixed-context shared-edge cases; hits={hits}, charged dependency probes={probes}; not benchmark/proof authority"
    );
}

#[test]
fn seeded_budget_boundaries_keep_plain_and_observed_results_identical() {
    let mut cases = Cases(20_261_009);
    for ordinal in 0..12 {
        let (scope, open, expected, _) = workload(&mut cases, ordinal, ordinal % 4);
        let full = scope
            .close_with_limits(&open, TermScopeLimits::default())
            .unwrap();
        assert_eq!(full.term, expected);
        for max_visits in [
            0,
            1,
            full.stats.visits - 1,
            full.stats.visits,
            full.stats.visits + 1,
        ] {
            let limits = TermScopeLimits {
                max_visits,
                ..TermScopeLimits::default()
            };
            let plain = scope.close_impl(&open, limits, false);
            let observed = scope.close_with_diagnostics(&open, limits);
            assert_eq!(plain.result, observed.result);
            assert_eq!(plain.stats, observed.stats);
            if max_visits < full.stats.visits {
                assert_eq!(plain.result, Err(TermScopeError::VisitLimit));
                assert_eq!(plain.stats.visits, max_visits);
            } else {
                assert_eq!(plain.result, Ok(expected.clone()));
            }
        }
    }
}

#[test]
fn wide_named_contexts_preserve_the_independent_closed_and_kernel_typed_oracle() {
    let mut scope = TermScope::new();
    let first = FVarId::new(1);
    let second = FVarId::new(2);
    let old = std::iter::once(Frame::Named(first))
        .chain(std::iter::once(Frame::Named(second)))
        .chain((0..130).map(|i| Frame::Named(FVarId::new(100 + i))))
        .collect::<Vec<_>>();
    let new = std::iter::once(Frame::Named(second))
        .chain((0..31).map(|i| Frame::Named(FVarId::new(500 + i))))
        .chain(std::iter::once(Frame::Named(first)))
        .chain((0..103).map(|i| Frame::Named(FVarId::new(700 + i))))
        .collect::<Vec<_>>();
    let mut shared = Arc::new(Expr::apps(
        Expr::const_str("Nat.add"),
        [Expr::fvar(first), Expr::fvar(second)],
    ));
    for _ in 0..24 {
        shared = Arc::new(Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared));
    }
    let arms = [
        input_arm(&mut scope, &shared, &old),
        input_arm(&mut scope, &shared, &new),
    ];
    let input = Expr::apps(Expr::const_str("Nat.add"), arms);
    let expected_child = |frames: &[Frame]| {
        let index = |id| {
            u32::try_from(
                frames.len()
                    - 1
                    - frames
                        .iter()
                        .position(|frame| matches!(frame, Frame::Named(actual) if *actual == id))
                        .unwrap(),
            )
            .unwrap()
        };
        let mut body = Expr::apps(
            Expr::const_str("Nat.add"),
            [Expr::bvar(index(first)), Expr::bvar(index(second))],
        );
        for _ in 0..24 {
            body = Expr::app(Expr::const_str("Nat.succ"), body);
        }
        body
    };
    let expected = Expr::apps(
        Expr::const_str("Nat.add"),
        [
            oracle_arm(&expected_child(&old), old.len()),
            oracle_arm(&expected_child(&new), new.len()),
        ],
    );
    let report = scope.close_with_diagnostics(&input, TermScopeLimits::default());
    let actual = report.result.unwrap();
    assert_eq!(actual, expected);
    let mut env = Environment::new();
    env.init_nat().unwrap();
    TypeChecker::new(&env).check_type(&actual, &nat()).unwrap();
    assert!(report.diagnostics.cache.named_projection_contextual_hits > 0);
}
