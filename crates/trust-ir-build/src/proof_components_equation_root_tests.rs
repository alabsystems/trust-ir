// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::super::bounded_instantiate::TelescopeWork;
use super::*;
use crate::term_scope::TermScopeLimits;
use clean_kernel::{Environment, Level};
fn n() -> Expr {
    Expr::const_str("Nat")
}
fn succ(mut value: Expr, count: usize) -> Expr {
    for _ in 0..count {
        value = Expr::app(Expr::const_str("Nat.succ"), value);
    }
    value
}
fn equality(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [n(), left, right],
    )
}
fn fixture(scope: &LocalScope, external: &[ScopedLocal]) -> (ProofComponents, ExternalContext) {
    let mut parts = ProofComponents::new("equation.roots", ProofLimits::default());
    parts.set_base(scope, vec![]).unwrap();
    let mut context = parts.charged_external_context(scope, external).unwrap();
    parts
        .charged_enable_external_materialization_reuse(scope, &mut context)
        .unwrap();
    (parts, context)
}
fn statement(scope: &mut LocalScope) -> (ScopedLocal, Expr) {
    let x = scope.try_local(n()).unwrap();
    let shared = succ(x.term().clone(), 40);
    let root = x.pi(equality(shared.clone(), shared));
    (x, root)
}
fn run(
    parts: &mut ProofComponents,
    scope: &LocalScope,
    context: &ExternalContext,
    root: &Expr,
    args: &[Expr],
) -> (Result<Expr, String>, TelescopeWork) {
    parts.charged_instantiate_in_external_context_observed(scope, context, root, args)
}

#[test]
fn equation_root_reuses_only_materialization_with_changed_arguments_and_original_replay() {
    let mut scope = LocalScope::new();
    let (_, root) = statement(&mut scope);
    let (mut parts, context) = fixture(&scope, &[]);
    let (first, cold) = run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(3)]);
    let first = first.unwrap();
    let (second, warm) = run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(7)]);
    let second = second.unwrap();
    let expected = equality(succ(Expr::nat_lit(3), 40), succ(Expr::nat_lit(3), 40));
    assert_eq!(first, expected);
    assert_eq!(
        second,
        equality(succ(Expr::nat_lit(7), 40), succ(Expr::nat_lit(7), 40))
    );
    assert_ne!(first, second);
    assert!(warm.materialization < cold.materialization);
    assert_eq!(context.inventory.equation_root_count(), 1);
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [n(), succ(Expr::nat_lit(3), 40)],
    );
    let bundle = parts
        .close_scoped(&scope, proof, first, TermScopeLimits::default())
        .unwrap();
    let bytes = bundle.encode_with_claim(&expected).unwrap();
    let (decoded, claim) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, expected);
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    decoded.replay(&env, &claim, 2_000_000).unwrap();
}

#[test]
fn equation_root_same_owner_independent_inventories_cannot_share_generation_zero() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let x = scope.try_local(n()).unwrap();
    let value = succ(a.term().clone(), 40);
    let root = x.pi(equality(value.clone(), value));
    let (mut parts, first) = fixture(&scope, &[a.clone()]);
    run(&mut parts, &scope, &first, &root, &[Expr::nat_lit(0)])
        .0
        .unwrap();
    let mut second = parts.charged_external_context(&scope, &[b]).unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut second)
        .unwrap();
    let error = run(&mut parts, &scope, &second, &root, &[Expr::nat_lit(0)])
        .0
        .unwrap_err();
    assert!(error.contains(&crate::term_scope::TermScopeError::OutOfScope(a.id()).to_string()));
    assert_eq!(first.inventory.equation_root_count(), 1);
    assert_eq!(second.inventory.equation_root_count(), 0);
    run(&mut parts, &scope, &first, &root, &[Expr::nat_lit(1)])
        .0
        .unwrap();
}

#[test]
fn equation_root_unused_name_shadow_growth_is_checked_before_bad_arguments() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let mut result = n();
    for _ in 0..40 {
        result = Expr::arrow(n(), result);
    }
    let root = x.pi(result); // x never appears as an FVar.
    let (mut parts, mut context) = fixture(&scope, &[]);
    run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
        .0
        .unwrap();
    assert_eq!(context.inventory.equation_root_count(), 1);
    parts
        .charged_extend_external_context(&scope, &mut context, &[x.clone()])
        .unwrap();
    let before = parts.counts().3;
    let error = run(&mut parts, &scope, &context, &root, &[Expr::bvar(0)])
        .0
        .unwrap_err();
    assert!(error.contains(&crate::term_scope::TermScopeError::ShadowedLocal(x.id()).to_string()));
    assert!(parts.counts().3 > before);
    context.restore(0).unwrap();
    assert!(
        run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
            .0
            .unwrap_err()
            .contains(&crate::term_scope::TermScopeError::VisitLimit.to_string())
    );
}

#[test]
fn equation_root_unused_shared_names_in_types_and_let_values_are_retained() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let y = scope.try_local(n()).unwrap();
    let hidden_type = y.pi(n());
    let hidden_value = y.lam(Expr::nat_lit(0));
    let z = scope.try_local(hidden_type.clone()).unwrap();
    let mut tail = n();
    for _ in 0..30 {
        tail = Expr::arrow(n(), tail);
    }
    let root = x.pi(z.let_(
        hidden_value,
        Expr::arrow(hidden_type.clone(), Expr::arrow(hidden_type, tail)),
    ));
    assert!(!root.has_fvar_quick(), "every deferred name is unused");
    let (mut parts, mut context) = fixture(&scope, &[]);
    run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
        .0
        .unwrap();
    assert_eq!(context.inventory.equation_root_count(), 1);
    parts
        .charged_extend_external_context(&scope, &mut context, &[y.clone()])
        .unwrap();
    let error = run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(1)])
        .0
        .unwrap_err();
    assert!(error.contains(&crate::term_scope::TermScopeError::ShadowedLocal(y.id()).to_string()));
}

#[test]
fn equation_root_shadow_and_reduced_depth_keep_the_fresh_canonical_refusal() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let mut result = n();
    for _ in 0..40 {
        result = Expr::arrow(n(), result);
    }
    let root = x.pi(result);
    let (mut parts, mut context) = fixture(&scope, &[]);
    run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
        .0
        .unwrap();
    assert_eq!(context.inventory.equation_root_count(), 1);
    parts
        .charged_extend_external_context(&scope, &mut context, &[x.clone()])
        .unwrap();
    let limits = TermScopeLimits {
        max_visits: 10_000,
        max_depth: 20,
    };
    let (canonical, _) =
        scope.close_external_forest_fully_with_limits(&[root.clone()], &[x.clone()], &[1], limits);
    let expected = crate::scoped_local::LocalScopeError::Closure(
        crate::term_scope::TermScopeError::ShadowedLocal(x.id()),
    );
    assert_eq!(canonical.unwrap_err(), expected);
    let (actual, stats) =
        scope.close_prepared_equation_forest_fully_with_limits(&[root], &context.inventory, limits);
    assert_eq!(actual.unwrap_err(), expected);
    assert!(stats.visits > 0);
}

#[test]
fn equation_root_foreign_attempts_do_not_poison_the_owner_or_certify_another_graph() {
    let mut scope = LocalScope::new();
    let (x, root) = statement(&mut scope);
    let (mut parts, context) = fixture(&scope, &[]);
    run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
        .0
        .unwrap();
    let (mut foreign_parts, _) = fixture(&scope, &[]);
    assert!(
        run(
            &mut foreign_parts,
            &scope,
            &context,
            &root,
            &[Expr::nat_lit(0)]
        )
        .0
        .is_err()
    );
    let foreign_scope = LocalScope::new();
    assert!(
        run(
            &mut parts,
            &foreign_scope,
            &context,
            &root,
            &[Expr::nat_lit(0)]
        )
        .0
        .is_err()
    );
    let expected = equality(succ(Expr::nat_lit(7), 40), succ(Expr::nat_lit(7), 40));
    assert_eq!(
        run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(7)])
            .0
            .unwrap(),
        expected
    );
    let different = x.pi(equality(
        succ(x.term().clone(), 41),
        succ(x.term().clone(), 41),
    ));
    assert_eq!(
        run(
            &mut parts,
            &scope,
            &context,
            &different,
            &[Expr::nat_lit(7)]
        )
        .0
        .unwrap(),
        equality(succ(Expr::nat_lit(7), 41), succ(Expr::nat_lit(7), 41))
    );
    assert_eq!(context.inventory.equation_root_count(), 2);
}

#[test]
fn equation_root_sibling_and_restored_then_extended_prefixes_recheck_actual_reads() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let x = scope.try_local(n()).unwrap();
    let value = succ(a.term().clone(), 40);
    let root = x.pi(equality(value.clone(), value));
    for extra_after_restore in [false, true] {
        let (mut parts, mut context) = fixture(&scope, &[]);
        parts
            .charged_extend_external_context(&scope, &mut context, &[a.clone()])
            .unwrap();
        run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
            .0
            .unwrap();
        context.restore(0).unwrap();
        parts
            .charged_extend_external_context(&scope, &mut context, &[b.clone()])
            .unwrap();
        if extra_after_restore {
            let c = scope.try_local(n()).unwrap();
            parts
                .charged_extend_external_context(&scope, &mut context, &[c])
                .unwrap();
        }
        let error = run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
            .0
            .unwrap_err();
        assert!(error.contains(&crate::term_scope::TermScopeError::OutOfScope(a.id()).to_string()));
    }
}

#[test]
fn equation_root_irrelevant_sibling_above_needed_prefix_reuses_but_still_checks_names() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let c = scope.try_local(n()).unwrap();
    let x = scope.try_local(n()).unwrap();
    let value = succ(a.term().clone(), 40);
    let root = x.pi(equality(value.clone(), value.clone())); // x is unused.
    let (mut parts, mut context) = fixture(&scope, &[]);
    parts
        .charged_extend_external_context(&scope, &mut context, &[a])
        .unwrap();
    let needed = context.checkpoint();
    parts
        .charged_extend_external_context(&scope, &mut context, &[b])
        .unwrap();
    let (first, cold) = run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)]);
    assert_eq!(first.unwrap(), equality(value.clone(), value.clone()));
    context.restore(needed).unwrap();
    parts
        .charged_extend_external_context(&scope, &mut context, &[c])
        .unwrap();
    let (second, warm) = run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(7)]);
    assert_eq!(second.unwrap(), equality(value.clone(), value));
    assert!(warm.materialization < cold.materialization);
    assert_eq!(context.inventory.equation_root_count(), 1);
    // The added ID is above the needed prefix but is an UNUSED declaration.
    // The independent name guard must still force canonical shadow refusal.
    parts
        .charged_extend_external_context(&scope, &mut context, &[x.clone()])
        .unwrap();
    let error = run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
        .0
        .unwrap_err();
    assert!(error.contains(&crate::term_scope::TermScopeError::ShadowedLocal(x.id()).to_string()));
}

#[test]
fn equation_root_needed_prefix_includes_fvars_only_in_binder_types_and_let_values() {
    for in_type in [true, false] {
        let mut scope = LocalScope::new();
        let needed = scope
            .try_local(if in_type {
                Expr::sort(Level::succ(Level::zero()))
            } else {
                n()
            })
            .unwrap();
        let spare = scope.try_local(needed.ty().clone()).unwrap();
        let x = scope
            .try_local(if in_type { needed.term().clone() } else { n() })
            .unwrap();
        let value = succ(Expr::nat_lit(0), 40);
        let proposition = equality(value.clone(), value);
        let root = if in_type {
            x.pi(proposition)
        } else {
            let z = scope.try_local(n()).unwrap();
            x.pi(z.let_(needed.term().clone(), proposition))
        };
        let (mut parts, mut context) = fixture(&scope, &[]);
        parts
            .charged_extend_external_context(&scope, &mut context, &[needed.clone()])
            .unwrap();
        // This exercises scope/reference admission; argument typing remains a
        // mandatory later kernel check, not a materialization-cache premise.
        run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
            .0
            .unwrap();
        context.restore(0).unwrap();
        parts
            .charged_extend_external_context(&scope, &mut context, &[spare])
            .unwrap();
        let error = run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
            .0
            .unwrap_err();
        assert!(
            error.contains(&crate::term_scope::TermScopeError::OutOfScope(needed.id()).to_string())
        );
    }
}

#[test]
fn equation_root_complete_input_height_and_deeper_wrapper_refuse_freshly() {
    let mut scope = LocalScope::new();
    let (_, root) = statement(&mut scope);
    for wrap in [false, true] {
        let (mut parts, context) = fixture(&scope, &[]);
        run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
            .0
            .unwrap();
        let candidate = if wrap {
            Expr::app(Expr::const_str("Nat.succ"), root.clone())
        } else {
            root.clone()
        };
        let (result, stats) = scope.close_prepared_equation_forest_fully_with_limits(
            &[candidate],
            &context.inventory,
            TermScopeLimits {
                max_visits: 10_000,
                max_depth: 20,
            },
        );
        assert_eq!(
            result.unwrap_err(),
            crate::scoped_local::LocalScopeError::Closure(
                crate::term_scope::TermScopeError::DepthLimit
            )
        );
        assert!(stats.visits > 0);
    }
}

#[test]
fn equation_root_later_argument_arity_and_substitution_failures_poison_reuse() {
    let mut scope = LocalScope::new();
    let (_, root) = statement(&mut scope);
    for bad in [
        vec![Expr::fvar(FVarId::new(u64::MAX))],
        vec![Expr::nat_lit(0), Expr::nat_lit(1)],
        vec![Expr::bvar(0)],
    ] {
        let (mut parts, context) = fixture(&scope, &[]);
        run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
            .0
            .unwrap();
        let before = parts.counts().3;
        assert!(run(&mut parts, &scope, &context, &root, &bad).0.is_err());
        assert!(parts.counts().3 > before);
        let paid = parts.counts().3;
        assert!(
            run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
                .0
                .unwrap_err()
                .contains(&crate::term_scope::TermScopeError::VisitLimit.to_string())
        );
        assert!(parts.counts().3 >= paid);
    }
}

#[test]
fn equation_root_every_cold_and_warm_payment_prefix_keeps_the_same_limit() {
    let mut scope = LocalScope::new();
    let (_, root) = statement(&mut scope);
    let external = (0..3)
        .map(|_| scope.try_local(n()).unwrap())
        .collect::<Vec<_>>();
    let roots = [root.clone(), Expr::nat_lit(0)];
    let mut complete = false;
    for cap in 0..=512 {
        let (_, context) = fixture(&scope, &external);
        let (result, stats) = scope.close_prepared_equation_forest_fully_with_limits(
            &roots,
            &context.inventory,
            TermScopeLimits {
                max_visits: cap,
                max_depth: 100,
            },
        );
        assert!(stats.visits <= cap);
        if result.is_err() {
            assert_eq!(context.inventory.equation_root_count(), 0);
        } else {
            complete = true;
            assert_eq!(context.inventory.equation_root_count(), 1);
        }
    }
    assert!(
        complete,
        "finite prefixes must also reach the full positive"
    );
    for cap in 0..=32 {
        let (mut parts, context) = fixture(&scope, &external);
        run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
            .0
            .unwrap();
        let (result, stats) = scope.close_prepared_equation_forest_fully_with_limits(
            &roots,
            &context.inventory,
            TermScopeLimits {
                max_visits: cap,
                max_depth: 100,
            },
        );
        assert!(stats.visits <= cap);
        if result.is_err() {
            assert!(
                run(&mut parts, &scope, &context, &root, &[Expr::nat_lit(0)])
                    .0
                    .is_err()
            );
        }
    }
}
