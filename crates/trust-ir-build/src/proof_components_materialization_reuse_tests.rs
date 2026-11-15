// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use clean_kernel::{Environment, Level};
use std::sync::Arc;

#[test]
fn prepared_complete_fvar_envelope_keeps_exact_memo_hits_and_sibling_roots() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let gap = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let outside = scope.try_local(n()).unwrap();
    let mut parts = parts(&scope, 100_000);
    let mut ctx = parts
        .charged_external_context(
            &scope,
            &[a.clone(), gap.clone(), b.clone(), outside.clone()],
        )
        .unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut ctx)
        .unwrap();
    let shared = Arc::new(Expr::apps(
        Expr::const_str("Nat.add"),
        [b.term().clone(), a.term().clone()],
    ));
    let prior = Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
    let parent = chain(
        Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared),
        30,
    );
    let empty = chain(Expr::nat_lit(0), 30);
    parts
        .charged_materialize_external_context_fully(
            &scope,
            &ctx,
            &[prior, parent.clone(), empty.clone()],
        )
        .unwrap();
    let view = parts.external_ordinary_view(&scope, &ctx).unwrap().unwrap();
    let known = view.envelope(&parent).unwrap();
    assert!(known.may_contain(a.id()) && known.may_contain(b.id()) && known.may_contain(gap.id()));
    assert!(!known.may_contain(outside.id()));
    assert!(!view.envelope(&empty).unwrap().may_contain(a.id()));
    assert!(
        view.envelope(outside.term()).is_none(),
        "unpublished inputs are unknown"
    );
}

#[test]
fn prepared_complete_fvar_envelope_propagates_persistent_hits_and_rechecks_sources() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let gap = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let c = scope.try_local(n()).unwrap();
    let mut parts = parts(&scope, 100_000);
    let mut ctx = parts
        .charged_external_context(&scope, &[a.clone(), gap.clone(), b.clone(), c.clone()])
        .unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut ctx)
        .unwrap();
    let left = chain(a.term().clone(), 30);
    parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[left.clone()])
        .unwrap();
    let root = Expr::apps(
        Expr::const_str("Nat.add"),
        [left, chain(b.term().clone(), 30)],
    );
    parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
        .unwrap();
    let before = parts.counts().3;
    assert_eq!(
        parts
            .substitute_materialized_in_external_context(
                &scope,
                &ctx,
                &[(c.clone(), a.term().clone())],
                &[root.clone()]
            )
            .unwrap(),
        vec![root.clone()]
    );
    let outside_work = parts.counts().3 - before;
    let before = parts.counts().3;
    assert_eq!(
        parts
            .substitute_materialized_in_external_context(
                &scope,
                &ctx,
                &[(gap, c.term().clone())],
                &[root.clone()]
            )
            .unwrap(),
        vec![root.clone()]
    );
    assert!(
        parts.counts().3 - before > outside_work,
        "a gap inside the conservative range must still descend"
    );
    let expected = Expr::apps(
        Expr::const_str("Nat.add"),
        [chain(b.term().clone(), 30), chain(a.term().clone(), 30)],
    );
    assert_eq!(
        parts
            .substitute_materialized_in_external_context(
                &scope,
                &ctx,
                &[(a.clone(), b.term().clone()), (b, a.term().clone())],
                &[root]
            )
            .unwrap(),
        vec![expected]
    );
}
fn n() -> Expr {
    Expr::const_str("Nat")
}

#[test]
fn prepared_materialize_then_substitute_prunes_only_the_returned_fully_checked_graph() {
    for optimized in [false, true] {
        let mut scope = LocalScope::new();
        let x = scope.try_local(n()).unwrap();
        let y = scope.try_local(n()).unwrap();
        let mut parts = parts(&scope, 1800);
        let mut ctx = parts
            .charged_external_context(&scope, &[x.clone(), y.clone()])
            .unwrap();
        parts
            .charged_enable_external_materialization_reuse(&scope, &mut ctx)
            .unwrap();
        let root = Expr::apps(
            Expr::const_str("Nat.add"),
            [chain(Expr::nat_lit(0), 300), x.term().clone()],
        );
        parts
            .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
            .unwrap();
        let result = if optimized {
            parts.substitute_materialized_in_external_context(
                &scope,
                &ctx,
                &[(x, y.term().clone())],
                &[root],
            )
        } else {
            parts.substitute_in_external_context(&scope, &ctx, &[(x, y.term().clone())], &[root])
        };
        if optimized {
            assert_eq!(
                result.unwrap(),
                vec![Expr::apps(
                    Expr::const_str("Nat.add"),
                    [chain(Expr::nat_lit(0), 300), y.term().clone()]
                )]
            );
        } else {
            assert!(result.unwrap_err().contains("work limit"));
        }
    }
}

#[test]
fn prepared_materialize_then_substitute_keeps_unused_shadow_and_sibling_refusals() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let c = scope.try_local(n()).unwrap();
    let mut parts = parts(&scope, 100_000);
    let mut ctx = parts
        .charged_external_context(&scope, &[a.clone()])
        .unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut ctx)
        .unwrap();
    let mark = ctx.checkpoint();
    parts
        .charged_extend_external_context(&scope, &mut ctx, &[b.clone()])
        .unwrap();
    let root = chain(b.term().clone(), 80);
    parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
        .unwrap();
    ctx.restore(mark).unwrap();
    parts
        .charged_extend_external_context(&scope, &mut ctx, &[c])
        .unwrap();
    assert_eq!(
        parts
            .substitute_materialized_in_external_context(&scope, &ctx, &[], &[root])
            .unwrap_err(),
        crate::term_scope::TermScopeError::OutOfScope(b.id()).to_string()
    );
    let mut fresh = parts
        .charged_external_context(&scope, &[a, b.clone()])
        .unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut fresh)
        .unwrap();
    let unused = chain(b.lam(Expr::nat_lit(0)), 30);
    assert!(!unused.has_fvar_quick());
    assert_eq!(
        parts
            .substitute_materialized_in_external_context(&scope, &fresh, &[], &[unused])
            .unwrap_err(),
        crate::term_scope::TermScopeError::ShadowedLocal(b.id()).to_string()
    );
    assert!(
        parts
            .substitute_materialized_in_external_context(&scope, &fresh, &[], &[Expr::nat_lit(0)])
            .is_err()
    );
}

#[test]
fn prepared_materialize_then_substitute_checks_full_input_height_before_closed_pruning() {
    let scope = LocalScope::new();
    let mut parts = parts(&scope, 500_000);
    let mut ctx = parts.charged_external_context(&scope, &[]).unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut ctx)
        .unwrap();
    let root = chain(Expr::nat_lit(0), 300);
    parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
        .unwrap();
    assert!(
        parts
            .substitute_materialized_in_external_context(&scope, &ctx, &[], &[chain(root, 16_084)])
            .unwrap_err()
            .contains("depth limit")
    );
}

#[test]
fn prepared_materialize_then_substitute_typed_canonical_result_keeps_complete_replay() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let y = scope.try_local(n()).unwrap();
    let formal = scope.try_local(n()).unwrap();
    let mut parts = parts(&scope, 100_000);
    parts
        .extend_base(OwnedProofCapture::Parameter(x.clone()))
        .unwrap();
    parts
        .extend_base(OwnedProofCapture::Parameter(y.clone()))
        .unwrap();
    let mut ctx = parts
        .charged_external_context(&scope, &[x.clone(), y.clone()])
        .unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut ctx)
        .unwrap();
    let input = formal.lam(Expr::apps(
        Expr::const_str("Nat.add"),
        [x.term().clone(), formal.term().clone()],
    ));
    let actual = parts
        .substitute_materialized_in_external_context(
            &scope,
            &ctx,
            &[(x.clone(), y.term().clone())],
            &[input],
        )
        .unwrap()
        .remove(0);
    assert!(scope.named_binder_id(&actual).is_none());
    let expected = Expr::lam(
        clean_kernel::BinderInfo::Default,
        n(),
        Expr::apps(
            Expr::const_str("Nat.add"),
            [y.term().clone(), Expr::bvar(0)],
        ),
    );
    let ty = Expr::arrow(n(), n());
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty.clone(), actual, expected.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, expected],
    );
    let claim = scope.close(&x.pi(y.pi(goal.clone()))).unwrap();
    let bundle = parts
        .close_scoped(
            &scope,
            x.lam(y.lam(proof)),
            goal,
            crate::term_scope::TermScopeLimits::default(),
        )
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, transported);
    decoded.replay(&env, &transported, 2_000_000).unwrap();
}
fn chain(mut root: Expr, count: usize) -> Expr {
    for _ in 0..count {
        root = Expr::app(Expr::const_str("Nat.succ"), root);
    }
    root
}
fn parts(scope: &LocalScope, operations: usize) -> ProofComponents {
    let mut parts = ProofComponents::new(
        "prepared.materialization.reuse",
        ProofLimits {
            operations,
            ..Default::default()
        },
    );
    parts.set_base(scope, vec![]).unwrap();
    parts
}

#[test]
fn prepared_materialization_reuse_preserves_ancestor_prefix_and_same_length_siblings() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let c = scope.try_local(n()).unwrap();
    let mut parts = parts(&scope, 100_000);
    let mut ctx = parts
        .charged_external_context(&scope, &[a.clone()])
        .unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut ctx)
        .unwrap();
    let root = chain(a.term().clone(), 80);
    let before = parts.counts().3;
    assert_eq!(
        parts
            .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
            .unwrap(),
        vec![root.clone()]
    );
    let cold = parts.counts().3 - before;
    let mark = ctx.checkpoint();
    parts
        .charged_extend_external_context(&scope, &mut ctx, &[b.clone()])
        .unwrap();
    let before = parts.counts().3;
    parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
        .unwrap();
    assert!(parts.counts().3 - before < cold);
    let sibling_root = chain(b.term().clone(), 80);
    parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[sibling_root.clone()])
        .unwrap();
    ctx.restore(mark).unwrap();
    parts
        .charged_extend_external_context(&scope, &mut ctx, &[c])
        .unwrap();
    let before = parts.counts().3;
    parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[root])
        .unwrap();
    assert!(parts.counts().3 - before < cold);
    let error = parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[sibling_root])
        .unwrap_err();
    assert_eq!(
        error,
        crate::term_scope::TermScopeError::OutOfScope(b.id()).to_string()
    );
    assert!(
        parts
            .charged_materialize_external_context_fully(&scope, &ctx, &[Expr::nat_lit(0)])
            .is_err()
    );
}

#[test]
fn prepared_materialization_reuse_restore_then_reextend_never_recycles_generation() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let mut parts = parts(&scope, 100_000);
    let mut ctx = parts.charged_external_context(&scope, &[a]).unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut ctx)
        .unwrap();
    let mark = ctx.checkpoint();
    parts
        .charged_extend_external_context(&scope, &mut ctx, &[b.clone()])
        .unwrap();
    let root = chain(b.term().clone(), 80);
    let before = parts.counts().3;
    parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
        .unwrap();
    let cold = parts.counts().3 - before;
    let before = parts.counts().3;
    parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
        .unwrap();
    let hot = parts.counts().3 - before;
    assert!(hot < cold);
    ctx.restore(mark).unwrap();
    parts
        .charged_extend_external_context(&scope, &mut ctx, &[b])
        .unwrap();
    let before = parts.counts().3;
    parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[root])
        .unwrap();
    assert!(parts.counts().3 - before > hot);
}

#[test]
fn prepared_materialization_reuse_never_hides_unused_binder_or_same_spelled_external_shadow() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let mut parts = parts(&scope, 100_000);
    let mut ctx = parts.charged_external_context(&scope, &[a]).unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut ctx)
        .unwrap();
    let ordinary = chain(
        Expr::let_named(
            Name::from_string("same"),
            n(),
            Expr::nat_lit(0),
            Expr::bvar(0),
            false,
        ),
        30,
    );
    let named = chain(
        b.let_named(
            Name::from_string("same"),
            Expr::nat_lit(0),
            Expr::nat_lit(0),
            false,
        ),
        30,
    );
    parts
        .charged_materialize_external_context_fully(
            &scope,
            &ctx,
            &[ordinary.clone(), named.clone()],
        )
        .unwrap();
    parts
        .charged_extend_external_context(&scope, &mut ctx, &[b.clone()])
        .unwrap();
    assert_eq!(
        parts
            .charged_materialize_external_context_fully(&scope, &ctx, &[ordinary.clone()])
            .unwrap(),
        vec![ordinary]
    );
    assert_eq!(
        parts
            .charged_materialize_external_context_fully(&scope, &ctx, &[named])
            .unwrap_err(),
        crate::term_scope::TermScopeError::ShadowedLocal(b.id()).to_string()
    );
}

#[test]
fn prepared_materialization_reuse_checks_full_height_and_failed_enclosing_attempts() {
    let scope = LocalScope::new();
    let mut parts = parts(&scope, 500_000);
    let mut ctx = parts.charged_external_context(&scope, &[]).unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut ctx)
        .unwrap();
    let root = chain(Expr::nat_lit(0), 300);
    parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
        .unwrap();
    let deep = chain(root, 16_084);
    assert!(
        parts
            .charged_materialize_external_context_fully(&scope, &ctx, &[deep])
            .unwrap_err()
            .contains("depth limit")
    );
    assert!(
        parts
            .charged_enable_external_materialization_reuse(&scope, &mut ctx)
            .is_err()
    );
    let mut fresh = parts.charged_external_context(&scope, &[]).unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut fresh)
        .unwrap();
    let wrong_arity = chain(Expr::nat_lit(0), 30);
    assert!(
        parts
            .charged_instantiate_in_external_context(
                &scope,
                &fresh,
                &wrong_arity,
                &[Expr::nat_lit(0)]
            )
            .unwrap_err()
            .contains("arity")
    );
    assert!(
        parts
            .charged_materialize_external_context_fully(&scope, &fresh, &[wrong_arity])
            .is_err()
    );
}

#[test]
fn prepared_materialization_reuse_never_transfers_owner_or_changed_graph_admission() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let mut owner = parts(&scope, 100_000);
    let mut ctx = owner
        .charged_external_context(&scope, &[a.clone()])
        .unwrap();
    owner
        .charged_enable_external_materialization_reuse(&scope, &mut ctx)
        .unwrap();
    let root = chain(a.term().clone(), 80);
    owner
        .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
        .unwrap();
    let mut other = parts(&scope, 100_000);
    assert!(
        other
            .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
            .is_err()
    );
    let mut foreign = LocalScope::new();
    assert_eq!(foreign.try_local(n()).unwrap().id(), a.id());
    assert!(
        owner
            .charged_materialize_external_context_fully(&foreign, &ctx, &[root.clone()])
            .is_err()
    );
    owner
        .charged_materialize_external_context_fully(&scope, &ctx, &[root])
        .unwrap();
    assert!(
        owner
            .charged_materialize_external_context_fully(
                &scope,
                &ctx,
                &[chain(b.term().clone(), 80)]
            )
            .is_err()
    );
}

#[test]
fn prepared_materialization_reuse_typed_result_requires_original_decoded_kernel_replay() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    let mut scope = LocalScope::new();
    let input = scope.try_local(n()).unwrap();
    let mut parts = parts(&scope, 100_000);
    parts
        .extend_base(OwnedProofCapture::Parameter(input.clone()))
        .unwrap();
    let mut ctx = parts
        .charged_external_context(&scope, &[input.clone()])
        .unwrap();
    parts
        .charged_enable_external_materialization_reuse(&scope, &mut ctx)
        .unwrap();
    let root = chain(input.term().clone(), 80);
    let first = parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[root.clone()])
        .unwrap()
        .remove(0);
    let second = parts
        .charged_materialize_external_context_fully(&scope, &ctx, &[root])
        .unwrap()
        .remove(0);
    assert_eq!(first, second);
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [n(), first.clone(), second],
    );
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [n(), first],
    );
    let claim = scope.close(&input.pi(goal.clone())).unwrap();
    let bundle = parts
        .close_scoped(
            &scope,
            input.lam(proof),
            goal,
            crate::term_scope::TermScopeLimits::default(),
        )
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, transported);
    decoded.replay(&env, &transported, 2_000_000).unwrap();
}
