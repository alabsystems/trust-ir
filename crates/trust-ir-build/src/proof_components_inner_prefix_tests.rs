// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::term_scope::TermScopeLimits;
use clean_kernel::{Environment, Level};
fn n() -> Expr {
    Expr::const_str("Nat")
}
fn chain(mut child: Arc<Expr>, count: usize) -> Expr {
    for _ in 0..count {
        child = Arc::new(Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), child));
    }
    child.as_ref().clone()
}
fn equality(value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [n(), value.clone(), value],
    )
}
fn fixture(scope: &LocalScope) -> (ProofComponents, ExternalContext) {
    let mut parts = ProofComponents::new("inner.prefix", ProofLimits::default());
    parts.set_base(scope, vec![]).unwrap();
    let mut context = parts.charged_external_context(scope, &[]).unwrap();
    parts
        .charged_enable_external_materialization_reuse(scope, &mut context)
        .unwrap();
    (parts, context)
}

#[test]
fn inner_materialization_reuses_irrelevant_siblings_and_keeps_original_decoded_claim() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let c = scope.try_local(n()).unwrap();
    let root = chain(Arc::new(a.term().clone()), 40);
    let goal = a.pi(equality(root.clone()));
    let claim = scope.close(&goal).unwrap();
    let (mut parts, mut context) = fixture(&scope);
    parts
        .charged_extend_external_context(&scope, &mut context, std::slice::from_ref(&a))
        .unwrap();
    let needed = context.checkpoint();
    parts
        .charged_extend_external_context(&scope, &mut context, &[b])
        .unwrap();
    let before = parts.counts().3;
    assert_eq!(
        parts
            .charged_materialize_external_context_fully(
                &scope,
                &context,
                std::slice::from_ref(&root),
            )
            .unwrap(),
        vec![root.clone()]
    );
    let cold = parts.counts().3 - before;
    context.restore(needed).unwrap();
    parts
        .charged_extend_external_context(&scope, &mut context, &[c])
        .unwrap();
    let before = parts.counts().3;
    assert_eq!(
        parts
            .charged_materialize_external_context_fully(
                &scope,
                &context,
                std::slice::from_ref(&root),
            )
            .unwrap(),
        vec![root.clone()]
    );
    assert!(parts.counts().3 - before < cold);
    let proof = a.lam(Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [n(), root],
    ));
    let bundle = parts
        .close_scoped(&scope, proof, goal, TermScopeLimits::default())
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(transported, claim);
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    decoded.replay(&env, &transported, 2_000_000).unwrap();
}

#[test]
fn inner_materialization_propagates_required_prefix_through_both_memo_routes() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    // Height two uses the fresh per-call pointer memo; height ten can use the
    // persistent completed child. Distinct wrapper Arcs prevent another hit
    // from hiding the specific shared child's required-prefix propagation.
    for height in [2, 10] {
        let shared = Arc::new(chain(Arc::new(a.term().clone()), height - 1));
        let first = chain(shared.clone(), 24);
        let second = chain(shared, 24);
        let (mut parts, mut context) = fixture(&scope);
        parts
            .charged_extend_external_context(&scope, &mut context, std::slice::from_ref(&a))
            .unwrap();
        parts
            .charged_materialize_external_context_fully(&scope, &context, &[first, second.clone()])
            .unwrap();
        context.restore(0).unwrap();
        parts
            .charged_extend_external_context(&scope, &mut context, std::slice::from_ref(&b))
            .unwrap();
        let error = parts
            .charged_materialize_external_context_fully(&scope, &context, &[second])
            .unwrap_err();
        assert!(error.contains(&crate::term_scope::TermScopeError::OutOfScope(a.id()).to_string()));
    }
}

#[test]
fn position_index_enable_extend_and_prepaid_restore_keep_every_finite_bill() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let c = scope.try_local(n()).unwrap();
    let mut completed = false;
    for cap in 0..=64 {
        let mut parts = ProofComponents::new(
            "position.prefix",
            ProofLimits {
                operations: cap,
                ..Default::default()
            },
        );
        parts.set_base(&scope, vec![]).unwrap();
        let Ok(mut context) = parts.charged_external_context(&scope, std::slice::from_ref(&a))
        else {
            assert!(parts.counts().3 <= cap);
            continue;
        };
        assert!(!context.inventory.reuses_materialization());
        if parts
            .charged_enable_external_materialization_reuse(&scope, &mut context)
            .is_err()
        {
            assert!(!context.inventory.reuses_materialization());
            assert!(parts.counts().3 <= cap);
            continue;
        }
        let checkpoint = context.checkpoint();
        let extended =
            parts.charged_extend_external_context(&scope, &mut context, &[b.clone(), c.clone()]);
        assert!(parts.counts().3 <= cap);
        assert_eq!(parts.counts().0, 0);
        if extended.is_err() {
            assert_eq!(context.checkpoint(), checkpoint);
            let ids = context.inventory.ids_for(&scope).unwrap();
            assert!(ids.contains(&a.id()));
            assert!(!ids.contains(&b.id()) && !ids.contains(&c.id()));
        } else {
            completed = true;
            let paid = parts.counts().3;
            context.restore(checkpoint).unwrap();
            assert_eq!(parts.counts().3, paid, "suffix removal was already prepaid");
            let (result, _) = scope.close_prepared_external_forest_fully_with_limits(
                &[c.term().clone()],
                &context.inventory,
                TermScopeLimits::default(),
            );
            assert_eq!(
                result.unwrap_err(),
                crate::scoped_local::LocalScopeError::Closure(
                    crate::term_scope::TermScopeError::OutOfScope(c.id())
                )
            );
        }
    }
    assert!(completed);
}
