use super::*;
use crate::{proof_assembly::ProofLimits, scoped_local::LocalScope};
use clean_kernel::{Environment, Expr, Level, Name};
use std::sync::Arc;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    env
}

#[test]
fn ambient_parameters_do_not_spend_dynamic_capture_union_work() {
    let mut scope = LocalScope::new();
    let mut ambient = Vec::new();
    for _ in 0..20 {
        ambient.push(scope.try_local(c("Nat")).unwrap());
        // Keep the ambient parameters in distinct sparse dependency words.
        for _ in 0..63 {
            let _ = scope.try_local(c("Nat")).unwrap();
        }
    }
    let dynamic = scope.try_local(c("Nat")).unwrap();
    let mut term = dynamic.term().clone();
    for parameter in &ambient {
        term = Expr::apps(c("Nat.add"), [term, parameter.term().clone()]);
    }
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c("Nat"), term.clone(), term.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [c("Nat"), term],
    );
    let limits = ProofLimits {
        operations: 128,
        ..ProofLimits::default()
    };
    let mut plan = ProofComponents::new("Ambient", limits);
    plan.set_base(
        &scope,
        ambient
            .iter()
            .cloned()
            .map(OwnedProofCapture::Parameter)
            .collect(),
    )
    .unwrap();
    let reference = plan
        .bind_scoped(
            &mut scope,
            &[OwnedProofCapture::Parameter(dynamic.clone())],
            eq.clone(),
            proof,
        )
        .expect("ambient words must not consume the dynamic dependency budget");
    assert_eq!(plan.counts().2, ambient.len() + 1);
    let open_goal = dynamic.pi(eq);
    let mut full_goal = open_goal.clone();
    let mut root = dynamic.lam(reference);
    for parameter in ambient.iter().rev() {
        root = parameter.lam(root);
        full_goal = parameter.pi(full_goal);
    }
    let external = scope.close(&full_goal).unwrap();
    let artifact = plan
        .close_scoped(&scope, root, open_goal, scope.closing_limits())
        .unwrap();
    artifact.replay(&env(), &external, 2_000_000).unwrap();
    let mut corrupt = artifact.clone();
    corrupt.declarations.last_mut().unwrap().value = Some(c("True.intro"));
    assert!(corrupt.replay(&env(), &external, 2_000_000).is_err());
}

#[test]
fn ambient_growth_preserves_cached_dynamic_capture_dependencies() {
    let mut scope = LocalScope::new();
    let ambient = scope.try_local(c("Nat")).unwrap();
    let dynamic = scope.try_local(c("Nat")).unwrap();
    let term = Expr::apps(
        c("Nat.add"),
        [ambient.term().clone(), dynamic.term().clone()],
    );
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c("Nat"), term.clone(), term.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [c("Nat"), term],
    );
    let mut plan = ProofComponents::new("Growing", ProofLimits::default());
    plan.set_base(&scope, vec![]).unwrap();
    // Cache the original dependency set before the later ambient extension.
    // Final closure, not this untrusted construction, checks the complete base.
    let _first_reference = plan
        .bind_scoped(
            &mut scope,
            &[OwnedProofCapture::Parameter(dynamic.clone())],
            eq.clone(),
            proof.clone(),
        )
        .unwrap();
    plan.extend_base(OwnedProofCapture::Parameter(ambient.clone()))
        .unwrap();
    let reference = plan
        .bind_scoped(
            &mut scope,
            &[
                OwnedProofCapture::Parameter(ambient.clone()),
                OwnedProofCapture::Parameter(dynamic.clone()),
            ],
            eq.clone(),
            proof,
        )
        .unwrap();
    assert_eq!(
        plan.counts().2,
        3,
        "each component still captures the dynamic parameter"
    );
    let goal = dynamic.pi(eq);
    let external = scope.close(&ambient.pi(goal.clone())).unwrap();
    let root = ambient.lam(dynamic.lam(reference));
    let artifact = plan
        .close_scoped(&scope, root, goal, scope.closing_limits())
        .unwrap();
    artifact.replay(&env(), &external, 2_000_000).unwrap();
    let mut missing = artifact.clone();
    missing.declarations.remove(0);
    missing.outer_count -= 1;
    assert!(missing.replay(&env(), &external, 2_000_000).is_err());
}

#[test]
fn internal_binders_are_not_lifted_as_external_captures() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(c("Nat")).unwrap();
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c("Nat"), x.term().clone(), x.term().clone()],
    );
    let refl = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [c("Nat"), x.term().clone()],
    );
    let goal = x.pi(eq);
    let proof = x.lam(refl);
    let mut plan = ProofComponents::new("Internal", ProofLimits::default());
    plan.set_base(&scope, vec![]).unwrap();
    let reference = plan
        .bind_scoped(
            &mut scope,
            &[OwnedProofCapture::Parameter(x)],
            goal.clone(),
            proof,
        )
        .unwrap();
    assert_eq!(plan.counts().2, 0, "the bound local is not a free capture");
    let external = scope.close(&goal).unwrap();
    let artifact = plan
        .close_scoped(&scope, reference, goal, scope.closing_limits())
        .unwrap();
    artifact.replay(&env(), &external, 2_000_000).unwrap();
}

#[test]
fn exact_mixed_telescope_roundtrips_and_rejects_corrupted_values() {
    let env = env();
    let mut scope = LocalScope::new();
    let alpha = scope.try_local(Expr::type_()).unwrap();
    let x = scope.try_local(alpha.term().clone()).unwrap();
    let alias = scope.try_local(alpha.term().clone()).unwrap();
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [alpha.term().clone(), alias.term().clone(), x.term().clone()],
    );
    let h = scope.try_local(eq.clone()).unwrap();
    let captures = vec![
        OwnedProofCapture::Parameter(alpha.clone()),
        OwnedProofCapture::Parameter(x.clone()),
        OwnedProofCapture::Definition {
            local: alias.clone(),
            value: Arc::new(x.term().clone()),
        },
        OwnedProofCapture::Parameter(h.clone()),
    ];
    let mut plan = ProofComponents::new("Mixed", ProofLimits::default());
    plan.set_base(&scope, captures).unwrap();
    let reference = plan
        .bind_scoped(&mut scope, &[], eq.clone(), h.term().clone())
        .unwrap();
    let root = alpha.lam(x.lam(alias.let_(x.term().clone(), h.lam(reference))));
    let external = scope
        .close(&alpha.pi(x.pi(alias.let_(x.term().clone(), h.pi(eq.clone())))))
        .unwrap();
    let artifact = plan
        .close_scoped(&scope, root, eq, scope.closing_limits())
        .unwrap();
    let wire = artifact.encode_with_claim(&external).unwrap();
    let (decoded, claim) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
    assert_eq!(claim, external);
    assert_eq!(decoded.outer_count, 4);
    decoded.replay(&env, &external, 2_000_000).unwrap();
    let mut wrong = decoded.clone();
    wrong.declarations.last_mut().unwrap().value = Some(c("True.intro"));
    assert!(wrong.replay(&env, &external, 2_000_000).is_err());
    let mut forward = decoded.clone();
    forward.declarations.swap(0, 1);
    assert!(forward.replay(&env, &external, 2_000_000).is_err());
    let mut duplicate = decoded.clone();
    duplicate.declarations[1].id = duplicate.declarations[0].id;
    assert!(duplicate.replay(&env, &external, 2_000_000).is_err());
    let mut missing = decoded.clone();
    missing.declarations.pop();
    assert!(missing.replay(&env, &external, 2_000_000).is_err());
    assert!(decoded.replay(&env, &external, 1).is_err());
    assert!(ScopedProofComponentBundle::decode_with_claim(&wire[..wire.len() - 1]).is_err());
}

#[test]
fn external_prefix_growth_preserves_real_shadow_guards_and_one_budget() {
    let mut scope = LocalScope::new();
    let future = scope.try_local(c("Nat")).unwrap();
    let lambda = future.lam(future.term().clone());
    let (result, work) = scope.close_external_forest(
        &[lambda.clone(), future.term().clone()],
        std::slice::from_ref(&future),
        &[0, 1],
    );
    let roots = result.unwrap();
    assert_eq!(work.completed_roots, 2);
    assert_eq!(roots[1], *future.term());
    let shared = Arc::new(lambda);
    let (shadow, work) = scope.close_external_forest(
        &[
            Expr::app_arc(Arc::new(c("id")), shared.clone()),
            Expr::app_arc(Arc::new(c("other")), shared),
        ],
        &[future],
        &[0, 1],
    );
    assert!(
        shadow.is_err(),
        "a cached earlier closed binder cannot shadow a later external"
    );
    assert_eq!(work.completed_roots, 1);
    let limited = LocalScope::with_limits(crate::scoped_local::LocalScopeLimits {
        closing: crate::term_scope::TermScopeLimits {
            max_visits: 2,
            max_depth: 16,
        },
        ..Default::default()
    });
    let (refused, work) =
        limited.close_external_forest(&[c("Nat"), c("Nat"), c("Nat")], &[], &[0, 0, 0]);
    assert!(refused.is_err());
    assert_eq!(work.visits, 2);
    assert_eq!(work.completed_roots, 2);
}

#[test]
fn foreign_capture_owner_is_refused() {
    let owner = LocalScope::new();
    let mut foreign = LocalScope::new();
    let local = foreign.try_local(Expr::type_()).unwrap();
    let mut plan = ProofComponents::new("Foreign", ProofLimits::default());
    assert!(
        plan.set_base(&owner, vec![OwnedProofCapture::Parameter(local.clone())])
            .is_err()
    );
    plan.set_base(&owner, vec![]).unwrap();
    assert!(
        plan.extend_base(OwnedProofCapture::Parameter(local.clone()))
            .is_err()
    );
    assert!(
        plan.extend_base_definition(OwnedProofCapture::Parameter(local.clone()))
            .is_err()
    );
    let (result, _) = owner.close_external_forest(&[local.term().clone()], &[local], &[1]);
    assert!(result.is_err());
}

#[test]
fn replay_rejects_untracked_locals_new_assumptions_and_nested_budget_ownership() {
    let env = env();
    let base = ScopedProofComponentBundle {
        declarations: vec![],
        outer_count: 0,
        root: c("True.intro"),
        goal: c("True"),
        work: None,
    };
    base.replay(&env, &c("True"), 10_000).unwrap();
    let mut untracked = base.clone();
    untracked.root = Expr::fvar(clean_kernel::expr::FVarId::new(123));
    assert!(untracked.replay(&env, &c("True"), 10_000).is_err());
    let mut assumed = base.clone();
    assumed.declarations.push(ScopedProofDeclaration {
        id: clean_kernel::expr::FVarId::new(123),
        name: Name::anon(),
        binder: clean_kernel::BinderInfo::Default.into(),
        non_dep: false,
        type_: c("False"),
        value: None,
    });
    assert!(assumed.replay(&env, &c("True"), 10_000).is_err());
    assumed.outer_count = 2;
    assert!(assumed.replay(&env, &c("True"), 10_000).is_err());
    assumed.outer_count = 1;
    assumed.declarations[0].id = clean_kernel::expr::FVarId::new(1 << 63);
    assert!(assumed.replay(&env, &c("True"), 10_000).is_err());
    struct Budget;
    impl Drop for Budget {
        fn drop(&mut self) {
            clean_kernel::tc::clear_declaration_budget();
        }
    }
    clean_kernel::tc::set_declaration_budget(47);
    let _budget = Budget;
    assert!(base.replay(&env, &c("True"), 10_000).is_err());
    assert_eq!(
        clean_kernel::tc::declaration_budget_limit(),
        47,
        "a nested replay must not clear or replace its caller's budget"
    );
}

#[test]
fn opaque_normalization_preserves_original_definition_and_complete_replay() {
    let mut scope = LocalScope::new();
    let local = scope.try_local(c("Nat")).unwrap();
    let value = Expr::nat_lit(7);
    let mut plan = ProofComponents::new("OpaqueOriginal", ProofLimits::default());
    plan.set_base(
        &scope,
        vec![OwnedProofCapture::Definition {
            local: local.clone(),
            value: Arc::new(value.clone()),
        }],
    )
    .unwrap();
    let inputs = [local.term().clone()];
    let (plain, _) = scope.close_external_forest(&inputs, std::slice::from_ref(&local), &[1]);
    let plain = plain.unwrap().remove(0);
    let (ordinary, _, ordinary_work) = plan
        .untrusted_normalization_context(&scope, &inputs)
        .unwrap();
    let environment = env();
    assert_eq!(
        clean_kernel::TypeChecker::with_context(&environment, ordinary).whnf(&plain),
        value
    );
    let before = plan.counts();
    let (opaque, _, work) = plan
        .untrusted_normalization_context_with_opaque(&scope, &inputs, std::slice::from_ref(&local))
        .unwrap();
    assert_eq!(
        clean_kernel::TypeChecker::with_context(&environment, opaque).whnf(&plain),
        plain
    );
    assert!(work >= 5);
    assert!(ordinary_work > 0);
    assert_eq!(plan.counts(), before);
    let full_claim = scope.close(&local.let_(value.clone(), c("True"))).unwrap();
    assert!(
        clean_kernel::TypeChecker::new(&environment)
            .infer_sort(&full_claim)
            .unwrap()
            .is_zero()
    );
    let bundle = plan
        .close_scoped(
            &scope,
            local.let_(value.clone(), c("True.intro")),
            c("True"),
            scope.closing_limits(),
        )
        .unwrap();
    let bytes = bundle.encode_with_claim(&full_claim).unwrap();
    let (bundle, claim) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, full_claim);
    assert_eq!(bundle.declarations.len(), 1);
    assert_eq!(bundle.declarations[0].value, Some(value));
    bundle.replay(&environment, &full_claim, 2_000_000).unwrap();
}

#[test]
fn opaque_normalization_refuses_foreign_duplicate_absent_and_parameter_handles() {
    let mut scope = LocalScope::new();
    let local = scope.try_local(c("Nat")).unwrap();
    let parameter = scope.try_local(c("Nat")).unwrap();
    let absent = scope.try_local(c("Nat")).unwrap();
    let mut other = LocalScope::new();
    let foreign = other.try_local(c("Nat")).unwrap();
    let mut plan = ProofComponents::new("OpaqueOwnership", ProofLimits::default());
    plan.set_base(
        &scope,
        vec![
            OwnedProofCapture::Definition {
                local: local.clone(),
                value: Arc::new(Expr::nat_lit(7)),
            },
            OwnedProofCapture::Parameter(parameter.clone()),
        ],
    )
    .unwrap();
    let before = plan.counts();
    for requested in [
        vec![foreign],
        vec![local.clone(), local.clone()],
        vec![absent],
        vec![parameter],
    ] {
        assert!(
            plan.untrusted_normalization_context_with_opaque(
                &scope,
                &[local.term().clone()],
                &requested
            )
            .is_err()
        );
        assert_eq!(plan.counts(), before);
    }
    let (_, _, _) = plan
        .untrusted_normalization_context_with_opaque(&scope, &[local.term().clone()], &[local])
        .unwrap();
}

#[test]
fn opaque_normalization_charges_inventory_before_publication() {
    let mut scope = LocalScope::new();
    let local = scope.try_local(c("Nat")).unwrap();
    let mut plan = ProofComponents::new(
        "OpaqueBudget",
        ProofLimits {
            operations: 1,
            ..Default::default()
        },
    );
    plan.set_base(
        &scope,
        vec![OwnedProofCapture::Definition {
            local: local.clone(),
            value: Arc::new(Expr::nat_lit(7)),
        }],
    )
    .unwrap();
    let before = plan.counts();
    assert!(
        matches!(plan.untrusted_normalization_context_with_opaque(&scope,&[local.term().clone()],&[local]),Err(error) if error.contains("inventory operation limit"))
    );
    assert_eq!(plan.counts(), before);
}

#[test]
fn opaque_normalization_does_not_hide_original_type_capture_order() {
    let mut scope = LocalScope::new();
    let ty = scope.try_local(Expr::type_()).unwrap();
    let local = scope.try_local(ty.term().clone()).unwrap();
    let mut plan = ProofComponents::new("OpaqueTypeOrder", ProofLimits::default());
    plan.set_base(
        &scope,
        vec![
            OwnedProofCapture::Definition {
                local: local.clone(),
                value: Arc::new(Expr::nat_lit(7)),
            },
            OwnedProofCapture::Parameter(ty),
        ],
    )
    .unwrap();
    let error = plan
        .untrusted_normalization_context_with_opaque(&scope, &[local.term().clone()], &[local])
        .err()
        .expect("opacity cannot admit a later type dependency");
    assert!(
        error.contains("scope") || error.contains("local"),
        "{error}"
    );
}

#[test]
fn opaque_normalization_retains_unused_cold_invalid_original_for_complete_rejection() {
    let mut scope = LocalScope::new();
    let local = scope.try_local(c("Nat")).unwrap();
    let mut plan = ProofComponents::new("OpaqueColdInvalid", ProofLimits::default());
    plan.set_base(
        &scope,
        vec![OwnedProofCapture::Definition {
            local: local.clone(),
            value: Arc::new(c("True.intro")),
        }],
    )
    .unwrap();
    let (opaque, _, _) = plan
        .untrusted_normalization_context_with_opaque(
            &scope,
            &[local.term().clone()],
            std::slice::from_ref(&local),
        )
        .unwrap();
    let environment = env();
    let (plain, _) =
        scope.close_external_forest(&[local.term().clone()], std::slice::from_ref(&local), &[1]);
    let plain = plain.unwrap().remove(0);
    assert_eq!(
        clean_kernel::TypeChecker::with_context(&environment, opaque).whnf(&plain),
        plain
    );
    // Keep the ORIGINAL invalid declaration in the literal root/claim prefix;
    // it is not a false semantic theorem or a new parameter assumption.
    let full_claim = scope
        .close(&local.let_(c("True.intro"), c("True")))
        .unwrap();
    let bundle = plan
        .close_scoped(
            &scope,
            local.let_(c("True.intro"), c("True.intro")),
            c("True"),
            scope.closing_limits(),
        )
        .unwrap();
    let bytes = bundle.encode_with_claim(&full_claim).unwrap();
    let (bundle, claim) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, full_claim);
    assert_eq!(bundle.declarations.len(), 1);
    assert_eq!(bundle.declarations[0].value, Some(c("True.intro")));
    let error = bundle
        .replay(&environment, &full_claim, 2_000_000)
        .err()
        .expect("the original bad definition is mandatory even when unused");
    assert!(
        error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
        "{error}"
    );
}
