// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Ordinary conditional-result consumer of actual scoped substitution.
//! The complete raw result and original declaration stay in rooted replay.
use clean_kernel::{Environment, Expr, ExprKind, Level, Name};
use trust_ir_build::proof_assembly::ProofLimits;
use trust_ir_build::proof_components::{
    OwnedProofCapture, ProofComponents, ScopedProofComponentBundle,
};
use trust_ir_build::scoped_local::{LocalScope, LocalScopeLimits, ScopedLocal};

fn at(name: &str, levels: Vec<Level>, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), levels), args)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn status() -> Expr {
    at("Except", vec![Level::zero(); 2], [nat(), nat()])
}
fn raw_type() -> Expr {
    at("Prod", vec![Level::zero(); 2], [nat(), status()])
}
fn add(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [x, y])
}
fn pair(state: Expr, value: Expr) -> Expr {
    at(
        "Prod.mk",
        vec![Level::zero(); 2],
        [nat(), status(), state, value],
    )
}
fn outcome(error: bool, value: Expr) -> Expr {
    at(
        if error { "Except.error" } else { "Except.ok" },
        vec![Level::zero(); 2],
        [nat(), nat(), value],
    )
}
fn projection(first: bool, raw: Expr) -> Expr {
    at(
        if first { "Prod.fst" } else { "Prod.snd" },
        vec![Level::zero(); 2],
        [nat(), status(), raw],
    )
}
fn eq(left: Expr, right: Expr) -> Expr {
    at(
        "Eq",
        vec![Level::succ(Level::zero())],
        [raw_type(), left, right],
    )
}
fn refl(value: Expr) -> Expr {
    at(
        "Eq.refl",
        vec![Level::succ(Level::zero())],
        [raw_type(), value],
    )
}
fn observe(scope: &mut LocalScope, raw: Expr, payload: Expr, depth: usize) -> Expr {
    if depth == 0 {
        return pair(
            add(projection(true, raw), payload.clone()),
            outcome(false, payload),
        );
    }
    let major = scope.try_local(status()).unwrap();
    let error = scope.try_local(nat()).unwrap();
    let value = scope.try_local(nat()).unwrap();
    let failed = observe(
        scope,
        raw.clone(),
        add(payload.clone(), error.term().clone()),
        depth - 1,
    );
    let normal = observe(
        scope,
        raw.clone(),
        add(add(payload, value.term().clone()), Expr::nat_lit(1)),
        depth - 1,
    );
    at(
        "Except.rec",
        vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
        [
            nat(),
            nat(),
            major.lam(raw_type()),
            error.lam(failed),
            value.lam(normal),
            projection(false, raw),
        ],
    )
}

#[test]
fn conditional_result_source_survives_applied_function_substitution() {
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env.init_nat().unwrap();
    env.init_prod().unwrap();
    env.init_except_t().unwrap();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    for (reduce, depth) in [
        (false, 0),
        (true, 0),
        (false, 4),
        (true, 4),
        (false, 8),
        (true, 8),
    ] {
        let mut scope = LocalScope::new();
        let flag = scope.try_local(Expr::const_str("Bool")).unwrap();
        let initial = scope.try_local(nat()).unwrap();
        let mut parts =
            ProofComponents::new("ordinary.application.substitution", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(flag.clone()),
                    OwnedProofCapture::Parameter(initial.clone()),
                ],
            )
            .unwrap();
        let input = scope.try_local(nat()).unwrap();
        let selector = scope.try_local(Expr::const_str("Bool")).unwrap();
        let body = input.lam(at(
            "Bool.rec",
            vec![Level::succ(Level::zero())],
            [
                selector.lam(raw_type()),
                pair(input.term().clone(), outcome(true, Expr::nat_lit(0))),
                pair(
                    add(input.term().clone(), Expr::nat_lit(1)),
                    outcome(false, input.term().clone()),
                ),
                flag.term().clone(),
            ],
        ));
        let function = parts
            .bind_scoped_owned(
                &mut scope,
                &[],
                Expr::arrow(nat(), raw_type()),
                body.clone(),
            )
            .unwrap();
        let raw = Expr::app(function.reference.clone(), initial.term().clone());
        let observation = observe(&mut scope, raw.clone(), Expr::nat_lit(0), depth);
        let unused = scope.try_local(nat()).unwrap();
        let external = [flag.clone(), initial.clone(), function.local.clone()];
        let bindings = [(function.local.clone(), unused.lam(raw))];
        let mut candidate = if reduce {
            parts.substitute_scoped_applications(
                &scope,
                &external,
                &bindings,
                &[observation.clone()],
            )
        } else {
            parts.substitute_scoped_terms(&scope, &external, &bindings, &[observation.clone()])
        }
        .unwrap();
        let endpoint = candidate.remove(0);
        let producer_work = parts.counts().3;
        let claim = scope
            .close(
                &flag.pi(initial.pi(function
                    .local
                    .let_(body.clone(), eq(observation.clone(), observation.clone())))),
            )
            .unwrap();
        let goal = eq(endpoint, observation.clone());
        let bundle = parts
            .close_scoped(
                &scope,
                flag.lam(initial.lam(refl(observation.clone()))),
                goal,
                Default::default(),
            )
            .unwrap();
        // Keep the exact proof while changing the complete raw endpoint. The
        // independent claim agrees with that changed goal, so a refusal must
        // come from proof checking rather than mismatched claim transport.
        let wrong = pair(
            add(projection(true, observation.clone()), Expr::nat_lit(1)),
            projection(false, observation.clone()),
        );
        let wrong_claim = scope
            .close(
                &flag.pi(initial.pi(function
                    .local
                    .let_(body, eq(observation.clone(), wrong.clone())))),
            )
            .unwrap();
        let wrong = scope
            .close_external_forest(&[wrong], &external, &[external.len()])
            .0
            .unwrap()
            .remove(0);
        let mut mutant = bundle.clone();
        let ExprKind::App(eq_left, _) = mutant.goal.kind() else {
            panic!("expected equality goal");
        };
        mutant.goal = Expr::app_arc(eq_left.clone(), std::sync::Arc::new(wrong));
        let wrong_wire = mutant.encode_with_claim(&wrong_claim).unwrap();
        let (mutant, wrong_claim) =
            ScopedProofComponentBundle::decode_with_claim(&wrong_wire).unwrap();
        let refused = mutant.replay(&env, &wrong_claim, 2_000_000);
        assert!(
            refused.is_err(),
            "same proof accepted a changed raw endpoint"
        );
        let refusal = refused.err().unwrap();
        assert!(refusal.contains("TypeMismatch"), "{refusal}");
        eprintln!("ordinary wrong-result reduce={reduce} depth={depth} refused=TypeMismatch");
        let wire = bundle.encode_with_claim(&claim).unwrap();
        if let Some(base) = std::env::var_os("SCOPED_APPLICATION_ARTIFACT_DIR") {
            let base = std::path::PathBuf::from(base);
            std::fs::create_dir_all(&base).unwrap();
            std::fs::write(
                base.join(format!("reduce-{reduce}-depth-{depth}.bin")),
                &wire,
            )
            .unwrap();
            std::fs::write(
                base.join(format!("wrong-reduce-{reduce}-depth-{depth}.bin")),
                &wrong_wire,
            )
            .unwrap();
        }
        let (bundle, claim) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
        let result = bundle.replay(&env, &claim, 2_000_000);
        eprintln!(
            "ordinary applied substitution reduce={reduce} depth={depth} producer={producer_work} wire={} result={:?}",
            wire.len(),
            result
                .as_ref()
                .map(|accepted| (accepted.kernel_work, accepted.scope_visits))
                .map_err(|error| error.chars().take(800).collect::<String>())
        );
        assert!(result.is_ok(), "{:?}", result.err());
    }
}

fn parts(scope: &LocalScope, external: &[ScopedLocal], operations: usize) -> ProofComponents {
    let mut parts = ProofComponents::new(
        "ordinary.application.controls",
        ProofLimits {
            operations,
            ..Default::default()
        },
    );
    parts
        .set_base(
            scope,
            external
                .iter()
                .cloned()
                .map(OwnedProofCapture::Parameter)
                .collect(),
        )
        .unwrap();
    parts
}

#[test]
fn curried_substitution_is_simultaneous_and_preserves_unrelated_redexes() {
    let mut scope = LocalScope::new();
    let f = scope
        .try_local(Expr::arrow(nat(), Expr::arrow(nat(), nat())))
        .unwrap();
    let g = scope.try_local(Expr::arrow(nat(), nat())).unwrap();
    let x = scope.try_local(nat()).unwrap();
    let a = scope.try_local(nat()).unwrap();
    let b = scope.try_local(nat()).unwrap();
    let identity = scope.try_local(nat()).unwrap();
    let external = [f.clone(), g.clone(), x.clone()];
    let bindings = [
        (
            f.clone(),
            a.lam(b.lam(add(
                Expr::app(g.term().clone(), a.term().clone()),
                b.term().clone(),
            ))),
        ),
        (g.clone(), a.lam(Expr::nat_lit(99))),
    ];
    let unrelated = Expr::app(identity.lam(identity.term().clone()), Expr::nat_lit(3));
    let roots = [
        Expr::apps(f.term().clone(), [x.term().clone(), Expr::nat_lit(7)]),
        Expr::app(g.term().clone(), x.term().clone()),
        unrelated,
    ];
    let unrelated = scope.close(&roots[2]).unwrap();
    let mut parts = parts(&scope, &external, 1_000_000);
    let reduced = parts
        .substitute_scoped_applications(&scope, &external, &bindings, &roots)
        .unwrap();
    assert_eq!(
        reduced[0],
        add(
            Expr::app(g.term().clone(), x.term().clone()),
            Expr::nat_lit(7)
        )
    );
    assert_eq!(reduced[1], Expr::nat_lit(99));
    assert_eq!(reduced[2], unrelated);
    let structural = parts
        .substitute_scoped_terms(&scope, &external, &bindings, &roots)
        .unwrap();
    assert_ne!(structural[0], reduced[0]);
    assert_ne!(structural[1], reduced[1]);
}

#[test]
fn application_substitution_refuses_foreign_duplicate_shadowed_and_open_inputs() {
    let mut scope = LocalScope::new();
    let f = scope.try_local(Expr::arrow(nat(), nat())).unwrap();
    let x = scope.try_local(nat()).unwrap();
    let absent = scope.try_local(nat()).unwrap();
    let internal = scope.try_local(nat()).unwrap();
    let mut other = LocalScope::new();
    let foreign = other.try_local(f.ty().clone()).unwrap();
    let external = [f.clone(), x.clone()];
    let replacement = internal.lam(internal.term().clone());
    let bindings = [(f.clone(), replacement.clone())];
    let root = Expr::app(f.term().clone(), x.term().clone());
    let mut parts = parts(&scope, &external, 1_000_000);
    assert!(
        parts
            .substitute_scoped_applications(&other, &[], &[], &[nat()])
            .is_err()
    );
    assert!(
        parts
            .substitute_scoped_applications(&scope, &[foreign], &[], &[nat()])
            .is_err()
    );
    assert!(
        parts
            .substitute_scoped_applications(&scope, &[f.clone(), f.clone()], &[], &[nat()])
            .is_err()
    );
    assert!(
        parts
            .substitute_scoped_applications(
                &scope,
                &external,
                &[
                    (f.clone(), replacement.clone()),
                    (f.clone(), replacement.clone())
                ],
                &[root.clone()]
            )
            .is_err()
    );
    assert!(
        parts
            .substitute_scoped_applications(
                &scope,
                &external,
                &[(absent.clone(), Expr::nat_lit(0))],
                &[root.clone()]
            )
            .is_err()
    );
    assert!(
        parts
            .substitute_scoped_applications(
                &scope,
                &external,
                &[(f.clone(), Expr::bvar(0))],
                &[root.clone()]
            )
            .unwrap_err()
            .contains("loose bound")
    );
    assert!(
        parts
            .substitute_scoped_applications(&scope, &external, &bindings, &[x.lam(root)])
            .is_err()
    );
    // Even a discarded argument must belong to the full validated inventory.
    assert!(
        parts
            .substitute_scoped_applications(
                &scope,
                &external,
                &[(f.clone(), internal.lam(Expr::nat_lit(0)))],
                &[Expr::app(f.term().clone(), absent.term().clone())]
            )
            .is_err()
    );
    let before = parts.counts().3;
    let error = parts
        .substitute_scoped_applications(
            &scope,
            &external,
            &bindings,
            &[internal.lam(Expr::app(f.term().clone(), internal.term().clone()))],
        )
        .unwrap_err();
    assert!(error.contains("loose bound variable"), "{error}");
    assert!(
        parts.counts().3 > before,
        "failed contraction must retain its spent work"
    );
}

#[test]
fn application_substitution_repeated_calls_share_the_original_budget() {
    let mut scope = LocalScope::new();
    let f = scope.try_local(Expr::arrow(nat(), nat())).unwrap();
    let x = scope.try_local(nat()).unwrap();
    let internal = scope.try_local(nat()).unwrap();
    let external = [f.clone(), x.clone()];
    let bindings = [(f.clone(), internal.lam(internal.term().clone()))];
    let roots = [Expr::app(f.term().clone(), x.term().clone())];
    let mut parts = parts(&scope, &external, 256);
    let mut successes = 0;
    loop {
        let before = parts.counts().3;
        let result = parts.substitute_scoped_applications(&scope, &external, &bindings, &roots);
        assert!(parts.counts().3 >= before);
        assert!(parts.counts().3 <= 256);
        if result.is_err() {
            break;
        }
        assert!(parts.counts().3 > before);
        assert_eq!(result.unwrap()[0], *x.term());
        successes += 1;
        assert!(successes < 256, "work was reset between calls");
    }
    assert!(successes > 0);
    let before = parts.counts().3;
    assert!(
        parts
            .substitute_scoped_applications(&scope, &external, &bindings, &roots)
            .is_err()
    );
    assert!(parts.counts().3 >= before);
}

#[test]
fn application_substitution_checks_depth_after_embedding_the_argument() {
    let mut scope = LocalScope::with_limits(LocalScopeLimits {
        closing: trust_ir_build::term_scope::TermScopeLimits {
            max_depth: 8,
            ..Default::default()
        },
        ..Default::default()
    });
    let f = scope.try_local(Expr::arrow(nat(), nat())).unwrap();
    let x = scope.try_local(nat()).unwrap();
    let internal = scope.try_local(nat()).unwrap();
    let external = [f.clone(), x.clone()];
    let mut body = internal.term().clone();
    let mut argument = x.term().clone();
    for _ in 0..4 {
        body = Expr::app(Expr::const_str("Nat.succ"), body);
        argument = Expr::app(Expr::const_str("Nat.succ"), argument);
    }
    let replacement = internal.lam(body);
    let root = Expr::app(f.term().clone(), argument);
    // Each separate input fits the cap; only the combined output exceeds it.
    assert!(
        scope
            .close_external_forest(
                &[replacement.clone(), root.clone()],
                &external,
                &[external.len(); 2]
            )
            .0
            .is_ok()
    );
    let mut parts = parts(&scope, &external, 1_000_000);
    let error = parts
        .substitute_scoped_applications(&scope, &external, &[(f, replacement)], &[root])
        .unwrap_err();
    assert!(error.to_ascii_lowercase().contains("depth"), "{error}");
}

#[test]
fn application_substitution_retains_unused_invalid_original_declarations() {
    let mut scope = LocalScope::new();
    let mut parts = parts(&scope, &[], 1_000_000);
    let _invalid = parts
        .bind_scoped(
            &mut scope,
            &[],
            at(
                "Eq",
                vec![Level::succ(Level::zero())],
                [nat(), Expr::nat_lit(0), Expr::nat_lit(1)],
            ),
            at(
                "Eq.refl",
                vec![Level::succ(Level::zero())],
                [nat(), Expr::nat_lit(0)],
            ),
        )
        .unwrap();
    let root = parts
        .substitute_scoped_applications(&scope, &[], &[], &[Expr::const_str("True.intro")])
        .unwrap()
        .remove(0);
    let bundle = parts
        .close_scoped(&scope, root, Expr::const_str("True"), Default::default())
        .unwrap();
    let bytes = bundle.encode_with_claim(&Expr::const_str("True")).unwrap();
    let (bundle, claim) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    let error = bundle
        .replay(&env, &claim, 2_000_000)
        .err()
        .expect("invalid original declaration was discarded");
    assert!(
        error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
        "{error}"
    );
}
