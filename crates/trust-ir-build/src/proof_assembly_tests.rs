// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ordinary kernel-prelude checks. No Core evaluator, aliases, domain axioms,
//! front-end interpretation, or proof-authority wrappers are installed here.

use super::*;
use clean_kernel::{Environment, KernelTypeError, TypeChecker, env::ConstantKind};

#[path = "proof_assembly_prefix_tests.rs"]
mod prefix;

#[path = "proof_assembly_let_tests.rs"]
mod lets;

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    at("Eq", vec![Level::succ(Level::zero())], [ty, a, b])
}
fn refl(ty: Expr, a: Expr) -> Expr {
    at("Eq.refl", vec![Level::succ(Level::zero())], [ty, a])
}
fn exists(x: &ScopedLocal, body: Expr) -> Expr {
    at(
        "Exists",
        vec![Level::succ(Level::zero())],
        [x.ty().clone(), x.lam(body)],
    )
}
fn forall(xs: &[ScopedLocal], body: Expr) -> Expr {
    xs.iter().rev().fold(body, |body, x| x.pi(body))
}
fn lams(xs: &[ScopedLocal], body: Expr) -> Expr {
    xs.iter().rev().fold(body, |body, x| x.lam(body))
}
fn environment() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    env.init_true_false().unwrap();
    env.init_and().unwrap();
    env.init_exists().unwrap();
    env
}
fn checked(env: &Environment, proof: &Expr, claim: &Expr) {
    TypeChecker::new(env)
        .check_type(claim, &Expr::sort(Level::zero()))
        .unwrap();
    TypeChecker::new(env).check_type(proof, claim).unwrap();
    let audit = env.audit_certification(claim, proof);
    assert!(audit.is_certified(), "{audit:#?}");
    for name in &audit.dependencies {
        assert_ne!(env.get_const(name).unwrap().kind, ConstantKind::Axiom);
        assert!(env.axiom_deps(name).unwrap().is_empty(), "{name}");
        assert!(env.trust_marker_deps(name).unwrap().is_empty(), "{name}");
    }
}
fn rejected(env: &Environment, proof: &Expr, claim: &Expr) {
    TypeChecker::new(env)
        .check_type(claim, &Expr::sort(Level::zero()))
        .unwrap();
    let error = TypeChecker::new(env).check_type(proof, claim).unwrap_err();
    assert!(
        matches!(error, KernelTypeError::TypeMismatch { .. }),
        "semantic rejection only: {error}"
    );
}

#[test]
fn borrowed_dependent_capture_and_forall_candidates_replay_and_refuse_bad_owners() {
    let env = environment();
    let mut scope = LocalScope::new();
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let a = scope.try_local(Expr::type_()).unwrap();
    let x = scope.try_local(a.term().clone()).unwrap();
    let n = scope.try_local(c("Nat")).unwrap();
    let z = scope.try_local(c("Nat")).unwrap();
    let original = z.pi(eq(a.term().clone(), x.term().clone(), x.term().clone()));
    let captures = [a.clone(), x.clone(), n.clone()];
    // Exercise an iterator of BORROWED handles, not a converted local vector.
    let normalized = logic
        .normalize_open(&scope, captures.iter(), &original)
        .unwrap();
    let proof = logic
        .introduce_forall(&mut scope, normalized, |logic, _, _, instance| {
            logic.candidate(instance, refl(a.term().clone(), x.term().clone()))
        })
        .unwrap();
    checked(
        &env,
        &scope.close(&lams(&captures, proof.term().clone())).unwrap(),
        &scope.close(&forall(&captures, original)).unwrap(),
    );
    let wrong = z.pi(eq(c("Nat"), n.term().clone(), nat(0)));
    rejected(
        &env,
        &scope.close(&lams(&captures, proof.term().clone())).unwrap(),
        &scope.close(&forall(&captures, wrong)).unwrap(),
    );
    assert!(
        logic
            .normalize_open(&scope, [&x, &a, &n], proof.proposition())
            .is_err()
    );
    assert!(
        logic
            .normalize_open(&scope, [&a, &a, &x, &n], proof.proposition())
            .is_err()
    );
    let mut foreign = LocalScope::new();
    let foreign_a = foreign.try_local(Expr::type_()).unwrap();
    assert_eq!(foreign_a.id(), a.id(), "foreign numeric IDs may collide");
    assert!(
        logic
            .normalize_open(&scope, [&foreign_a, &x, &n], proof.proposition())
            .is_err()
    );
    let mut tiny = ProofAssembly::new(ProofLimits {
        captures: 1,
        ..ProofLimits::default()
    })
    .unwrap();
    assert!(
        tiny.normalize_open(&scope, captures.iter(), proof.proposition())
            .is_err()
    );
}

#[test]
fn existential_projection_preserves_dependent_witness_and_rejects_wrong_continuations() {
    let env = environment();
    let mut scope = LocalScope::new();
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let a = scope.try_local(Expr::type_()).unwrap();
    let x = scope.try_local(a.term().clone()).unwrap();
    let y = scope.try_local(a.term().clone()).unwrap();
    let relation = eq(a.term().clone(), y.term().clone(), x.term().clone());
    let premise = scope
        .try_local(exists(&y, app("And", [relation.clone(), c("True")])))
        .unwrap();
    let goal = exists(&y, relation);
    let parameters = [a, x, premise.clone()];
    let normalized = logic
        .normalize_open(&scope, parameters.iter(), premise.ty())
        .unwrap();
    let premise_fact = logic.candidate(normalized, premise.term().clone()).unwrap();
    let normalized_goal = logic
        .normalize_open(&scope, parameters.iter(), &goal)
        .unwrap();
    let mut expired = None;
    let proof = logic
        .eliminate_exists(
            &mut scope,
            &premise_fact,
            normalized_goal.clone(),
            |logic, _, witness, evidence| {
                expired = Some(evidence.clone());
                let relation = logic.and_at(&evidence, 0)?;
                logic.introduce_exists(normalized_goal.clone(), witness.term().clone(), &relation)
            },
        )
        .unwrap();
    assert!(logic.and_at(&expired.unwrap(), 0).is_err());
    checked(
        &env,
        &scope
            .close(&lams(&parameters, proof.term().clone()))
            .unwrap(),
        &scope.close(&forall(&parameters, goal)).unwrap(),
    );
    assert!(
        logic
            .eliminate_exists(
                &mut scope,
                &premise_fact,
                normalized_goal,
                |logic, _, _, _| logic.candidate(c("True"), c("True.intro"))
            )
            .is_err()
    );
    // A false proof body with the RIGHT metadata must still fail real replay.
    let forged = logic
        .candidate(proof.proposition().clone(), c("True.intro"))
        .unwrap();
    rejected(
        &env,
        &scope
            .close(&lams(&parameters, forged.term().clone()))
            .unwrap(),
        &scope
            .close(&forall(&parameters, proof.proposition().clone()))
            .unwrap(),
    );
}

#[test]
fn expired_error_and_panicking_contexts_never_revive_and_counters_stay_charged() {
    let mut logic = ProofAssembly::new(ProofLimits {
        contexts: 8,
        ..ProofLimits::default()
    })
    .unwrap();
    let outer = logic.candidate(c("True"), c("True.intro")).unwrap();
    let escaped = logic
        .with_scope(|inner| inner.candidate(c("True"), c("True.intro")))
        .unwrap();
    assert!(logic.check_live(&escaped).is_err());
    let mut failed = None;
    let error: Result<()> = logic.with_scope(|inner| {
        failed = Some(inner.candidate(c("True"), c("True.intro"))?);
        Err("deliberate continuation error".into())
    });
    assert!(error.is_err());
    assert!(logic.check_live(&failed.unwrap()).is_err());
    let mut panicked = None;
    let before_count = logic.operations;
    let before_context = logic.next_context;
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _: Result<()> = logic.with_scope(|inner| {
            panicked = Some(inner.candidate(c("True"), c("True.intro"))?);
            panic!("deliberate continuation panic")
        });
    }));
    assert!(panic.is_err());
    assert!(logic.in_root_context());
    let panicked = panicked.unwrap();
    assert!(logic.check_live(&panicked).is_err());
    assert!(logic.operations > before_count && logic.next_context > before_context);
    logic.check_live(&outer).unwrap();
    logic
        .with_scope(|sibling| {
            assert!(sibling.check_live(&panicked).is_err());
            assert!(sibling.check_live(&escaped).is_err());
            sibling.check_live(&outer)
        })
        .unwrap();
    assert!(
        ProofAssembly::new(ProofLimits {
            contexts: 0,
            ..ProofLimits::default()
        })
        .is_err()
    );
    let mut one = ProofAssembly::new(ProofLimits {
        operations: 1,
        ..ProofLimits::default()
    })
    .unwrap();
    let live = one.candidate(c("True"), c("True.intro")).unwrap();
    assert!(one.candidate(c("True"), c("True.intro")).is_err());
    assert!(one.and_at(&live, usize::MAX).is_err());
    assert!(logic.check_live(&live).is_err(), "foreign producer handle");
}

#[test]
fn proof_valued_lets_are_checked_even_when_the_continuation_does_not_use_them() {
    let env = environment();
    let mut scope = LocalScope::new();
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let good = logic
        .candidate(eq(c("Nat"), nat(0), nat(0)), refl(c("Nat"), nat(0)))
        .unwrap();
    let good_local = scope.try_local(good.proposition().clone()).unwrap();
    let unused = scope
        .close(&good_local.let_(good.term().clone(), c("True.intro")))
        .unwrap();
    checked(&env, &unused, &c("True"));
    let used = scope
        .close(&good_local.let_(good.term().clone(), good_local.term().clone()))
        .unwrap();
    checked(&env, &used, good.proposition());
    let bad = logic
        .candidate(eq(c("Nat"), nat(0), nat(1)), refl(c("Nat"), nat(0)))
        .unwrap();
    let bad_local = scope.try_local(bad.proposition().clone()).unwrap();
    let unused_bad = scope
        .close(&bad_local.let_(bad.term().clone(), c("True.intro")))
        .unwrap();
    rejected(&env, &unused_bad, &c("True"));
}
