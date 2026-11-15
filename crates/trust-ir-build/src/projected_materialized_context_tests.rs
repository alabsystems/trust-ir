// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Generic ordinary Trust correlation: authorization reuse changes no wire.
use super::*;
use crate::{
    proof_assembly::ProofLimits, scoped_local::LocalScope, semantic_evaluation,
    term_scope::TermScopeLimits,
};
fn b() -> Expr {
    Expr::const_str("Bool")
}
fn flag(value: bool) -> Expr {
    Expr::const_str(if value { "Bool.true" } else { "Bool.false" })
}
fn pair_type() -> Expr {
    at("Prod", vec![Level::zero(); 2], [b(), b()])
}
fn pair(first: Expr, second: Expr) -> Expr {
    at("Prod.mk", vec![Level::zero(); 2], [b(), b(), first, second])
}
fn computation(scope: &mut LocalScope, major: Expr, corrupt: bool) -> Expr {
    let ignored = scope.allocate_local(b()).unwrap();
    at(
        "Bool.rec",
        vec![Level::succ(Level::zero())],
        [
            ignored.lam(pair_type()),
            pair(flag(false), flag(false)),
            pair(flag(true), flag(!corrupt)),
            major,
        ],
    )
}
fn select(name: &str, term: Expr) -> Expr {
    at(name, vec![Level::zero(); 2], [b(), b(), term])
}
fn fixture(scope: &mut LocalScope, guard: Expr, corrupt: bool) -> Expr {
    let mut answer = flag(true);
    // Recomputed equal cases are ordinary administrative beta reductions,
    // not shared-node assumptions. Corruption changes a genuine result.
    for index in 0..8 {
        let first = computation(scope, guard.clone(), false);
        let argument = scope.allocate_local(b()).unwrap();
        let body = computation(scope, argument.term().clone(), corrupt && index == 0);
        let second = Expr::app(argument.lam(body), guard.clone());
        let right = select("Prod.snd", second);
        let ignored = scope.allocate_local(b()).unwrap();
        let equal = at(
            "Bool.rec",
            vec![Level::succ(Level::zero())],
            [
                ignored.lam(b()),
                Expr::app(Expr::const_str("Bool.not"), right.clone()),
                right,
                select("Prod.fst", first),
            ],
        );
        answer = Expr::apps(Expr::const_str("Bool.and"), [equal, answer]);
    }
    answer
}
fn run(mode: MaterializedValidationMode, corrupt: bool) -> (Vec<u8>, ProjectedEqualityWork) {
    let mut env = semantic_evaluation::build_environment().unwrap();
    semantic_evaluation::install_case_maps_into(&mut env).unwrap();
    env.init_nat().unwrap();
    let mut scope = LocalScope::new();
    let guard = scope.allocate_local(b()).unwrap();
    // A wide ordinary consumer telescope makes repeated authorization visible.
    // These are genuine arbitrary parameters, not extra work/proof allowances.
    let mut globals = vec![guard.clone()];
    globals.extend((0..128).map(|_| scope.allocate_local(Expr::const_str("Nat")).unwrap()));
    let source = fixture(&mut scope, guard.term().clone(), corrupt);
    let observed = scope.allocate_local(b()).unwrap();
    let project = observed.lam(observed.term().clone());
    let external = eq(
        &Level::zero(),
        b(),
        Expr::app(project.clone(), source.clone()),
        flag(true),
    );
    let mut parts = ProofComponents::new("ordinary.inventory.correlation", ProofLimits::default());
    parts
        .set_base(
            &scope,
            globals
                .iter()
                .cloned()
                .map(OwnedProofCapture::Parameter)
                .collect(),
        )
        .unwrap();
    let mut work = ProjectedEqualityWork::default();
    let candidate = replay_projected_equality_profiled(
        &env,
        &mut scope,
        &globals,
        &[],
        b(),
        b(),
        project,
        source,
        flag(true),
        Level::zero(),
        ImageReplayLimits::default(),
        &mut parts,
        ProjectedCaseStrategy::Correlated,
        mode,
        &mut work,
    )
    .unwrap();
    let claim = scope
        .close(&globals.iter().rev().fold(external, |body, p| p.pi(body)))
        .unwrap();
    let bundle = parts
        .close_scoped(
            &scope,
            globals
                .iter()
                .rev()
                .fold(candidate.proof, |body, p| p.lam(body)),
            candidate.component_proposition,
            TermScopeLimits::default(),
        )
        .unwrap();
    let wire = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) =
        crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
    assert_eq!(transported, claim);
    let result = decoded.replay(&env, &claim, 2_000_000);
    if corrupt {
        let error = result
            .err()
            .expect("changed computation cannot establish the original frozen property");
        assert!(
            error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
            "{error}"
        );
    } else {
        result.unwrap();
    }
    (wire, work)
}
#[test]
fn authenticated_inventory_reuse_preserves_correlated_wire_and_strict_replay() {
    for corrupt in [false, true] {
        let (fresh_wire, fresh) = run(MaterializedValidationMode::FreshInventory, corrupt);
        let (reused_wire, reused) = run(MaterializedValidationMode::PerReplace, corrupt);
        assert_eq!(
            reused_wire, fresh_wire,
            "optimization must preserve every actual declaration and frozen endpoint"
        );
        assert!(
            fresh.replacement_reductions + fresh.materialized_case_comparisons >= 2,
            "fixture must really exercise repeated ordinary validation: {fresh:?}"
        );
        assert_eq!(fresh.replacement_reductions, reused.replacement_reductions);
        assert_eq!(
            fresh.materialized_case_comparisons,
            reused.materialized_case_comparisons
        );
        assert!(
            reused.total_context_visits < fresh.total_context_visits,
            "real charged work must decrease without changing wire: fresh={fresh:?}; reused={reused:?}"
        );
    }
}
