// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Correlation follows equal materialized computations, not allocation sharing.
use super::*;
use crate::{
    proof_assembly::ProofLimits, scoped_local::LocalScope, semantic_evaluation,
    term_scope::TermScopeLimits,
};
fn bool_() -> Expr {
    Expr::const_str("Bool")
}
fn flag(value: bool) -> Expr {
    Expr::const_str(if value { "Bool.true" } else { "Bool.false" })
}
fn pair_type() -> Expr {
    at(
        "Prod",
        vec![Level::zero(), Level::zero()],
        [bool_(), bool_()],
    )
}
fn pair(first: Expr, second: Expr) -> Expr {
    at(
        "Prod.mk",
        vec![Level::zero(), Level::zero()],
        [bool_(), bool_(), first, second],
    )
}
fn computation(sc: &mut LocalScope, major: Expr, corrupt: bool) -> Expr {
    let ignored = sc.allocate_local(bool_()).unwrap();
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
fn run(corrupt: bool) {
    let mut env = semantic_evaluation::build_environment().unwrap();
    semantic_evaluation::install_case_maps_into(&mut env).unwrap();
    let mut sc = LocalScope::new();
    let guard = sc.allocate_local(bool_()).unwrap();
    let first = computation(&mut sc, guard.term().clone(), false);
    let argument = sc.allocate_local(bool_()).unwrap();
    let body = computation(&mut sc, argument.term().clone(), corrupt);
    // Beta substitution rebuilds the second computation AFTER source forest
    // materialization. Its children need not share first's physical Arcs.
    let second = Expr::app(argument.lam(body), guard.term().clone());
    let select = |name: &str, value| {
        at(
            name,
            vec![Level::zero(), Level::zero()],
            [bool_(), bool_(), value],
        )
    };
    let source = pair(select("Prod.fst", first), select("Prod.snd", second));
    let input = sc.allocate_local(pair_type()).unwrap();
    let ignored = sc.allocate_local(bool_()).unwrap();
    let second = select("Prod.snd", input.term().clone());
    let project = input.lam(at(
        "Bool.rec",
        vec![Level::succ(Level::zero())],
        [
            ignored.lam(bool_()),
            Expr::app(Expr::const_str("Bool.not"), second.clone()),
            second,
            select("Prod.fst", input.term().clone()),
        ],
    ));
    let mut parts = ProofComponents::new("ordinary.recomputed.correlation", ProofLimits::default());
    parts
        .set_base(&sc, vec![OwnedProofCapture::Parameter(guard.clone())])
        .unwrap();
    let (candidate, work) = replay_projected_equality_with_diagnostics(
        &env,
        &mut sc,
        std::slice::from_ref(&guard),
        &[],
        pair_type(),
        bool_(),
        project,
        source,
        flag(true),
        Level::zero(),
        ImageReplayLimits::default(),
        &mut parts,
        ProjectedCaseStrategy::Correlated,
    );
    eprintln!("recomputed corrupt={corrupt} work={work:?}");
    let candidate = candidate.unwrap();
    let claim = sc.close(&guard.pi(candidate.proposition)).unwrap();
    let bundle = parts
        .close_scoped(
            &sc,
            guard.lam(candidate.proof),
            candidate.component_proposition,
            TermScopeLimits::default(),
        )
        .unwrap();
    let wire = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, claim) =
        crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
    if let Some(base) = std::env::var_os("IR_PROJECTED_RECOMPUTED_ARTIFACT_DIR") {
        let path = std::path::PathBuf::from(base).join(if corrupt { "changed" } else { "equal" });
        std::fs::create_dir_all(&path).unwrap();
        std::fs::write(path.join("scoped.bin"), wire).unwrap();
    }
    let result = decoded.replay(&env, &claim, 2_000_000);
    match (corrupt, result) {
        (false, Ok(ok)) => eprintln!(
            "recomputed accepted kernel_work={} scope_visits={}",
            ok.kernel_work, ok.scope_visits
        ),
        (true, Err(error))
            if error.contains("TypeMismatch") && !error.contains("BudgetExhausted") => {}
        (_, result) => panic!(
            "recomputed corrupt={corrupt}: {}",
            result
                .err()
                .unwrap_or_else(|| "changed computation accepted".into())
        ),
    }
}
#[test]
fn equal_recomputed_pair_fields_keep_their_correlation() {
    run(false);
}
#[test]
fn changed_recomputed_pair_field_is_refused() {
    run(true);
}
