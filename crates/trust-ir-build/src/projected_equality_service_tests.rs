// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Ordinary protected-field service consumer; no source-language or provider
//! semantics. A failure notification may change the first field only.
use super::*;
use crate::{
    proof_assembly::ProofLimits, scoped_local::LocalScope, semantic_evaluation,
    term_scope::TermScopeLimits,
};

fn n() -> Expr {
    Expr::const_str("Nat")
}
fn ty(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    at(name, vec![Level::zero(), Level::zero()], args)
}
fn choose(sc: &mut LocalScope, value: Expr, flag: Expr, yes: Expr, no: Expr) -> Expr {
    let ignored = sc.allocate_local(Expr::const_str("Bool")).unwrap();
    at(
        "Bool.rec",
        vec![Level::succ(Level::zero())],
        [ignored.lam(value), no, yes, flag],
    )
}
fn fixture(
    sc: &mut LocalScope,
    notify: bool,
    corrupt: bool,
) -> (Vec<ScopedLocal>, Expr, Expr, Expr, Expr) {
    let bool_ = Expr::const_str("Bool");
    let state = ty("Prod", [n(), n()]);
    let status = ty("Except", [n(), bool_.clone()]);
    let response = ty("Prod", [n(), status.clone()]);
    let answer = ty("Prod", [state.clone(), status.clone()]);
    let service = sc
        .allocate_local(Expr::arrow(n(), response.clone()))
        .unwrap();
    let before = sc.allocate_local(state.clone()).unwrap();
    let select_before = sc.allocate_local(bool_.clone()).unwrap();
    let returned = sc.allocate_local(response).unwrap();
    let flag = sc.allocate_local(bool_.clone()).unwrap();
    let code = sc.allocate_local(n()).unwrap();
    let world = ty("Prod.snd", [n(), n(), before.term().clone()]);
    let next = ty(
        "Prod.mk",
        [
            n(),
            n(),
            ty("Prod.fst", [n(), status.clone(), returned.term().clone()]),
            if corrupt {
                Expr::app(Expr::const_str("Nat.succ"), world.clone())
            } else {
                world.clone()
            },
        ],
    );
    let failed_state = if notify {
        choose(
            sc,
            state.clone(),
            select_before.term().clone(),
            before.term().clone(),
            next.clone(),
        )
    } else {
        next.clone()
    };
    let outcome = sc.allocate_local(status.clone()).unwrap();
    let source = at(
        "Except.rec",
        vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
        [
            n(),
            bool_.clone(),
            outcome.lam(answer.clone()),
            code.lam(ty(
                "Prod.mk",
                [
                    state.clone(),
                    status.clone(),
                    failed_state,
                    ty("Except.error", [n(), bool_.clone(), code.term().clone()]),
                ],
            )),
            flag.lam(ty(
                "Prod.mk",
                [
                    state.clone(),
                    status.clone(),
                    next,
                    ty("Except.ok", [n(), bool_, flag.term().clone()]),
                ],
            )),
            ty("Prod.snd", [n(), status.clone(), returned.term().clone()]),
        ],
    );
    let source = returned.let_(
        Expr::app(
            service.term().clone(),
            ty("Prod.fst", [n(), n(), before.term().clone()]),
        ),
        source,
    );
    let input = sc.allocate_local(answer.clone()).unwrap();
    let project = input.lam(ty(
        "Prod.snd",
        [
            n(),
            n(),
            ty("Prod.fst", [state, status, input.term().clone()]),
        ],
    ));
    (
        vec![service, before, select_before],
        answer,
        project,
        source,
        world,
    )
}

#[test]
fn protected_service_notification_preserves_untouched_field() {
    let mut env = semantic_evaluation::build_environment().unwrap();
    semantic_evaluation::install_case_maps_into(&mut env).unwrap();
    env.init_nat().unwrap();
    let mut failures = Vec::new();
    for strategy in [
        ProjectedCaseStrategy::Structural,
        ProjectedCaseStrategy::Correlated,
    ] {
        for notify in [false, true] {
            for corrupt in [false, true] {
                let mut sc = LocalScope::new();
                let (globals, answer, project, source, expected) =
                    fixture(&mut sc, notify, corrupt);
                let mut parts =
                    ProofComponents::new("ordinary.protected.service", ProofLimits::default());
                parts
                    .set_base(
                        &sc,
                        globals
                            .iter()
                            .cloned()
                            .map(OwnedProofCapture::Parameter)
                            .collect(),
                    )
                    .unwrap();
                let candidate = replay_projected_equality_with_strategy(
                    &env,
                    &mut sc,
                    &globals,
                    &[],
                    answer,
                    n(),
                    project,
                    source,
                    expected,
                    Level::zero(),
                    ImageReplayLimits::default(),
                    &mut parts,
                    strategy,
                )
                .unwrap();
                let goal = sc
                    .close(
                        &globals
                            .iter()
                            .rev()
                            .fold(candidate.proposition, |g, p| p.pi(g)),
                    )
                    .unwrap();
                let root = globals.iter().rev().fold(candidate.proof, |b, p| p.lam(b));
                let bundle = parts
                    .close_scoped(
                        &sc,
                        root,
                        candidate.component_proposition,
                        TermScopeLimits::default(),
                    )
                    .unwrap();
                let wire = bundle.encode_with_claim(&goal).unwrap();
                let (decoded, goal) =
                    crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire)
                        .unwrap();
                let result = decoded.replay(&env, &goal, 2_000_000);
                if let Some(base) = std::env::var_os("IR_PROJECTION_SERVICE_ARTIFACT_DIR") {
                    let path = std::path::PathBuf::from(base)
                        .join(format!("service-{strategy:?}-{notify}-{corrupt}"));
                    std::fs::create_dir_all(&path).unwrap();
                    std::fs::write(path.join("scoped.bin"), wire).unwrap();
                    std::fs::write(path.join("goal.txt"), goal.to_string()).unwrap();
                    for (i, decl) in decoded.declarations.iter().enumerate() {
                        std::fs::write(
                            path.join(format!("declaration-{i}.txt")),
                            format!(
                                "{:?}\nTYPE\n{}\nVALUE\n{}\n",
                                decl.id,
                                decl.type_,
                                decl.value
                                    .as_ref()
                                    .map(ToString::to_string)
                                    .unwrap_or_default()
                            ),
                        )
                        .unwrap();
                    }
                    std::fs::write(
                        path.join("verdict.txt"),
                        match &result {
                            Ok(ok) => format!("accepted work={}", ok.kernel_work),
                            Err(error) => error.clone(),
                        },
                    )
                    .unwrap();
                }
                match (corrupt, result) {
                    (false, Ok(_)) => {}
                    (true, Err(error))
                        if error.contains("TypeMismatch") && !error.contains("BudgetExhausted") => {
                    }
                    (false, Err(error)) => failures.push(format!("{strategy:?}/{notify}: {error}")),
                    (true, Ok(_)) => {
                        failures.push(format!("{strategy:?}/{notify}: changed field accepted"))
                    }
                    (true, Err(error)) => {
                        failures.push(format!("{strategy:?}/{notify}: wrong refusal: {error}"))
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
