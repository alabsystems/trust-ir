// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Ordinary constructor observations whose demanded list hides a computed state.
use super::*;
use crate::{
    proof_assembly::ProofLimits, proof_components::ScopedProofComponentBundle,
    scoped_local::LocalScope, semantic_evaluation, term_scope::TermScopeLimits,
};
fn z(name: &str, count: usize, args: impl IntoIterator<Item = Expr>) -> Expr {
    at(name, vec![Level::zero(); count], args)
}
fn n() -> Expr {
    Expr::const_str("Nat")
}
fn b() -> Expr {
    Expr::const_str("Bool")
}
fn list() -> Expr {
    z("List", 1, [n()])
}
fn option() -> Expr {
    z("Option", 1, [n()])
}
fn none() -> Expr {
    z("Option.none", 1, [n()])
}
fn some(x: Expr) -> Expr {
    z("Option.some", 1, [n(), x])
}
fn prod(a: Expr, b: Expr) -> Expr {
    z("Prod", 2, [a, b])
}
fn pair(a: Expr, b: Expr, x: Expr, y: Expr) -> Expr {
    z("Prod.mk", 2, [a, b, x, y])
}
fn field(index: usize, a: Expr, b: Expr, raw: Expr) -> Expr {
    z(
        if index == 0 { "Prod.fst" } else { "Prod.snd" },
        2,
        [a, b, raw],
    )
}
fn choose(sc: &mut LocalScope, ty: Expr, guard: Expr, no: Expr, yes: Expr) -> Expr {
    let major = sc.allocate_local(b()).unwrap();
    at(
        "Bool.rec",
        vec![Level::succ(Level::zero())],
        [major.lam(ty), no, yes, guard],
    )
}
fn head(sc: &mut LocalScope, xs: Expr) -> Expr {
    let major = sc.allocate_local(list()).unwrap();
    let h = sc.allocate_local(n()).unwrap();
    let t = sc.allocate_local(list()).unwrap();
    let ih = sc.allocate_local(option()).unwrap();
    at(
        "List.rec",
        vec![Level::succ(Level::zero()), Level::zero()],
        [
            n(),
            major.lam(option()),
            none(),
            h.lam(t.lam(ih.lam(some(h.term().clone())))),
            xs,
        ],
    )
}
#[derive(Clone, Copy, Debug)]
enum Shape {
    Raw,
    Normal,
    Nested,
    ComputedExcept,
}
struct Fixture {
    scope: LocalScope,
    globals: Vec<ScopedLocal>,
    observed: Expr,
    source: Expr,
    project: Expr,
    expected: Expr,
}
fn fixture(shape: Shape, empty_false: bool) -> Fixture {
    let mut sc = LocalScope::new();
    let guard = sc.allocate_local(b()).unwrap();
    let x = sc.allocate_local(n()).unwrap();
    let xs = sc.allocate_local(list()).unwrap();
    let payload = sc.allocate_local(b()).unwrap();
    let base = prod(n(), list());
    let nested = matches!(shape, Shape::Nested);
    let state = if nested {
        prod(base.clone(), n())
    } else {
        base.clone()
    };
    let cons = z("List.cons", 1, [n(), x.term().clone(), xs.term().clone()]);
    let no_list = if empty_false {
        z("List.nil", 1, [n()])
    } else {
        cons.clone()
    };
    let state_arm = |counter, items| {
        let inner = pair(n(), list(), Expr::nat_lit(counter), items);
        if nested {
            pair(base.clone(), n(), inner, Expr::nat_lit(91))
        } else {
            inner
        }
    };
    let computed = choose(
        &mut sc,
        state.clone(),
        guard.term().clone(),
        state_arm(7, no_list),
        state_arm(8, cons),
    );
    let status = z("Except", 2, [n(), b()]);
    let error = z("Except.error", 2, [n(), b(), Expr::nat_lit(37)]);
    let ok = z("Except.ok", 2, [n(), b(), payload.term().clone()]);
    let outcome = match shape {
        Shape::Raw | Shape::Nested => error,
        Shape::Normal => ok,
        Shape::ComputedExcept => choose(&mut sc, status.clone(), guard.term().clone(), error, ok),
    };
    let observed = prod(state.clone(), status.clone());
    // Keep this outer constructor. Only the projector demands the computed state.
    let source = pair(state.clone(), status.clone(), computed, outcome);
    let input = sc.allocate_local(observed.clone()).unwrap();
    let state_input = sc.allocate_local(state.clone()).unwrap();
    let base_input = if nested {
        field(0, base.clone(), n(), state_input.term().clone())
    } else {
        state_input.term().clone()
    };
    let measurement_body = head(&mut sc, field(1, n(), list(), base_input));
    let measure = state_input.lam(measurement_body);
    let expected = some(x.term().clone());
    let body = match shape {
        Shape::Normal | Shape::ComputedExcept => z(
            semantic_evaluation::NORMAL_OBSERVATION,
            1,
            [
                state.clone(),
                n(),
                b(),
                option(),
                measure,
                expected.clone(),
                input.term().clone(),
            ],
        ),
        Shape::Raw | Shape::Nested => {
            Expr::app(measure, field(0, state, status, input.term().clone()))
        }
    };
    let project = input.lam(body);
    Fixture {
        scope: sc,
        globals: vec![guard, x, xs, payload],
        observed,
        source,
        project,
        expected,
    }
}
fn environment() -> Environment {
    let mut env = semantic_evaluation::build_environment().unwrap();
    semantic_evaluation::install_case_maps_into(&mut env).unwrap();
    semantic_evaluation::install_list_projection_into(&mut env).unwrap();
    semantic_evaluation::install_normal_post_into(&mut env).unwrap();
    env.init_option().unwrap();
    env
}
fn closed_claim(f: &Fixture, expected: Expr) -> Expr {
    let goal = eq(
        &Level::zero(),
        option(),
        Expr::app(f.project.clone(), f.source.clone()),
        expected,
    );
    f.scope
        .close(&f.globals.iter().rev().fold(goal, |g, l| l.pi(g)))
        .unwrap()
}
fn candidate(
    env: &Environment,
    f: &mut Fixture,
    strategy: ProjectedCaseStrategy,
) -> (ScopedProofComponentBundle, Expr, ProjectedEqualityWork) {
    let mut parts = ProofComponents::new("ordinary.list.receiver", ProofLimits::default());
    parts
        .set_base(
            &f.scope,
            f.globals
                .iter()
                .cloned()
                .map(OwnedProofCapture::Parameter)
                .collect(),
        )
        .unwrap();
    let (candidate, work) = replay_projected_equality_with_diagnostics(
        env,
        &mut f.scope,
        &f.globals,
        &[],
        f.observed.clone(),
        option(),
        f.project.clone(),
        f.source.clone(),
        f.expected.clone(),
        Level::zero(),
        ImageReplayLimits::default(),
        &mut parts,
        strategy,
    );
    let candidate = candidate.unwrap();
    let claim = closed_claim(f, f.expected.clone());
    let root = f
        .globals
        .iter()
        .rev()
        .fold(candidate.proof, |p, l| l.lam(p));
    let bundle = parts
        .close_scoped(
            &f.scope,
            root,
            candidate.component_proposition,
            TermScopeLimits::default(),
        )
        .unwrap();
    (bundle, claim, work)
}
fn replay(
    name: &str,
    env: &Environment,
    bundle: &ScopedProofComponentBundle,
    claim: &Expr,
    accepted: bool,
) {
    let wire = bundle.encode_with_claim(claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
    assert_eq!(&transported, claim);
    let result = decoded.replay(env, &transported, 2_000_000);
    let verdict = match &result {
        Ok(ok) => format!(
            "Accepted; kernel_work={}; scope_visits={}; all3 closures empty",
            ok.kernel_work, ok.scope_visits
        ),
        Err(e) => e.clone(),
    };
    if let Some(base) = std::env::var_os("IR_LIST_RECEIVER_ARTIFACT_DIR") {
        let dir = std::path::PathBuf::from(base).join(name);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("scoped.bin"), wire).unwrap();
        std::fs::write(
            dir.join("root.dag"),
            trust_ir::proof::encode_clean_expr_dag_v2(&decoded.root).unwrap(),
        )
        .unwrap();
        std::fs::write(
            dir.join("claim.dag"),
            trust_ir::proof::encode_clean_expr_dag_v2(&transported).unwrap(),
        )
        .unwrap();
        std::fs::write(dir.join("verdict.txt"), &verdict).unwrap();
    }
    eprintln!(
        "list-receiver {name}: {}",
        if result.is_ok() {
            "Accepted"
        } else {
            "Refused"
        }
    );
    if accepted {
        result.unwrap();
    } else {
        assert!(
            verdict.contains("TypeMismatch") && !verdict.contains("BudgetExhausted"),
            "{name}: {verdict}"
        );
    }
}
fn run(shape: Shape, empty_false: bool, strategy: ProjectedCaseStrategy, accepted: bool) {
    let env = environment();
    let mut f = fixture(shape, empty_false);
    let (bundle, claim, work) = candidate(&env, &mut f, strategy);
    let name = format!("{shape:?}-{empty_false}-{strategy:?}");
    eprintln!("list-receiver {name} work={work:?}");
    replay(&name, &env, &bundle, &claim, accepted);
}
#[test]
fn computed_state_head_under_raw_constructor() {
    run(Shape::Raw, false, ProjectedCaseStrategy::Correlated, true);
}
#[test]
fn normal_result_computed_state_head() {
    run(
        Shape::Normal,
        false,
        ProjectedCaseStrategy::Correlated,
        true,
    );
}
#[test]
fn nested_product_computed_state_head() {
    run(
        Shape::Nested,
        false,
        ProjectedCaseStrategy::Correlated,
        true,
    );
}
#[test]
fn computed_except_receiver_keeps_normal_observation_conditional() {
    run(
        Shape::ComputedExcept,
        false,
        ProjectedCaseStrategy::Correlated,
        true,
    );
}
#[test]
fn actual_empty_false_arm_still_refuses() {
    run(Shape::Raw, true, ProjectedCaseStrategy::Correlated, false);
    run(
        Shape::Normal,
        true,
        ProjectedCaseStrategy::Correlated,
        false,
    );
}
#[test]
fn structural_strategy_does_not_gain_correlated_list_search() {
    run(Shape::Raw, false, ProjectedCaseStrategy::Structural, false);
}
#[test]
fn exact_same_proof_refuses_none_and_successor_head() {
    let env = environment();
    let mut f = fixture(Shape::Raw, false);
    let (bundle, claim, _) = candidate(&env, &mut f, ProjectedCaseStrategy::Correlated);
    replay("same-proof-original", &env, &bundle, &claim, true);
    let left = bundle.goal.get_app_args()[1].clone();
    for (name, wrong) in [
        ("same-proof-none", none()),
        (
            "same-proof-successor",
            some(Expr::app(
                Expr::const_str("Nat.succ"),
                f.globals[1].term().clone(),
            )),
        ),
    ] {
        let claim = closed_claim(&f, wrong.clone());
        let mut changed = bundle.clone();
        // Keep every declaration and the exact complete root proof unchanged.
        changed.goal = eq(&Level::zero(), option(), left.clone(), wrong);
        assert_eq!(changed.root, bundle.root);
        replay(name, &env, &changed, &claim, false);
    }
}
