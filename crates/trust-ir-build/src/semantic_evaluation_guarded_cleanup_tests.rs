// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
use super::*;
use clean_kernel::KernelTypeError;

fn at0(name: &str, levels: usize, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::zero(); levels]),
        args,
    )
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn status() -> Expr {
    at0("Except", 2, [nat(), nat()])
}
fn answer() -> Expr {
    at0("Prod", 2, [nat(), status()])
}
fn outcome0(ok: bool, value: u64) -> Expr {
    at0(
        if ok { "Except.ok" } else { "Except.error" },
        2,
        [nat(), nat(), Expr::nat_lit(value)],
    )
}
fn response(state: Expr, value: Expr) -> Expr {
    at0("Prod.mk", 2, [nat(), status(), state, value])
}
fn eq0(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [answer(), left, right],
    )
}
fn capture(name: &str, goal: &Expr, proof: &Expr, verdict: &str) {
    if let Some(base) = std::env::var_os("IR_GUARDED_CLEANUP_ARTIFACT_DIR") {
        let dir = std::path::PathBuf::from(base).join(name);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("goal.bin"),
            trust_ir::proof::encode_clean_expr_dag_v2(goal).unwrap(),
        )
        .unwrap();
        std::fs::write(
            dir.join("proof.bin"),
            trust_ir::proof::encode_clean_expr_dag_v2(proof).unwrap(),
        )
        .unwrap();
        std::fs::write(dir.join("verdict.txt"), verdict).unwrap();
    }
}
fn empty_closure(env: &Environment, goal: &Expr, proof: &Expr) {
    let audit = env.audit_certification(goal, proof);
    assert!(audit.is_certified(), "{:?}", audit.issues);
    assert!(audit.foundations.is_empty(), "{:?}", audit.foundations);
    for name in &audit.dependencies {
        assert!(env.axiom_deps(name).unwrap().is_empty(), "domain: {name}");
        assert!(
            env.foundational_axiom_deps(name).unwrap().is_empty(),
            "foundation: {name}"
        );
        assert!(
            env.trust_marker_deps(name).unwrap().is_empty(),
            "marker: {name}"
        );
    }
}
fn environment() -> Environment {
    let mut env = build_environment().unwrap();
    install_guarded_raw_cleanup_into(&mut env).unwrap();
    env.init_nat().unwrap();
    env
}

#[test]
fn generic_guarded_cleanup_checks_with_empty_three_closures() {
    let env = environment();
    let t = env
        .get_const(&Name::from_string(GUARDED_RAW_CLEANUP))
        .unwrap();
    let proof = Expr::const_(Name::from_string(GUARDED_RAW_CLEANUP), vec![u()]);
    TypeChecker::new(&env).check_type(&proof, &t.type_).unwrap();
    empty_closure(&env, &t.type_, &proof);
    capture(
        "generic-law",
        &t.type_,
        &proof,
        "accepted; domain/foundation/trust-marker closures empty\n",
    );
    for name in NAMES {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        assert!(env.axiom_deps(&Name::from_string(name)).unwrap().is_empty());
        assert!(
            env.foundational_axiom_deps(&Name::from_string(name))
                .unwrap()
                .is_empty()
        );
        assert!(
            env.trust_marker_deps(&Name::from_string(name))
                .unwrap()
                .is_empty()
        );
        assert!(info.value.is_some());
    }
}

#[test]
fn additive_install_retains_all_existing_evaluation_declaration_bytes() {
    let mut env = build_environment().unwrap();
    install_case_maps_into(&mut env).unwrap();
    let names = DEFINITIONS
        .iter()
        .chain(THEOREMS)
        .copied()
        .chain(CASE_MAP_THEOREMS)
        .collect::<Vec<_>>();
    let before = names
        .iter()
        .map(|name| {
            let c = env.get_const(&Name::from_string(name)).unwrap();
            (
                *name,
                trust_ir::proof::encode_clean_expr_dag_v2(&c.type_).unwrap(),
                trust_ir::proof::encode_clean_expr_dag_v2(c.value.as_ref().unwrap()).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    install_guarded_raw_cleanup_into(&mut env).unwrap();
    for (name, ty, value) in before {
        let c = env.get_const(&Name::from_string(name)).unwrap();
        if let Some(base) = std::env::var_os("IR_GUARDED_CLEANUP_ARTIFACT_DIR") {
            let dir = std::path::PathBuf::from(base)
                .join("unchanged-declarations")
                .join(name);
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(dir.join("type-before.bin"), &ty).unwrap();
            std::fs::write(dir.join("value-before.bin"), &value).unwrap();
            std::fs::write(
                dir.join("type-after.bin"),
                trust_ir::proof::encode_clean_expr_dag_v2(&c.type_).unwrap(),
            )
            .unwrap();
            std::fs::write(
                dir.join("value-after.bin"),
                trust_ir::proof::encode_clean_expr_dag_v2(c.value.as_ref().unwrap()).unwrap(),
            )
            .unwrap();
        }
        assert_eq!(
            ty,
            trust_ir::proof::encode_clean_expr_dag_v2(&c.type_).unwrap(),
            "{name} type"
        );
        assert_eq!(
            value,
            trust_ir::proof::encode_clean_expr_dag_v2(c.value.as_ref().unwrap()).unwrap(),
            "{name} value"
        );
    }
}

#[test]
fn last_owned_name_collision_refuses_without_mutating_environment() {
    let mut env = build_environment().unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string(GUARDED_RAW_CLEANUP),
        level_params: vec![],
        type_: Expr::const_str("Bool"),
        value: Expr::const_str("Bool.false"),
        is_reducible: true,
    })
    .unwrap();
    let count = env.num_constants();
    assert!(install_guarded_raw_cleanup_into(&mut env).is_err());
    assert_eq!(count, env.num_constants());
    assert!(
        env.get_const(&Name::from_string(GUARDED_CLEANUP_DECODE_FIRST))
            .is_none()
    );
    assert!(
        env.get_const(&Name::from_string(GUARDED_CLEANUP_RAW_FIRST))
            .is_none()
    );
}

// A parser transaction owns a cursor checkpoint. Closing its temporary input
// advances cleanup state by three; parse success resumes a different path.
// The answer retains the complete cursor and either parse or close error.
// This is a non-TLA consumer of the generic law, not a provider-fidelity claim.
fn parser_transaction(
    original_ok: bool,
    cleanup_ok: bool,
    ignores_callback: bool,
) -> (Expr, Expr, Expr) {
    let mut sc = Scope::default();
    let state = sc.local(nat());
    let value = sc.local(nat());
    let raw = sc.local(status());
    let callback = sc.local(Expr::arrow(nat(), Expr::arrow(status(), answer())));
    let ok = lams(
        &[state.clone(), value.clone()],
        response(
            state.term.clone(),
            at0("Except.ok", 2, [nat(), nat(), value.term.clone()]),
        ),
    );
    let err = lams(
        &[state.clone(), value.clone()],
        response(
            state.term.clone(),
            at0("Except.error", 2, [nat(), nat(), value.term.clone()]),
        ),
    );
    let plus = |n| {
        Expr::apps(
            Expr::const_str("Nat.add"),
            [state.term.clone(), Expr::nat_lit(n)],
        )
    };
    let yes = lams(&[state.clone(), raw.clone()], response(plus(100), raw.term));
    let cleanup_result = if ignores_callback {
        response(Expr::nat_lit(41), outcome0(true, 73))
    } else {
        Expr::apps(
            callback.term.clone(),
            [
                plus(3),
                outcome0(cleanup_ok, if cleanup_ok { 99 } else { 29 }),
            ],
        )
    };
    let cleanup = lams(&[state, callback], cleanup_result);
    let arguments = vec![
        nat(),
        nat(),
        nat(),
        answer(),
        cleanup,
        yes,
        ok,
        err,
        Expr::nat_lit(5),
        outcome0(original_ok, if original_ok { 7 } else { 17 }),
    ];
    let left = at0(GUARDED_CLEANUP_DECODE_FIRST, 1, arguments.clone());
    let proof = at0(GUARDED_RAW_CLEANUP, 1, arguments);
    let expected = if original_ok {
        response(Expr::nat_lit(105), outcome0(true, 7))
    } else if ignores_callback {
        response(Expr::nat_lit(41), outcome0(true, 73))
    } else {
        response(
            Expr::nat_lit(8),
            outcome0(false, if cleanup_ok { 17 } else { 29 }),
        )
    };
    (left, expected, proof)
}

#[test]
fn parser_transaction_preserves_guard_actual_state_and_error_precedence() {
    let env = environment();
    for (name, original_ok, cleanup_ok, ignored) in [
        ("parser-open-success", true, false, false),
        ("parser-close-success", false, true, false),
        ("parser-close-error", false, false, false),
        ("parser-unrestricted-cps", false, false, true),
    ] {
        let (left, expected, proof) = parser_transaction(original_ok, cleanup_ok, ignored);
        let goal = eq0(left, expected);
        TypeChecker::new(&env).check_type(&proof, &goal).unwrap();
        empty_closure(&env, &goal, &proof);
        capture(
            name,
            &goal,
            &proof,
            "accepted; complete returned state/outcome; three empty closures\n",
        );
    }
}

#[test]
fn parser_same_input_wrong_state_error_and_ignored_close_failure_refuse() {
    let env = environment();
    for (name, close_ok, wrong_state, wrong_error) in [
        ("wrong-restored-state", true, 5, 17),
        ("wrong-original-error", true, 8, 18),
        ("ignored-close-error", false, 8, 17),
    ] {
        let (left, _, proof) = parser_transaction(false, close_ok, false);
        let goal = eq0(
            left,
            response(Expr::nat_lit(wrong_state), outcome0(false, wrong_error)),
        );
        let error = TypeChecker::new(&env)
            .check_type(&proof, &goal)
            .unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "{error:?}"
        );
        capture(
            name,
            &goal,
            &proof,
            "TypeMismatch; same consumer input and proof, changed expected result\n",
        );
    }
}

#[test]
fn original_success_guard_cannot_be_replaced_with_cleanup() {
    let env = environment();
    let (left, _, proof) = parser_transaction(true, false, false);
    let goal = eq0(left, response(Expr::nat_lit(8), outcome0(false, 29)));
    let error = TypeChecker::new(&env)
        .check_type(&proof, &goal)
        .unwrap_err();
    assert!(
        matches!(error, KernelTypeError::TypeMismatch { .. }),
        "{error:?}"
    );
    capture(
        "wrong-success-guard",
        &goal,
        &proof,
        "TypeMismatch; successful parse cannot run failure cleanup\n",
    );
}
