// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
use super::*;

fn at(name: &str, levels: usize, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::zero(); levels]),
        args,
    )
}
fn n() -> Expr {
    Expr::const_str("Nat")
}
fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn boolean(value: bool) -> Expr {
    Expr::const_str(if value { "Bool.true" } else { "Bool.false" })
}
fn product(a: Expr, b: Expr) -> Expr {
    at("Prod", 2, [a, b])
}
fn packed(a: Expr, b: Expr, x: Expr, y: Expr) -> Expr {
    at("Prod.mk", 2, [a, b, x, y])
}
fn equality(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
fn reflexive(ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, value],
    )
}
fn state_ty() -> Expr {
    product(n(), bool_ty())
}
fn state(counter: u64, flag: bool) -> Expr {
    packed(n(), bool_ty(), nat(counter), boolean(flag))
}
fn status_ty() -> Expr {
    at("Except", 2, [state_ty(), n()])
}
fn raw(post: Expr, value: u64, failure: Option<(u64, bool)>) -> Expr {
    let status = match failure {
        Some((code, detail)) => at("Except.error", 2, [state_ty(), n(), state(code, detail)]),
        None => at("Except.ok", 2, [state_ty(), n(), nat(value)]),
    };
    packed(state_ty(), status_ty(), post, status)
}
fn carrier() -> Expr {
    product(at("Option", 1, [n()]), n())
}
fn expected(counter: u64, value: u64) -> Expr {
    packed(
        at("Option", 1, [n()]),
        n(),
        at("Option.some", 1, [n(), nat(counter)]),
        nat(value),
    )
}
fn measure() -> Expr {
    let mut sc = Scope::default();
    let state = sc.local(state_ty());
    let value = sc.local(n());
    lams(
        &[state.clone(), value.clone()],
        packed(
            at("Option", 1, [n()]),
            n(),
            at(
                "Option.some",
                1,
                [n(), at("Prod.fst", 2, [n(), bool_ty(), state.term])],
            ),
            value.term,
        ),
    )
}
fn observer(m: Expr, measure: Expr, expected: Expr, raw: Expr) -> Expr {
    at(
        NORMAL_VALUE_OBSERVATION,
        1,
        [state_ty(), state_ty(), n(), m, measure, expected, raw],
    )
}
fn rule(m: Expr, measure: Expr, expected: Expr, raw: Expr, premise: Option<Expr>) -> Expr {
    let mut args = vec![state_ty(), state_ty(), n(), m, measure, expected, raw];
    args.extend(premise);
    at(NORMAL_VALUE_OBSERVATION_POST, 1, args)
}
fn goal(m: Expr, measure: Expr, expected: Expr, raw: Expr) -> Expr {
    let mut sc = Scope::default();
    let state = sc.local(state_ty());
    let value = sc.local(n());
    let predicate = lams(
        &[state.clone(), value.clone()],
        equality(m, Expr::apps(measure, [state.term, value.term]), expected),
    );
    at(
        NORMAL_POST,
        1,
        [state_ty(), state_ty(), n(), predicate, raw],
    )
}
fn environment() -> Environment {
    let mut env = Environment::default();
    env.set_option("maxHeartbeats".into(), Some(HEARTBEAT_LIMIT.to_string()));
    env.set_option(
        "tcMaxCacheEntries".into(),
        Some(CACHE_ENTRY_LIMIT.to_string()),
    );
    install_into(&mut env).unwrap();
    install_normal_value_post_into(&mut env).unwrap();
    env.init_nat().unwrap();
    env.init_option().unwrap();
    env
}
fn checked(name: &str, env: &Environment, proof: Expr, goal: Expr, accepted: bool) {
    // Transport both exact operands through the maintained bounded DAG decoder.
    let roundtrip = |term: &Expr| {
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
        assert_eq!(&decoded, term);
        (decoded, bytes)
    };
    let (proof, proof_wire) = roundtrip(&proof);
    let (goal, goal_wire) = roundtrip(&goal);
    let mut tc = TypeChecker::with_mode(env, env.mode());
    tc.set_heartbeat_limit(HEARTBEAT_LIMIT);
    tc.set_max_cache_entries(CACHE_ENTRY_LIMIT);
    tc.check_type(&goal, &Expr::sort(Level::zero())).unwrap();
    let result = tc.check_type(&proof, &goal);
    assert!(!tc.heartbeat_spent(), "{name}");
    let verdict = if accepted {
        result.unwrap();
        let audit = env.audit_certification(&goal, &proof);
        assert!(audit.is_certified(), "{name}: {audit:?}");
        "Accepted; no kernel budget exhaustion; rooted certification accepted".to_owned()
    } else {
        let error = format!(
            "{:?}",
            result.expect_err("semantic mutation or missing premise must refuse")
        );
        assert!(
            error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
            "{name}: {error}"
        );
        error
    };
    eprintln!(
        "value-normal-post {name}: {}",
        if accepted {
            "Accepted; rooted certification accepted"
        } else {
            "TypeMismatch; no kernel budget exhaustion"
        }
    );
    if let Some(root) = std::env::var_os("TRUST_IR_VALUE_POST_ARTIFACT_DIR") {
        let dir = std::path::PathBuf::from(root).join(name);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("proof.dag"), proof_wire).unwrap();
        std::fs::write(dir.join("goal.dag"), goal_wire).unwrap();
        std::fs::write(dir.join("verdict.txt"), verdict).unwrap();
    }
}
fn exact(
    name: &str,
    env: &Environment,
    m: Expr,
    measurement: Expr,
    expected: Expr,
    raw: Expr,
) -> Expr {
    let h = reflexive(m.clone(), expected.clone());
    checked(
        &format!("{name}-premise"),
        env,
        h.clone(),
        equality(
            m.clone(),
            observer(
                m.clone(),
                measurement.clone(),
                expected.clone(),
                raw.clone(),
            ),
            expected.clone(),
        ),
        true,
    );
    let proof = rule(
        m.clone(),
        measurement.clone(),
        expected.clone(),
        raw.clone(),
        Some(h),
    );
    checked(
        name,
        env,
        proof.clone(),
        goal(m, measurement, expected, raw),
        true,
    );
    proof
}
#[test]
fn actual_returned_state_and_value_are_both_required_by_the_same_proof() {
    let env = environment();
    let result = raw(state(7, true), 4, None);
    let target = expected(7, 4);
    let proof = exact(
        "compound-actual-state-value",
        &env,
        carrier(),
        measure(),
        target.clone(),
        result.clone(),
    );
    for (name, changed) in [
        ("wrong-returned-state", raw(state(3, false), 4, None)),
        ("wrong-returned-value", raw(state(7, true), 5, None)),
    ] {
        checked(
            name,
            &env,
            proof.clone(),
            goal(carrier(), measure(), target.clone(), changed),
            false,
        );
    }
    checked(
        "wrong-expected",
        &env,
        proof.clone(),
        goal(carrier(), measure(), expected(3, 4), result.clone()),
        false,
    );
    checked(
        "missing-equality-premise",
        &env,
        rule(carrier(), measure(), target.clone(), result.clone(), None),
        goal(carrier(), measure(), target, result),
        false,
    );
    // A measurement which forgets the flag cannot establish complete State equality.
    checked(
        "stronger-whole-state",
        &env,
        proof,
        equality(state_ty(), state(7, true), state(7, false)),
        false,
    );
}
#[test]
fn errors_preserve_complete_raw_state_error_and_value_type_without_a_normal_contract() {
    let env = environment();
    for (name, failure) in [
        ("compound-error-91", (91, false)),
        ("compound-error-93", (93, true)),
    ] {
        let result = raw(state(11, true), 0, Some(failure));
        let _proof = exact(name, &env, carrier(), measure(), expected(7, 4), result);
    }
    // An error's fallback equality cannot certify the same State on normal return.
    let result = raw(state(11, true), 4, None);
    let target = expected(7, 4);
    checked(
        "error-premise-used-on-normal-result",
        &env,
        rule(
            carrier(),
            measure(),
            target.clone(),
            result.clone(),
            Some(reflexive(carrier(), target.clone())),
        ),
        goal(carrier(), measure(), target, result),
        false,
    );
}
fn token_measure() -> Expr {
    let mut sc = Scope::default();
    let state = sc.local(state_ty());
    let token = sc.local(n());
    let pred = sc.local(n());
    let ih = sc.local(at("Option", 1, [n()]));
    let ignored = sc.local(n());
    let fields = at(
        "Option.some",
        1,
        [n(), at("Prod.fst", 2, [n(), bool_ty(), state.term.clone()])],
    );
    lams(
        &[state, token.clone()],
        Expr::apps(
            Expr::const_(
                Name::from_string("Nat.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                ignored.lam(at("Option", 1, [n()])),
                at("Option.some", 1, [n(), nat(7)]),
                lams(&[pred, ih], fields),
                token.term,
            ],
        ),
    )
}
#[test]
fn token_zero_fallback_proves_only_its_value_sensitive_predicate() {
    let env = environment();
    let m = at("Option", 1, [n()]);
    let target = at("Option.some", 1, [n(), nat(7)]);
    let result = raw(state(91, true), 0, None);
    let proof = exact(
        "token-zero-dependent-fallback",
        &env,
        m.clone(),
        token_measure(),
        target.clone(),
        result.clone(),
    );
    let mut sc = Scope::default();
    let post = sc.local(state_ty());
    let ignored = sc.local(n());
    let unconditional = lams(
        &[post.clone(), ignored],
        at(
            "Option.some",
            1,
            [n(), at("Prod.fst", 2, [n(), bool_ty(), post.term])],
        ),
    );
    checked(
        "token-zero-cannot-prove-unconditional-health",
        &env,
        proof.clone(),
        goal(m.clone(), unconditional, target.clone(), result),
        false,
    );
    checked(
        "token-zero-proof-cannot-certify-nonzero",
        &env,
        proof,
        goal(
            m.clone(),
            token_measure(),
            target.clone(),
            raw(state(91, true), 1, None),
        ),
        false,
    );
    let _proof = exact(
        "nonzero-token-reads-actual-state",
        &env,
        m,
        token_measure(),
        target,
        raw(state(7, true), 2, None),
    );
}
fn ordinary_run(failure: bool) -> Expr {
    let mut sc = Scope::default();
    let value = sc.local(n());
    let incoming = sc.local(state_ty());
    let counter = at("Prod.fst", 2, [n(), bool_ty(), incoming.term.clone()]);
    let changed = packed(
        n(),
        bool_ty(),
        Expr::app(Expr::const_str("Nat.succ"), counter),
        boolean(true),
    );
    let status = if failure {
        at("Except.error", 2, [state_ty(), n(), state(91, false)])
    } else {
        at(
            "Except.ok",
            2,
            [
                state_ty(),
                n(),
                Expr::app(Expr::const_str("Nat.succ"), value.term.clone()),
            ],
        )
    };
    let continuation = lams(
        &[value, incoming],
        packed(state_ty(), status_ty(), changed, status),
    );
    let first = at(PURE, 1, [state_ty(), state_ty(), n(), nat(4)]);
    at(
        BIND,
        1,
        [
            state_ty(),
            state_ty(),
            n(),
            n(),
            first,
            continuation,
            state(3, false),
        ],
    )
}
#[test]
fn ordinary_bind_run_uses_its_changed_returned_state_and_payload() {
    let env = environment();
    for failure in [false, true] {
        let result = ordinary_run(failure);
        let expected_raw = if failure {
            raw(state(4, true), 0, Some((91, false)))
        } else {
            raw(state(4, true), 5, None)
        };
        let raw_ty = product(state_ty(), status_ty());
        checked(
            if failure {
                "ordinary-bind-error-raw"
            } else {
                "ordinary-bind-normal-raw"
            },
            &env,
            reflexive(raw_ty.clone(), result.clone()),
            equality(raw_ty, result.clone(), expected_raw),
            true,
        );
        let _proof = exact(
            if failure {
                "ordinary-bind-error-post"
            } else {
                "ordinary-bind-normal-post"
            },
            &env,
            carrier(),
            measure(),
            expected(4, 5),
            result,
        );
    }
}
#[test]
fn compound_carrier_contains_types_in_a_higher_universe() {
    let env = environment();
    let one = Level::succ(Level::zero());
    let types = Expr::sort(one.clone());
    let call = |name: &str, count: usize, args: Vec<Expr>| {
        Expr::apps(
            Expr::const_(Name::from_string(name), vec![one.clone(); count]),
            args,
        )
    };
    let m = call("Prod", 2, vec![types.clone(), types.clone()]);
    let target = call(
        "Prod.mk",
        2,
        vec![types.clone(), types.clone(), n(), bool_ty()],
    );
    let mut sc = Scope::default();
    let state = sc.local(types.clone());
    let value = sc.local(types.clone());
    let measurement = lams(
        &[state.clone(), value.clone()],
        call(
            "Prod.mk",
            2,
            vec![types.clone(), types.clone(), state.term, value.term],
        ),
    );
    let status = call("Except", 2, vec![types.clone(), types.clone()]);
    let result = call(
        "Prod.mk",
        2,
        vec![
            types.clone(),
            status,
            n(),
            call(
                "Except.ok",
                2,
                vec![types.clone(), types.clone(), bool_ty()],
            ),
        ],
    );
    let h = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(one.clone())]),
        [m.clone(), target.clone()],
    );
    let proof = call(
        NORMAL_VALUE_OBSERVATION_POST,
        1,
        vec![
            types.clone(),
            types.clone(),
            types.clone(),
            m.clone(),
            measurement.clone(),
            target.clone(),
            result.clone(),
            h,
        ],
    );
    let state = sc.local(types.clone());
    let value = sc.local(types.clone());
    let predicate = lams(
        &[state.clone(), value.clone()],
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(one.clone())]),
            [m, Expr::apps(measurement, [state.term, value.term]), target],
        ),
    );
    let goal = call(
        NORMAL_POST,
        1,
        vec![types.clone(), types.clone(), types, predicate, result],
    );
    checked("higher-universe-compound-carrier", &env, proof, goal, true);
}
#[test]
fn bundle_preserves_original_bodies_and_empty_authority_closures() {
    let env = environment();
    let mut original = Environment::default();
    install_normal_post_into(&mut original).unwrap();
    for name in [NORMAL_POST, NORMAL_OBSERVATION, NORMAL_OBSERVATION_POST] {
        assert_eq!(
            original.get_const(&Name::from_string(name)),
            env.get_const(&Name::from_string(name))
        );
    }
    for endpoint in [NORMAL_OBSERVATION_POST, NORMAL_VALUE_OBSERVATION_POST] {
        recheck_theorem(&env, endpoint).unwrap();
        let name = Name::from_string(endpoint);
        assert!(env.axiom_deps(&name).unwrap().is_empty());
        assert!(env.foundational_axiom_deps(&name).unwrap().is_empty());
        assert!(env.trust_marker_deps(&name).unwrap().is_empty());
    }
    let defaults = build_environment().unwrap();
    for name in OWNED {
        assert!(defaults.get_const(&Name::from_string(name)).is_none());
    }
}
#[test]
fn every_bundle_name_collision_refuses_before_any_mutation() {
    for name in OWNED {
        let mut env = Environment::default();
        env.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            is_reducible: true,
        })
        .unwrap();
        env.set_option("maxHeartbeats".into(), Some("1".into()));
        env.set_option("tcMaxCacheEntries".into(), Some("3".into()));
        let before = (env.num_constants(), env.generation());
        let refused = install_normal_value_post_into(&mut env).unwrap_err();
        assert_eq!(refused.declaration, name);
        assert_eq!(before, (env.num_constants(), env.generation()));
        assert_eq!(env.get_option("maxHeartbeats"), Some(&Some("1".into())));
        assert_eq!(env.get_option("tcMaxCacheEntries"), Some(&Some("3".into())));
    }
    let mut original = Environment::default();
    install_normal_post_into(&mut original).unwrap();
    let before = (original.num_constants(), original.generation());
    assert!(install_normal_value_post_into(&mut original).is_err());
    assert_eq!(before, (original.num_constants(), original.generation()));
    let mut env = environment();
    let before = (env.num_constants(), env.generation());
    assert!(install_normal_value_post_into(&mut env).is_err());
    assert_eq!(before, (env.num_constants(), env.generation()));
}
