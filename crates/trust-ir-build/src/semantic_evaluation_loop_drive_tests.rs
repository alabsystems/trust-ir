// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
use super::*;

fn environment() -> Environment {
    let mut env = clean_verify::eval_ir::shared_specification_with_stack(
        clean_verify::eval_ir::EvalIrVocabulary::ByteV1,
    )
    .unwrap()
    .env()
    .clone();
    install_loop_into(&mut env).unwrap();
    env
}
fn check(env: &Environment, goal: &Expr, proof: &Expr) {
    let mut tc = TypeChecker::new(env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.set_heartbeat_limit(HEARTBEAT_LIMIT);
    tc.set_max_cache_entries(CACHE_ENTRY_LIMIT);
    tc.check_type(goal, &Expr::prop()).unwrap();
    tc.check_type(proof, goal).unwrap();
    let audit = env.audit_certification(goal, proof);
    assert!(audit.is_certified(), "{audit:?}");
    for name in audit.dependencies {
        assert!(env.axiom_deps(&name).unwrap().is_empty(), "{name}");
        assert!(
            env.foundational_axiom_deps(&name).unwrap().is_empty(),
            "{name}"
        );
        assert!(env.trust_marker_deps(&name).unwrap().is_empty(), "{name}");
    }
}
fn stored(env: &Environment, names: &[&str]) -> Vec<(Vec<u8>, Vec<u8>)> {
    names
        .iter()
        .map(|name| {
            let info = env.get_const(&Name::from_string(name)).unwrap();
            (
                trust_ir::proof::encode_clean_expr_dag_v2(&info.type_).unwrap(),
                trust_ir::proof::encode_clean_expr_dag_v2(info.value.as_ref().unwrap()).unwrap(),
            )
        })
        .collect()
}
fn quantified_prefix(wrong_pulse: bool, wrong_fuel: bool) -> (Expr, Expr) {
    let mut sc = Scope::default();
    let s = sc.local(Expr::type_());
    let d = sc.local(Expr::type_());
    let sd = sum0(&s.term, &d.term);
    let pulse = sc.local(Expr::arrow(s.term.clone(), sd.clone()));
    let other = sc.local(pulse.ty.clone());
    let n = sc.local(k("Nat"));
    let initial = sc.local(s.term.clone());
    let fuel = if wrong_fuel {
        at("Nat.succ", [n.term.clone()])
    } else {
        n.term.clone()
    };
    let actual = drive(
        &s.term,
        &d.term,
        pulse.term.clone(),
        fuel,
        side0(&s.term, &d.term, false, initial.term.clone()),
    );
    let expected = prefix0(
        &s.term,
        &d.term,
        if wrong_pulse {
            other.term.clone()
        } else {
            pulse.term.clone()
        },
        n.term.clone(),
        initial.term.clone(),
    );
    let proof = at(
        LOOP_DRIVE_PREFIX,
        [
            s.term.clone(),
            d.term.clone(),
            pulse.term.clone(),
            n.term.clone(),
            initial.term.clone(),
        ],
    );
    let vars = [s, d, pulse, other, n, initial];
    (pis(&vars, eq0(&sd, actual, expected)), lams(&vars, proof))
}
#[test]
fn universally_quantified_actual_pulse_count_state_and_done_replay() {
    let mut env = environment();
    let original = [
        LOOP_PREFIX,
        LOOP_PREFIX_CONGR,
        LOOP_COMPLETE_TRANSFER,
        "ir_drive_v1",
    ];
    let before = stored(&env, &original);
    let count = env.num_constants();
    let options = ["maxHeartbeats", "tcMaxCacheEntries"].map(|name| env.get_option(name).cloned());
    install_loop_drive_into(&mut env).unwrap();
    assert_eq!(env.num_constants(), count + OWNED.len());
    assert_eq!(before, stored(&env, &original));
    assert_eq!(
        options,
        ["maxHeartbeats", "tcMaxCacheEntries"].map(|name| env.get_option(name).cloned())
    );
    for name in OWNED {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        assert!(info.level_params.is_empty(), "bridge is Type0: {name}");
    }
    let (goal, proof) = quantified_prefix(false, false);
    check(&env, &goal, &proof);
    for name in &OWNED[2..] {
        recheck_theorem(&env, name).unwrap();
    }
    assert_eq!(
        env.get_const(&Name::from_string(LOOP_PREFIX))
            .unwrap()
            .level_params
            .len(),
        1
    );
}
#[test]
fn actual_prefix_completion_retains_the_exact_payload_and_halted_equality() {
    let mut env = environment();
    install_loop_drive_into(&mut env).unwrap();
    let mut sc = Scope::default();
    let s = sc.local(Expr::type_());
    let d = sc.local(Expr::type_());
    let sd = sum0(&s.term, &d.term);
    let pulse = sc.local(Expr::arrow(s.term.clone(), sd.clone()));
    let n = sc.local(k("Nat"));
    let initial = sc.local(s.term.clone());
    let done = sc.local(d.term.clone());
    let pref = prefix0(
        &s.term,
        &d.term,
        pulse.term.clone(),
        n.term.clone(),
        initial.term.clone(),
    );
    let result = side0(&s.term, &d.term, true, done.term.clone());
    let h = sc.local(eq0(&sd, pref, result.clone()));
    let actual = drive(
        &s.term,
        &d.term,
        pulse.term.clone(),
        n.term.clone(),
        side0(&s.term, &d.term, false, initial.term.clone()),
    );
    let arguments = [
        s.term.clone(),
        d.term.clone(),
        pulse.term.clone(),
        n.term.clone(),
        initial.term.clone(),
        done.term.clone(),
        h.term.clone(),
    ];
    let payload = eq0(&sd, actual.clone(), result);
    let halted = eq0(
        &k("Bool"),
        Expr::app(halted(&s.term, &d.term), actual),
        k("Bool.true"),
    );
    let vars = [s, d, pulse, n, initial, done, h];
    check(
        &env,
        &pis(&vars, payload),
        &lams(&vars, at(LOOP_DRIVE_COMPLETE, arguments.clone())),
    );
    check(
        &env,
        &pis(&vars, halted),
        &lams(&vars, at(LOOP_DRIVE_HALT, arguments)),
    );
}
fn type_mismatch(env: &Environment, goal: &Expr, proof: &Expr) {
    let mut tc = TypeChecker::new(env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.set_heartbeat_limit(HEARTBEAT_LIMIT);
    tc.set_max_cache_entries(CACHE_ENTRY_LIMIT);
    tc.check_type(goal, &Expr::prop()).unwrap();
    let error = tc.check_type(proof, goal).unwrap_err();
    assert!(
        matches!(error, clean_kernel::tc::TypeError::TypeMismatch { .. }),
        "semantic mismatch required: {error:?}"
    );
}
#[test]
fn wrong_actual_pulse_fuel_and_suspended_completion_are_type_mismatches() {
    let mut env = environment();
    install_loop_drive_into(&mut env).unwrap();
    let (goal, proof) = quantified_prefix(false, false);
    check(&env, &goal, &proof);
    for (pulse, fuel) in [(true, false), (false, true)] {
        let (goal, proof) = quantified_prefix(pulse, fuel);
        type_mismatch(&env, &goal, &proof);
    }
    let mut sc = Scope::default();
    let s = sc.local(Expr::type_());
    let d = sc.local(Expr::type_());
    let sd = sum0(&s.term, &d.term);
    let pulse = sc.local(Expr::arrow(s.term.clone(), sd.clone()));
    let n = sc.local(k("Nat"));
    let initial = sc.local(s.term.clone());
    let suspended = sc.local(s.term.clone());
    let pref = prefix0(
        &s.term,
        &d.term,
        pulse.term.clone(),
        n.term.clone(),
        initial.term.clone(),
    );
    let waiting = side0(&s.term, &d.term, false, suspended.term.clone());
    let h = sc.local(eq0(&sd, pref.clone(), waiting.clone()));
    let actual = drive(
        &s.term,
        &d.term,
        pulse.term.clone(),
        n.term.clone(),
        side0(&s.term, &d.term, false, initial.term.clone()),
    );
    let prefix_proof = at(
        LOOP_DRIVE_PREFIX,
        [
            s.term.clone(),
            d.term.clone(),
            pulse.term.clone(),
            n.term.clone(),
            initial.term.clone(),
        ],
    );
    let exact = Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![one()]),
        [
            sd.clone(),
            actual.clone(),
            pref,
            waiting.clone(),
            prefix_proof,
            h.term.clone(),
        ],
    );
    let proof = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![one(), one()]),
        [
            sd,
            k("Bool"),
            actual.clone(),
            waiting,
            halted(&s.term, &d.term),
            exact,
        ],
    );
    let goal = eq0(
        &k("Bool"),
        Expr::app(halted(&s.term, &d.term), actual.clone()),
        k("Bool.true"),
    );
    let correctly_suspended = eq0(
        &k("Bool"),
        Expr::app(halted(&s.term, &d.term), actual),
        k("Bool.false"),
    );
    let vars = [s, d, pulse, n, initial, suspended, h];
    check(
        &env,
        &pis(&vars, correctly_suspended),
        &lams(&vars, proof.clone()),
    );
    type_mismatch(&env, &pis(&vars, goal), &lams(&vars, proof));
}
#[test]
fn owned_names_and_noncanonical_driver_refuse_without_replacement() {
    let mut env = environment();
    env.add_decl(Declaration::Definition {
        name: Name::from_string(LOOP_DRIVE_HALT),
        level_params: vec![],
        type_: k("Nat"),
        value: Expr::nat_lit(0),
        is_reducible: true,
    })
    .unwrap();
    let count = env.num_constants();
    assert!(install_loop_drive_into(&mut env).is_err());
    assert_eq!(count, env.num_constants());
    let mut fake = Environment::new();
    fake.init_bool().unwrap();
    install_loop_into(&mut fake).unwrap();
    let mut sc = Scope::default();
    let c = sc.local(Expr::type_());
    let h = sc.local(Expr::arrow(c.term.clone(), k("Bool")));
    let f = sc.local(Expr::arrow(c.term.clone(), c.term.clone()));
    let n = sc.local(k("Nat"));
    let x = sc.local(c.term.clone());
    add0(
        &mut fake,
        "ir_drive_v1",
        &[c.clone(), h, f, n, x.clone()],
        c.term,
        x.term,
        false,
    )
    .unwrap();
    let count = fake.num_constants();
    let error = install_loop_drive_into(&mut fake).unwrap_err();
    assert!(format!("{error:?}").contains("TypeMismatch"), "{error:?}");
    assert_eq!(count, fake.num_constants());
}
#[test]
fn an_active_caller_budget_is_never_refilled() {
    let mut env = environment();
    clean_kernel::tc::set_declaration_budget(1);
    let result = install_loop_drive_into(&mut env);
    let limit = clean_kernel::tc::declaration_budget_limit();
    let remaining = clean_kernel::tc::declaration_budget_remaining();
    clean_kernel::tc::clear_declaration_budget();
    assert!(result.is_err());
    assert_eq!(limit, 1);
    assert!(remaining <= 1);
}
