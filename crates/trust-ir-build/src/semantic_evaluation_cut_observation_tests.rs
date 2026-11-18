// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! General stateful consumer controls for the same-answer forward adapter.
use super::*;

fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn successor(mut value: Expr, count: usize) -> Expr {
    for _ in 0..count {
        value = Expr::app(Expr::const_str("Nat.succ"), value);
    }
    value
}
fn raw(state: Expr, failed: bool, payload: Expr) -> Expr {
    pair(
        &nat(),
        &outcome(&nat(), &nat()),
        state,
        apps(
            if failed { "Except.error" } else { "Except.ok" },
            [nat(), nat(), payload],
        ),
    )
}
fn conjunction(left: Expr, right: Expr) -> Expr {
    Expr::apps(Expr::const_str("And"), [left, right])
}
fn environment() -> Environment {
    let mut env = build_environment().unwrap();
    super::super::super::install_handle_into(&mut env).unwrap();
    install_loop_into(&mut env).unwrap();
    install_cut_run_into(&mut env).unwrap();
    install_cut_observation_into(&mut env).unwrap();
    env.init_nat().unwrap();
    env.init_and().unwrap();
    env
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
fn empty_closures(env: &Environment, name: &str) {
    let name = Name::from_string(name);
    assert!(env.axiom_deps(&name).unwrap().is_empty());
    assert!(env.foundational_axiom_deps(&name).unwrap().is_empty());
    assert!(env.trust_marker_deps(&name).unwrap().is_empty());
}

#[test]
fn cut_observation_install_preserves_complete_original_declarations_and_custody() {
    let mut missing = build_environment().unwrap();
    let count = missing.num_constants();
    assert!(install_cut_observation_into(&mut missing).is_err());
    assert_eq!(missing.num_constants(), count);

    let mut env = build_environment().unwrap();
    super::super::super::install_handle_into(&mut env).unwrap();
    install_loop_into(&mut env).unwrap();
    install_cut_run_into(&mut env).unwrap();
    let original = [RUN_TO_PULSE, RUN_TO_PULSE_CPS, IMAGE_TO_PULSE];
    let before = stored(&env, &original);
    let count = env.num_constants();
    install_cut_observation_into(&mut env).unwrap();
    assert_eq!(env.num_constants(), count + 1);
    assert_eq!(before, stored(&env, &original));
    for name in original.into_iter().chain([IMAGE_TO_PULSE_OBSERVATION]) {
        empty_closures(&env, name);
    }
    recheck_theorem(&env, RUN_TO_PULSE_CPS).unwrap();
    recheck_theorem(&env, IMAGE_TO_PULSE).unwrap();
    recheck_theorem(&env, IMAGE_TO_PULSE_OBSERVATION).unwrap();
    let names = [
        RUN_TO_PULSE,
        RUN_TO_PULSE_CPS,
        IMAGE_TO_PULSE,
        IMAGE_TO_PULSE_OBSERVATION,
    ];
    let installed = stored(&env, &names);
    let count = env.num_constants();
    assert!(install_cut_observation_into(&mut env).is_err());
    assert_eq!(env.num_constants(), count);
    assert_eq!(installed, stored(&env, &names));
}

#[test]
fn cut_observation_owned_name_collision_refuses_before_mutation() {
    let mut env = build_environment().unwrap();
    super::super::super::install_handle_into(&mut env).unwrap();
    install_loop_into(&mut env).unwrap();
    install_cut_run_into(&mut env).unwrap();
    env.init_nat().unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string(IMAGE_TO_PULSE_OBSERVATION),
        level_params: vec![],
        type_: nat(),
        value: Expr::nat_lit(7),
        is_reducible: true,
    })
    .unwrap();
    let names = [
        RUN_TO_PULSE,
        RUN_TO_PULSE_CPS,
        IMAGE_TO_PULSE,
        IMAGE_TO_PULSE_OBSERVATION,
    ];
    let before = stored(&env, &names);
    let count = env.num_constants();
    assert!(install_cut_observation_into(&mut env).is_err());
    assert_eq!(env.num_constants(), count);
    assert_eq!(before, stored(&env, &names));
}

#[derive(Clone, Copy, Debug)]
enum Mode {
    Continue,
    Success,
    Error,
}

fn computation(
    sc: &mut Scope,
    mode: Mode,
    payload: Expr,
    failure: Expr,
    post_steps: usize,
    payload_steps: usize,
) -> Expr {
    let state = sc.local(nat());
    let opt = option_type(&nat());
    let status = match mode {
        Mode::Continue => apps(
            "Except.ok",
            [nat(), opt.clone(), apps("Option.none", [nat()])],
        ),
        Mode::Success => apps(
            "Except.ok",
            [
                nat(),
                opt.clone(),
                apps("Option.some", [nat(), successor(payload, payload_steps)]),
            ],
        ),
        Mode::Error => apps(
            "Except.error",
            [nat(), opt.clone(), successor(failure, payload_steps)],
        ),
    };
    state.lam(pair(
        &nat(),
        &outcome(&nat(), &opt),
        successor(state.term.clone(), post_steps),
        status,
    ))
}

/// This terminal context really handles the returned computation. Success
/// increments its returned State and payload; failure increments its State
/// twice and keeps a changed failure payload. The invocation's initial zero
/// never replaces the returned State retained by the handled raw result.
fn terminal_context(sc: &mut Scope, extra_steps: usize) -> Expr {
    let answer = result(&nat(), &nat(), &nat());
    let observed = sc.local(answer);
    let ignored = sc.local(nat());
    let post = sc.local(nat());
    let value = sc.local(nat());
    let failure = sc.local(nat());
    let yes = value.lam(post.lam(raw(
        successor(post.term.clone(), 1 + extra_steps),
        false,
        successor(value.term.clone(), 1),
    )));
    let no = failure.lam(post.lam(raw(
        successor(post.term.clone(), 2 + extra_steps),
        true,
        successor(failure.term.clone(), 1),
    )));
    observed.lam(Expr::app(
        apps(
            super::super::super::HANDLE,
            [
                nat(),
                nat(),
                nat(),
                nat(),
                nat(),
                ignored.lam(observed.term.clone()),
                yes,
                no,
            ],
        ),
        Expr::nat_lit(0),
    ))
}

fn mapped(sc: &mut Scope, m: Expr, finish: Expr, residual: Expr, state: Expr) -> Expr {
    let done = result(&nat(), &nat(), &nat());
    let selected = sc.local(pulse_type(&nat(), &nat(), &nat()));
    cases(
        &nat(),
        &done,
        selected.lam(done.clone()),
        residual,
        finish,
        decode(&nat(), &nat(), &nat(), Expr::app(m, state)),
        false,
    )
}

struct Fixture {
    goal: Expr,
    proof: Expr,
    wrong_goals: Vec<(&'static str, Expr)>,
    effect_goal: Expr,
    effect_proof: Expr,
}

fn fixture(mode: Mode) -> Fixture {
    let mut sc = Scope::default();
    let input = sc.local(nat());
    let payload = sc.local(nat());
    let failure = sc.local(nat());
    let answer = result(&nat(), &nat(), &nat());
    let opt = option_type(&nat());
    let m = computation(
        &mut sc,
        mode,
        payload.term.clone(),
        failure.term.clone(),
        1,
        1,
    );
    let convert = |run| apps(TO_CPS, [nat(), nat(), opt.clone(), answer.clone(), run]);
    let code = convert(m.clone());
    let state = sc.local(nat());
    let yes = sc.local(continuation(&nat(), &opt, &answer));
    let no = sc.local(continuation(&nat(), &nat(), &answer));
    let image = lams(
        &[state.clone(), yes.clone(), no.clone()],
        refl(
            &answer,
            Expr::apps(
                code.clone(),
                [state.term.clone(), yes.term.clone(), no.term.clone()],
            ),
        ),
    );
    let finish = terminal_context(&mut sc, 0);
    let next = sc.local(nat());
    let residual = next.lam(raw(
        successor(next.term.clone(), 3),
        false,
        Expr::nat_lit(17),
    ));
    let (yes, no) = observation_channels(
        &mut sc,
        &nat(),
        &nat(),
        &nat(),
        &answer,
        residual.clone(),
        finish.clone(),
    );
    let left = Expr::apps(code.clone(), [input.term.clone(), yes.clone(), no.clone()]);
    let right = mapped(
        &mut sc,
        m.clone(),
        finish.clone(),
        residual.clone(),
        input.term.clone(),
    );
    let observation = eq(&answer, left.clone(), right.clone());
    let image_type = |run: Expr| {
        apps(
            super::super::super::CPS_IMAGE,
            [nat(), nat(), opt.clone(), answer.clone(), run, code.clone()],
        )
    };
    let actual_image = image_type(m.clone());
    let goal = conjunction(actual_image.clone(), observation.clone());
    let observed = apps(
        IMAGE_TO_PULSE_OBSERVATION,
        [
            nat(),
            nat(),
            nat(),
            answer.clone(),
            m.clone(),
            code.clone(),
            image.clone(),
            finish.clone(),
            residual.clone(),
            input.term.clone(),
        ],
    );
    let proof = Expr::apps(
        Expr::const_str("And.intro"),
        [actual_image.clone(), observation, image, observed],
    );
    let mut wrong_goals = Vec::new();
    let wrong_state = computation(
        &mut sc,
        mode,
        payload.term.clone(),
        failure.term.clone(),
        0,
        1,
    );
    let wrong_right = mapped(
        &mut sc,
        wrong_state.clone(),
        finish.clone(),
        residual.clone(),
        input.term.clone(),
    );
    wrong_goals.push((
        "stale-returned-state",
        conjunction(actual_image.clone(), eq(&answer, left.clone(), wrong_right)),
    ));
    // The image claim changes semantically, while the same positive proof and
    // the observation conjunct retain their exact original structure.
    wrong_goals.push((
        "changed-actual-image",
        conjunction(
            image_type(wrong_state),
            eq(&answer, left.clone(), right.clone()),
        ),
    ));
    let ignored_state = sc.local(nat());
    let ignored_yes = sc.local(continuation(&nat(), &opt, &answer));
    let ignored_no = sc.local(continuation(&nat(), &nat(), &answer));
    let wrong_code = lams(
        &[ignored_state.clone(), ignored_yes, ignored_no],
        raw(ignored_state.term, false, Expr::nat_lit(99)),
    );
    wrong_goals.push((
        "changed-actual-code",
        conjunction(
            actual_image.clone(),
            eq(
                &answer,
                Expr::apps(wrong_code, [input.term.clone(), yes, no]),
                right.clone(),
            ),
        ),
    ));
    let wrong_tag = computation(
        &mut sc,
        match mode {
            Mode::Continue | Mode::Error => Mode::Success,
            Mode::Success => Mode::Continue,
        },
        payload.term.clone(),
        failure.term.clone(),
        1,
        1,
    );
    let wrong_right = mapped(
        &mut sc,
        wrong_tag,
        finish.clone(),
        residual.clone(),
        input.term.clone(),
    );
    wrong_goals.push((
        "changed-continue-terminal-tag",
        conjunction(actual_image.clone(), eq(&answer, left.clone(), wrong_right)),
    ));
    if !matches!(mode, Mode::Continue) {
        let wrong_payload = computation(
            &mut sc,
            mode,
            payload.term.clone(),
            failure.term.clone(),
            1,
            2,
        );
        let wrong_right = mapped(
            &mut sc,
            wrong_payload,
            finish.clone(),
            residual.clone(),
            input.term.clone(),
        );
        wrong_goals.push((
            "changed-terminal-payload",
            conjunction(actual_image.clone(), eq(&answer, left.clone(), wrong_right)),
        ));
        let wrong_finish = terminal_context(&mut sc, 1);
        let wrong_right = mapped(&mut sc, m, wrong_finish, residual, input.term.clone());
        wrong_goals.push((
            "changed-terminal-context-effects",
            conjunction(actual_image, eq(&answer, left, wrong_right)),
        ));
    }
    let expected = match mode {
        Mode::Continue => raw(successor(input.term.clone(), 4), false, Expr::nat_lit(17)),
        Mode::Success => raw(
            successor(input.term.clone(), 2),
            false,
            successor(payload.term.clone(), 2),
        ),
        Mode::Error => raw(
            successor(input.term.clone(), 3),
            true,
            successor(failure.term.clone(), 2),
        ),
    };
    let parameters = [input, payload, failure];
    let levels = [(Name::from_string("u"), Level::zero())];
    let close_goal = |goal| pis(&parameters, goal).instantiate_level_params(&levels);
    Fixture {
        goal: close_goal(goal),
        proof: lams(&parameters, proof).instantiate_level_params(&levels),
        wrong_goals: wrong_goals
            .into_iter()
            .map(|(label, goal)| (label, close_goal(goal)))
            .collect(),
        effect_goal: close_goal(eq(&answer, right, expected.clone())),
        effect_proof: lams(&parameters, refl(&answer, expected)).instantiate_level_params(&levels),
    }
}

fn decoded(bytes: &[u8]) -> Expr {
    trust_ir::proof::decode_clean_expr_dag_v2(bytes).unwrap()
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
        assert!(env.axiom_deps(&name).unwrap().is_empty());
        assert!(env.foundational_axiom_deps(&name).unwrap().is_empty());
        assert!(env.trust_marker_deps(&name).unwrap().is_empty());
    }
}

#[test]
fn cut_observation_retains_continue_and_effectful_terminal_state_value_and_error() {
    let env = environment();
    for mode in [Mode::Continue, Mode::Success, Mode::Error] {
        let f = fixture(mode);
        let encode = |term| trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap();
        check(
            &env,
            &decoded(&encode(&f.goal)),
            &decoded(&encode(&f.proof)),
        );
        check(
            &env,
            &decoded(&encode(&f.effect_goal)),
            &decoded(&encode(&f.effect_proof)),
        );
    }
}

#[test]
fn cut_observation_same_proof_refuses_changed_state_code_payload_context_and_image() {
    let env = environment();
    for mode in [Mode::Continue, Mode::Success, Mode::Error] {
        let f = fixture(mode);
        let proof_bytes = trust_ir::proof::encode_clean_expr_dag_v2(&f.proof).unwrap();
        let proof = decoded(&proof_bytes);
        check(&env, &f.goal, &proof);
        for (label, goal) in f.wrong_goals {
            let goal = decoded(&trust_ir::proof::encode_clean_expr_dag_v2(&goal).unwrap());
            assert_eq!(
                proof_bytes,
                trust_ir::proof::encode_clean_expr_dag_v2(&proof).unwrap()
            );
            let mut tc = TypeChecker::new(&env);
            tc.set_allow_unsafe(false);
            tc.set_allow_partial(false);
            tc.set_heartbeat_limit(HEARTBEAT_LIMIT);
            tc.set_max_cache_entries(CACHE_ENTRY_LIMIT);
            tc.check_type(&goal, &Expr::prop()).unwrap();
            let result = tc.check_type(&proof, &goal);
            assert!(
                matches!(
                    result,
                    Err(clean_kernel::tc::TypeError::TypeMismatch { .. })
                ),
                "{mode:?}/{label}: {result:?}"
            );
            assert!(!tc.heartbeat_spent(), "{mode:?}/{label}");
        }
    }
}
