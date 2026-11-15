// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Preserve a frame on success while retaining arbitrary failure frame/state.
//! Raw errors carry their actual post-frame explicitly. This is not a provider
//! fidelity, rollback, ownership, termination or source-machine admission.
use super::*;
pub const SUCCESS_FRAME_OBSERVATION: &str = "TrustIR.Eval.SuccessFrame.observation";
pub const SUCCESS_FRAME_RUN: &str = "TrustIR.Eval.SuccessFrame.run";
pub const SUCCESS_FRAME_PROJECTION: &str = "TrustIR.Eval.SuccessFrame.projection";
pub const SUCCESS_FRAME_EXPOSE: &str = "TrustIR.Eval.SuccessFrame.expose";
pub const SUCCESS_FRAME_PRESERVES: &str = "TrustIR.Eval.SuccessFrame.preserves_success";
pub const SUCCESS_FRAME_ERROR: &str = "TrustIR.Eval.SuccessFrame.error";
pub const SUCCESS_FRAME_BIND_CONSTANT_OBSERVER: &str =
    "TrustIR.Eval.SuccessFrame.bind_constant_observer";
pub const SUCCESS_FRAME_BIND_PRESERVES: &str = "TrustIR.Eval.SuccessFrame.bind_preserves_success";
pub const SUCCESS_FRAME_BIND: &str = "TrustIR.Eval.SuccessFrame.bind_observation";
pub const SUCCESS_FRAME_CPS_OBSERVER: &str = "TrustIR.Eval.SuccessFrame.cps_observer";
pub const SUCCESS_FRAME_BASE: &str = "TrustIR.Eval.SuccessFrame.base_projection";
pub const SUCCESS_FRAME_DECLARATIONS: [&str; 11] = [
    SUCCESS_FRAME_OBSERVATION,
    SUCCESS_FRAME_RUN,
    SUCCESS_FRAME_PROJECTION,
    SUCCESS_FRAME_EXPOSE,
    SUCCESS_FRAME_PRESERVES,
    SUCCESS_FRAME_ERROR,
    SUCCESS_FRAME_BIND,
    SUCCESS_FRAME_CPS_OBSERVER,
    SUCCESS_FRAME_BASE,
    SUCCESS_FRAME_BIND_PRESERVES,
    SUCCESS_FRAME_BIND_CONSTANT_OBSERVER,
];
fn observe(s: &Expr, f: &Expr, e: &Expr, a: &Expr, frame: Expr, raw: Expr) -> Expr {
    apps(
        SUCCESS_FRAME_OBSERVATION,
        [s.clone(), f.clone(), e.clone(), a.clone(), frame, raw],
    )
}
fn framed(s: &Expr, f: &Expr, e: &Expr, a: &Expr, raw: Expr) -> Expr {
    apps(
        SUCCESS_FRAME_RUN,
        [s.clone(), f.clone(), e.clone(), a.clone(), raw],
    )
}
fn project(s: &Expr, f: &Expr, e: &Expr, a: &Expr, initial: Expr, observed: Expr) -> Expr {
    apps(
        SUCCESS_FRAME_PROJECTION,
        [
            s.clone(),
            f.clone(),
            e.clone(),
            a.clone(),
            initial,
            observed,
        ],
    )
}
pub fn install_success_framing_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in SUCCESS_FRAME_DECLARATIONS {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    env.init_prod()
        .map_err(|e| error(SUCCESS_FRAME_OBSERVATION, e))?;
    env.init_except_t()
        .map_err(|e| error(SUCCESS_FRAME_OBSERVATION, e))?;
    definitions(env)?;
    laws(env)?;
    bind_law(env)?;
    composition::install(env)?;
    cps_observer_law(env)?;
    base_projection_law(env)?;
    for name in [
        SUCCESS_FRAME_EXPOSE,
        SUCCESS_FRAME_PRESERVES,
        SUCCESS_FRAME_ERROR,
        SUCCESS_FRAME_BIND,
        SUCCESS_FRAME_BIND_PRESERVES,
        SUCCESS_FRAME_BIND_CONSTANT_OBSERVER,
        SUCCESS_FRAME_CPS_OBSERVER,
        SUCCESS_FRAME_BASE,
    ] {
        recheck_theorem(env, name)?;
    }
    Ok(())
}
fn definitions(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a] = sc.types();
    let sf = prod(&s.term, &f.term);
    let fe = prod(&f.term, &e.term);
    let target = result(&sf, &e.term, &a.term);
    let frame = sc.local(f.term.clone());
    let observed = sc.local(result(&s.term, &fe, &a.term));
    let major = sc.local(observed.ty.clone());
    let post = sc.local(s.term.clone());
    let status = sc.local(outcome(&fe, &a.term));
    let failure = sc.local(fe.clone());
    let value = sc.local(a.term.clone());
    let mk = |frame: Expr, status: Expr| {
        pair(
            &sf,
            &outcome(&e.term, &a.term),
            pair(&s.term, &f.term, post.term.clone(), frame),
            status,
        )
    };
    let failure_status = apps(
        "Except.error",
        [
            e.term.clone(),
            a.term.clone(),
            projection(1, &f.term, &e.term, failure.term.clone()),
        ],
    );
    let success_status = apps(
        "Except.ok",
        [e.term.clone(), a.term.clone(), value.term.clone()],
    );
    let cases = outcome_cases(
        &fe,
        &a.term,
        status.lam(target.clone()),
        failure.lam(mk(
            projection(0, &f.term, &e.term, failure.term.clone()),
            failure_status,
        )),
        value.lam(mk(frame.term.clone(), success_status)),
        status.term.clone(),
        false,
    );
    let body = result_cases(
        &s.term,
        &fe,
        &a.term,
        major.lam(target.clone()),
        lams(&[post, status], cases),
        observed.term.clone(),
        false,
    );
    add(
        env,
        SUCCESS_FRAME_OBSERVATION,
        &[
            s.clone(),
            f.clone(),
            e.clone(),
            a.clone(),
            frame.clone(),
            observed,
        ],
        target.clone(),
        body,
        false,
    )?;
    let reader = sc.local(Expr::arrow(f.term.clone(), run(&s.term, &fe, &a.term)));
    let state = sc.local(sf.clone());
    let input_frame = projection(1, &s.term, &f.term, state.term.clone());
    let body = observe(
        &s.term,
        &f.term,
        &e.term,
        &a.term,
        input_frame.clone(),
        Expr::apps(
            reader.term.clone(),
            [
                input_frame,
                projection(0, &s.term, &f.term, state.term.clone()),
            ],
        ),
    );
    add(
        env,
        SUCCESS_FRAME_RUN,
        &[s.clone(), f.clone(), e.clone(), a.clone(), reader, state],
        target.clone(),
        body,
        false,
    )?;
    let full = sc.local(target.clone());
    let status = sc.local(outcome(&e.term, &a.term));
    let error_value = sc.local(e.term.clone());
    let ok_value = sc.local(a.term.clone());
    let post_frame = projection(
        1,
        &s.term,
        &f.term,
        projection(0, &sf, &outcome(&e.term, &a.term), full.term.clone()),
    );
    let body = outcome_cases(
        &e.term,
        &a.term,
        status.lam(f.term.clone()),
        error_value.lam(frame.term.clone()),
        ok_value.lam(post_frame),
        projection(1, &sf, &outcome(&e.term, &a.term), full.term.clone()),
        false,
    );
    add(
        env,
        SUCCESS_FRAME_PROJECTION,
        &[s, f.clone(), e, a, frame, full],
        f.term,
        body,
        false,
    )
}
fn laws(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a] = sc.types();
    let sf = prod(&s.term, &f.term);
    let fe = prod(&f.term, &e.term);
    let raw = result(&s.term, &fe, &a.term);
    let target = result(&sf, &e.term, &a.term);
    let m = sc.local(Expr::arrow(f.term.clone(), run(&s.term, &fe, &a.term)));
    let state = sc.local(sf.clone());
    let frame = projection(1, &s.term, &f.term, state.term.clone());
    let value = Expr::apps(
        m.term.clone(),
        [
            frame.clone(),
            projection(0, &s.term, &f.term, state.term.clone()),
        ],
    );
    let left = Expr::app(
        framed(&s.term, &f.term, &e.term, &a.term, m.term.clone()),
        state.term.clone(),
    );
    let right = observe(
        &s.term,
        &f.term,
        &e.term,
        &a.term,
        frame.clone(),
        value.clone(),
    );
    add(
        env,
        SUCCESS_FRAME_EXPOSE,
        &[
            s.clone(),
            f.clone(),
            e.clone(),
            a.clone(),
            m.clone(),
            state.clone(),
        ],
        eq(&target, left.clone(), right),
        refl(&target, left),
        true,
    )?;
    let equation = |observed| {
        eq(
            &f.term,
            project(
                &s.term,
                &f.term,
                &e.term,
                &a.term,
                frame.clone(),
                observe(&s.term, &f.term, &e.term, &a.term, frame.clone(), observed),
            ),
            frame.clone(),
        )
    };
    let major = sc.local(raw.clone());
    let post = sc.local(s.term.clone());
    let status = sc.local(outcome(&fe, &a.term));
    let failure = sc.local(fe.clone());
    let ok_value = sc.local(a.term.clone());
    let inner = outcome_cases(
        &fe,
        &a.term,
        status.lam(equation(pair(
            &s.term,
            &outcome(&fe, &a.term),
            post.term.clone(),
            status.term.clone(),
        ))),
        failure.lam(refl(&f.term, frame.clone())),
        ok_value.lam(refl(&f.term, frame.clone())),
        status.term.clone(),
        true,
    );
    let proof = result_cases(
        &s.term,
        &fe,
        &a.term,
        major.lam(equation(major.term.clone())),
        lams(&[post, status], inner),
        value.clone(),
        true,
    );
    add(
        env,
        SUCCESS_FRAME_PRESERVES,
        &[s.clone(), f.clone(), e.clone(), a.clone(), m, state],
        equation(value),
        proof,
        true,
    )?;
    let initial = sc.local(f.term.clone());
    let post = sc.local(s.term.clone());
    let error_frame = sc.local(f.term.clone());
    let error_value = sc.local(e.term.clone());
    let error = apps(
        "Except.error",
        [
            fe.clone(),
            a.term.clone(),
            pair(
                &f.term,
                &e.term,
                error_frame.term.clone(),
                error_value.term.clone(),
            ),
        ],
    );
    let left = observe(
        &s.term,
        &f.term,
        &e.term,
        &a.term,
        initial.term.clone(),
        pair(&s.term, &outcome(&fe, &a.term), post.term.clone(), error),
    );
    let right = pair(
        &sf,
        &outcome(&e.term, &a.term),
        pair(
            &s.term,
            &f.term,
            post.term.clone(),
            error_frame.term.clone(),
        ),
        apps(
            "Except.error",
            [e.term.clone(), a.term.clone(), error_value.term.clone()],
        ),
    );
    add(
        env,
        SUCCESS_FRAME_ERROR,
        &[s, f, e, a, initial, post, error_frame, error_value],
        eq(&target, left.clone(), right),
        refl(&target, left),
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    fn z(name: &str, levels: usize, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string(name), vec![Level::zero(); levels]),
            args,
        )
    }
    fn proof_at(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string(name), vec![Level::succ(Level::zero())]),
            args,
        )
    }
    fn n() -> Expr {
        Expr::const_str("Nat")
    }
    fn pair0(ty: Expr, a: Expr, b: Expr) -> Expr {
        z("Prod.mk", 2, [n(), ty, a, b])
    }
    fn environment() -> Environment {
        let mut env = build_environment().unwrap();
        install_success_framing_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env
    }
    #[test]
    fn success_frame_laws_are_checked_and_rooted_without_an_error_frame_invariant() {
        let mut env = environment();
        for name in [
            SUCCESS_FRAME_EXPOSE,
            SUCCESS_FRAME_PRESERVES,
            SUCCESS_FRAME_ERROR,
            SUCCESS_FRAME_BIND,
            SUCCESS_FRAME_CPS_OBSERVER,
            SUCCESS_FRAME_BASE,
        ] {
            recheck_theorem(&env, name).unwrap();
        }
        let count = env.num_constants();
        assert!(install_success_framing_into(&mut env).is_err());
        assert_eq!(count, env.num_constants());
    }
    #[test]
    fn success_frame_observation_retains_changed_error_frame_state_and_payload() {
        let env = environment();
        let sf = z("Prod", 2, [n(), n()]);
        let ef = sf.clone();
        let status = z("Except", 2, [n(), n()]);
        let observed = z("Prod", 2, [sf.clone(), status.clone()]);
        let mut sc = Scope::default();
        let frame = sc.local(n());
        let input = sc.local(n());
        for error_case in [true, false] {
            let raw_status = if error_case {
                z(
                    "Except.error",
                    2,
                    [
                        ef.clone(),
                        n(),
                        pair0(
                            n(),
                            z("Nat.succ", 0, [frame.term.clone()]),
                            Expr::nat_lit(7),
                        ),
                    ],
                )
            } else {
                z("Except.ok", 2, [ef.clone(), n(), Expr::nat_lit(9)])
            };
            let raw = lams(
                &[frame.clone(), input.clone()],
                pair0(
                    z("Except", 2, [ef.clone(), n()]),
                    Expr::nat_lit(8),
                    raw_status,
                ),
            );
            let initial = pair0(n(), Expr::nat_lit(3), Expr::nat_lit(11));
            let actual = z(
                SUCCESS_FRAME_RUN,
                1,
                [n(), n(), n(), n(), raw.clone(), initial.clone()],
            );
            let expected_status = z(
                if error_case {
                    "Except.error"
                } else {
                    "Except.ok"
                },
                2,
                [n(), n(), Expr::nat_lit(if error_case { 7 } else { 9 })],
            );
            let expected = z(
                "Prod.mk",
                2,
                [
                    sf.clone(),
                    status.clone(),
                    pair0(
                        n(),
                        Expr::nat_lit(8),
                        Expr::nat_lit(if error_case { 12 } else { 11 }),
                    ),
                    expected_status.clone(),
                ],
            );
            let eq = |right| proof_at("Eq", [observed.clone(), actual.clone(), right]);
            let proof = proof_at("Eq.refl", [observed.clone(), actual.clone()]);
            let wire = trust_ir::proof::encode_clean_expr_v1(&proof).unwrap();
            let proof = trust_ir::proof::decode_clean_expr_v1(&wire).unwrap();
            let checker = TypeChecker::new(&env);
            checker.check_type(&proof, &eq(expected)).unwrap();
            assert!(
                env.audit_certification(&eq(actual.clone()), &proof)
                    .is_certified()
            );
            for (base, fr, tag, payload) in [
                (
                    3,
                    if error_case { 12 } else { 11 },
                    error_case,
                    if error_case { 7 } else { 9 },
                ),
                (8, 5, error_case, if error_case { 7 } else { 9 }),
                (8, if error_case { 12 } else { 11 }, error_case, 99),
                (
                    8,
                    if error_case { 12 } else { 11 },
                    !error_case,
                    if error_case { 7 } else { 9 },
                ),
            ] {
                let wrong = z(
                    "Prod.mk",
                    2,
                    [
                        sf.clone(),
                        status.clone(),
                        pair0(n(), Expr::nat_lit(base), Expr::nat_lit(fr)),
                        z(
                            if tag { "Except.error" } else { "Except.ok" },
                            2,
                            [n(), n(), Expr::nat_lit(payload)],
                        ),
                    ],
                );
                let goal = eq(wrong);
                assert!(checker.infer_type(&goal).is_ok());
                assert!(checker.check_type(&proof, &goal).is_err());
            }
            let conditional = z(
                SUCCESS_FRAME_PROJECTION,
                1,
                [n(), n(), n(), n(), Expr::nat_lit(11), actual.clone()],
            );
            let law = z(
                SUCCESS_FRAME_PRESERVES,
                1,
                [n(), n(), n(), n(), raw, initial],
            );
            let goal = proof_at("Eq", [n(), conditional, Expr::nat_lit(11)]);
            checker.check_type(&law, &goal).unwrap();
            if error_case {
                let post = z("Prod.fst", 2, [sf.clone(), status.clone(), actual]);
                let error_frame = z("Prod.snd", 2, [n(), n(), post]);
                let false_goal = proof_at("Eq", [n(), error_frame, Expr::nat_lit(11)]);
                assert!(checker.infer_type(&false_goal).is_ok());
                assert!(
                    checker.check_type(&law, &false_goal).is_err(),
                    "success-only projection cannot assert unchanged failure frame"
                );
            }
        }
    }
    #[test]
    fn success_frame_bind_keeps_failure_state_and_skips_failed_continuations() {
        let env = environment();
        let sf = z("Prod", 2, [n(), n()]);
        let status = z("Except", 2, [n(), n()]);
        let observed = z("Prod", 2, [sf.clone(), status.clone()]);
        let fe = sf.clone();
        let raw_status = z("Except", 2, [fe.clone(), n()]);
        for first_error in [true, false] {
            let mut sc = Scope::default();
            let frame = sc.local(n());
            let base = sc.local(n());
            let value = sc.local(n());
            let next_frame = sc.local(n());
            let next_base = sc.local(n());
            let raw_error = |post, error_frame, error| {
                pair0(
                    raw_status.clone(),
                    Expr::nat_lit(post),
                    z(
                        "Except.error",
                        2,
                        [
                            fe.clone(),
                            n(),
                            pair0(n(), Expr::nat_lit(error_frame), Expr::nat_lit(error)),
                        ],
                    ),
                )
            };
            let first = if first_error {
                raw_error(5, 23, 7)
            } else {
                pair0(
                    raw_status.clone(),
                    Expr::nat_lit(6),
                    z("Except.ok", 2, [fe.clone(), n(), Expr::nat_lit(2)]),
                )
            };
            let m = frame.lam(base.lam(first));
            let k = value.lam(next_frame.lam(next_base.lam(raw_error(99, 29, 13))));
            let state = pair0(n(), Expr::nat_lit(3), Expr::nat_lit(11));
            let proof = z(
                SUCCESS_FRAME_BIND,
                1,
                [n(), n(), n(), n(), n(), m, k, state],
            );
            let expected = z(
                "Prod.mk",
                2,
                [
                    sf.clone(),
                    status.clone(),
                    pair0(
                        n(),
                        Expr::nat_lit(if first_error { 5 } else { 99 }),
                        Expr::nat_lit(if first_error { 23 } else { 29 }),
                    ),
                    z(
                        "Except.error",
                        2,
                        [n(), n(), Expr::nat_lit(if first_error { 7 } else { 13 })],
                    ),
                ],
            );
            let goal = proof_at("Eq", [observed.clone(), expected.clone(), expected.clone()]);
            let wire = trust_ir::proof::encode_clean_expr_v1(&proof).unwrap();
            let proof = trust_ir::proof::decode_clean_expr_v1(&wire).unwrap();
            TypeChecker::new(&env).check_type(&proof, &goal).unwrap();
            assert!(env.audit_certification(&goal, &proof).is_certified());
            let forged = z(
                "Prod.mk",
                2,
                [
                    sf.clone(),
                    status.clone(),
                    pair0(n(), Expr::nat_lit(99), Expr::nat_lit(11)),
                    z("Except.error", 2, [n(), n(), Expr::nat_lit(7)]),
                ],
            );
            let false_goal = proof_at("Eq", [observed.clone(), expected, forged]);
            assert!(
                TypeChecker::new(&env)
                    .check_type(&proof, &false_goal)
                    .is_err(),
                "bind must not execute a failed continuation or restore an arbitrary failure frame"
            );
        }
    }
    #[test]
    fn success_frame_last_owned_collision_refuses_before_any_extension() {
        let mut env = build_environment().unwrap();
        env.init_nat().unwrap();
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(SUCCESS_FRAME_ERROR),
            level_params: vec![],
            type_: proof_at("Eq", [n(), Expr::nat_lit(1), Expr::nat_lit(1)]),
            value: proof_at("Eq.refl", [n(), Expr::nat_lit(1)]),
        })
        .unwrap();
        let count = env.num_constants();
        assert!(install_success_framing_into(&mut env).is_err());
        assert_eq!(count, env.num_constants());
        assert!(
            env.get_const(&Name::from_string(SUCCESS_FRAME_OBSERVATION))
                .is_none()
        );
    }
    #[test]
    fn success_frame_cps_observer_retains_the_actual_run_and_requires_a_real_image() {
        let env = environment();
        let sf = z("Prod", 2, [n(), n()]);
        let outcome = z("Except", 2, [n(), n()]);
        for error_case in [false, true] {
            let mut sc = Scope::default();
            let ignored = sc.local(sf.clone());
            let post = pair0(n(), Expr::nat_lit(8), Expr::nat_lit(9));
            let observed = z(
                "Prod.mk",
                2,
                [
                    sf.clone(),
                    outcome.clone(),
                    post,
                    z(
                        if error_case {
                            "Except.error"
                        } else {
                            "Except.ok"
                        },
                        2,
                        [n(), n(), Expr::nat_lit(7)],
                    ),
                ],
            );
            let run = ignored.lam(observed);
            let state = pair0(n(), Expr::nat_lit(1), Expr::nat_lit(2));
            let next = sc.local(sf.clone());
            let value = sc.local(n());
            let failure = sc.local(n());
            let ok = lams(
                &[next.clone(), value],
                z("Prod.snd", 2, [n(), n(), next.term.clone()]),
            );
            let err = lams(&[next, failure], Expr::nat_lit(2));
            let actual = z(
                TO_CPS,
                1,
                [
                    sf.clone(),
                    n(),
                    n(),
                    n(),
                    run.clone(),
                    state.clone(),
                    ok,
                    err,
                ],
            );
            let proof = z(
                SUCCESS_FRAME_CPS_OBSERVER,
                1,
                [n(), n(), n(), n(), run.clone(), state.clone()],
            );
            let expected = Expr::nat_lit(if error_case { 2 } else { 9 });
            let goal = proof_at("Eq", [n(), actual.clone(), expected]);
            let wire = trust_ir::proof::encode_clean_expr_v1(&proof).unwrap();
            let decoded = trust_ir::proof::decode_clean_expr_v1(&wire).unwrap();
            TypeChecker::new(&env).check_type(&decoded, &goal).unwrap();
            assert!(env.audit_certification(&goal, &decoded).is_certified());
            let forged = proof_at(
                "Eq",
                [n(), actual, Expr::nat_lit(if error_case { 9 } else { 2 })],
            );
            assert!(
                TypeChecker::new(&env)
                    .check_type(&decoded, &forged)
                    .is_err(),
                "observer neither restores success state nor asserts unchanged failure state"
            );
            let full = Expr::app(run, state);
            let actual_post = z("Prod.fst", 2, [sf.clone(), outcome.clone(), full]);
            let actual_frame = z("Prod.snd", 2, [n(), n(), actual_post]);
            let retained = proof_at("Eq", [n(), actual_frame, Expr::nat_lit(9)]);
            TypeChecker::new(&env)
                .check_type(&proof_at("Eq.refl", [n(), Expr::nat_lit(9)]), &retained)
                .unwrap();
        }
    }
    #[test]
    fn success_frame_base_projection_keeps_actual_success_and_failure_states() {
        let env = environment();
        let sf = z("Prod", 2, [n(), n()]);
        let outcome = z("Except", 2, [n(), n()]);
        for error_case in [false, true] {
            let raw_status = if error_case {
                z(
                    "Except.error",
                    2,
                    [
                        sf.clone(),
                        n(),
                        pair0(n(), Expr::nat_lit(9), Expr::nat_lit(7)),
                    ],
                )
            } else {
                z("Except.ok", 2, [sf.clone(), n(), Expr::nat_lit(7)])
            };
            let raw = pair0(
                z("Except", 2, [sf.clone(), n()]),
                Expr::nat_lit(8),
                raw_status,
            );
            let full = z(
                SUCCESS_FRAME_OBSERVATION,
                1,
                [n(), n(), n(), n(), Expr::nat_lit(2), raw.clone()],
            );
            let post = z("Prod.fst", 2, [sf.clone(), outcome.clone(), full]);
            let actual = z("Prod.fst", 2, [n(), n(), post]);
            let proof = z(
                SUCCESS_FRAME_BASE,
                1,
                [n(), n(), n(), n(), Expr::nat_lit(2), raw],
            );
            let goal = proof_at("Eq", [n(), actual.clone(), Expr::nat_lit(8)]);
            let bytes = trust_ir::proof::encode_clean_expr_v1(&proof).unwrap();
            let decoded = trust_ir::proof::decode_clean_expr_v1(&bytes).unwrap();
            TypeChecker::new(&env).check_type(&decoded, &goal).unwrap();
            assert!(env.audit_certification(&goal, &decoded).is_certified());
            let false_goal = proof_at("Eq", [n(), actual, Expr::nat_lit(1)]);
            assert!(
                TypeChecker::new(&env)
                    .check_type(&decoded, &false_goal)
                    .is_err(),
                "base projection cannot restore an arbitrary entry snapshot"
            );
        }
    }
}

fn bind_law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a, b] = sc.types();
    let sf = prod(&s.term, &f.term);
    let fe = prod(&f.term, &e.term);
    let obs = result(&s.term, &fe, &a.term);
    let target = result(&sf, &e.term, &b.term);
    let m = sc.local(Expr::arrow(f.term.clone(), run(&s.term, &fe, &a.term)));
    let k = sc.local(Expr::arrow(
        a.term.clone(),
        Expr::arrow(f.term.clone(), run(&s.term, &fe, &b.term)),
    ));
    let state = sc.local(sf.clone());
    let base_state = projection(0, &s.term, &f.term, state.term.clone());
    let frame = projection(1, &s.term, &f.term, state.term.clone());
    let value = sc.local(a.term.clone());
    let lifted_k = value.lam(framed(
        &s.term,
        &f.term,
        &e.term,
        &b.term,
        Expr::app(k.term.clone(), value.term.clone()),
    ));
    let raw_value = sc.local(a.term.clone());
    let raw_k = raw_value.lam(Expr::apps(
        k.term.clone(),
        [raw_value.term.clone(), frame.clone()],
    ));
    let ignored = sc.local(s.term.clone());
    let ignored_frame = sc.local(sf.clone());
    let equation = |observed: Expr| {
        let source = observe(
            &s.term,
            &f.term,
            &e.term,
            &b.term,
            frame.clone(),
            bind(
                &s.term,
                &fe,
                &a.term,
                &b.term,
                ignored.lam(observed.clone()),
                raw_k.clone(),
                base_state.clone(),
            ),
        );
        let lifted = ignored_frame.lam(observe(
            &s.term,
            &f.term,
            &e.term,
            &a.term,
            frame.clone(),
            observed,
        ));
        let destination = bind(
            &sf,
            &e.term,
            &a.term,
            &b.term,
            lifted,
            lifted_k.clone(),
            state.term.clone(),
        );
        (source, destination)
    };
    let major = sc.local(obs.clone());
    let motive = major.lam({
        let (l, r) = equation(major.term.clone());
        eq(&target, l, r)
    });
    let next = sc.local(s.term.clone());
    let status = sc.local(outcome(&fe, &a.term));
    let inner_motive = status.lam({
        let (l, r) = equation(pair(
            &s.term,
            &outcome(&fe, &a.term),
            next.term.clone(),
            status.term.clone(),
        ));
        eq(&target, l, r)
    });
    let error_value = sc.local(fe.clone());
    let ok_value = sc.local(a.term.clone());
    let branch = |ok: bool, value: Expr| {
        let status_value = apps(
            if ok { "Except.ok" } else { "Except.error" },
            [fe.clone(), a.term.clone(), value],
        );
        let (left, _) = equation(pair(
            &s.term,
            &outcome(&fe, &a.term),
            next.term.clone(),
            status_value,
        ));
        refl(&target, left)
    };
    let inner = outcome_cases(
        &fe,
        &a.term,
        inner_motive,
        error_value.lam(branch(false, error_value.term.clone())),
        ok_value.lam(branch(true, ok_value.term.clone())),
        status.term.clone(),
        true,
    );
    let proof = result_cases(
        &s.term,
        &fe,
        &a.term,
        motive,
        lams(&[next, status], inner),
        Expr::apps(m.term.clone(), [frame.clone(), base_state.clone()]),
        true,
    );
    let left = observe(
        &s.term,
        &f.term,
        &e.term,
        &b.term,
        frame.clone(),
        bind(
            &s.term,
            &fe,
            &a.term,
            &b.term,
            Expr::app(m.term.clone(), frame),
            raw_k,
            base_state,
        ),
    );
    let right = bind(
        &sf,
        &e.term,
        &a.term,
        &b.term,
        framed(&s.term, &f.term, &e.term, &a.term, m.term.clone()),
        lifted_k,
        state.term.clone(),
    );
    add(
        env,
        SUCCESS_FRAME_BIND,
        &[s, f, e, a, b, m, k, state],
        eq(&target, left, right),
        proof,
        true,
    )
}

// A conditional observer of an explicit Run, not an invariant of arbitrary CPS.
// Failed Runs retain their actual state; only the observer returns the initial
// frame on error. Any source use still needs its actual checked CPS image.
fn cps_observer_law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a] = sc.types();
    let sf = prod(&s.term, &f.term);
    let m = sc.local(run(&sf, &e.term, &a.term));
    let state = sc.local(sf.clone());
    let initial = projection(1, &s.term, &f.term, state.term.clone());
    let ignored = sc.local(sf.clone());
    let ok_state = sc.local(sf.clone());
    let value = sc.local(a.term.clone());
    let err_state = sc.local(sf.clone());
    let failure = sc.local(e.term.clone());
    let ok = lams(
        &[ok_state.clone(), value],
        projection(1, &s.term, &f.term, ok_state.term),
    );
    let err = lams(&[err_state, failure], initial.clone());
    let equation = |observed: Expr| {
        let left = apps(
            TO_CPS,
            [
                sf.clone(),
                e.term.clone(),
                a.term.clone(),
                f.term.clone(),
                ignored.lam(observed.clone()),
                state.term.clone(),
                ok.clone(),
                err.clone(),
            ],
        );
        let right = project(
            &s.term,
            &f.term,
            &e.term,
            &a.term,
            initial.clone(),
            observed,
        );
        (left, right)
    };
    let observed = sc.local(result(&sf, &e.term, &a.term));
    let post = sc.local(sf.clone());
    let status = sc.local(outcome(&e.term, &a.term));
    let failure = sc.local(e.term.clone());
    let value = sc.local(a.term.clone());
    let at = |status: Expr| pair(&sf, &outcome(&e.term, &a.term), post.term.clone(), status);
    let motive = status.lam({
        let (l, r) = equation(at(status.term.clone()));
        eq(&f.term, l, r)
    });
    let branch = |tag, payload: Expr| {
        let (left, _) = equation(at(apps(tag, [e.term.clone(), a.term.clone(), payload])));
        refl(&f.term, left)
    };
    let inner = outcome_cases(
        &e.term,
        &a.term,
        motive,
        failure.lam(branch("Except.error", failure.term.clone())),
        value.lam(branch("Except.ok", value.term.clone())),
        status.term.clone(),
        true,
    );
    let outer_motive = observed.lam({
        let (l, r) = equation(observed.term.clone());
        eq(&f.term, l, r)
    });
    let actual = Expr::app(m.term.clone(), state.term.clone());
    let proof = result_cases(
        &sf,
        &e.term,
        &a.term,
        outer_motive,
        lams(&[post, status], inner),
        actual.clone(),
        true,
    );
    let left = apps(
        TO_CPS,
        [
            sf,
            e.term.clone(),
            a.term.clone(),
            f.term.clone(),
            m.term.clone(),
            state.term.clone(),
            ok,
            err,
        ],
    );
    let right = project(&s.term, &f.term, &e.term, &a.term, initial, actual);
    add(
        env,
        SUCCESS_FRAME_CPS_OBSERVER,
        &[s, f.clone(), e, a, m, state],
        eq(&f.term, left, right),
        proof,
        true,
    )
}

// The conditional frame adapter preserves the actual raw Base projection on
// both outcomes. Any Base relation (such as protected custody) is a separate
// premise; this law cannot invent one or restore an entry-state snapshot.
fn base_projection_law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a] = sc.types();
    let sf = prod(&s.term, &f.term);
    let fe = prod(&f.term, &e.term);
    let frame = sc.local(f.term.clone());
    let raw = sc.local(result(&s.term, &fe, &a.term));
    let equation = |input: Expr| {
        let full = observe(
            &s.term,
            &f.term,
            &e.term,
            &a.term,
            frame.term.clone(),
            input.clone(),
        );
        let next = projection(0, &sf, &outcome(&e.term, &a.term), full);
        let left = projection(0, &s.term, &f.term, next);
        let right = projection(0, &s.term, &outcome(&fe, &a.term), input);
        (left, right)
    };
    let major = sc.local(raw.ty.clone());
    let post = sc.local(s.term.clone());
    let status = sc.local(outcome(&fe, &a.term));
    let at = |status: Expr| pair(&s.term, &outcome(&fe, &a.term), post.term.clone(), status);
    let motive = status.lam({
        let (l, r) = equation(at(status.term.clone()));
        eq(&s.term, l, r)
    });
    let failure = sc.local(fe.clone());
    let value = sc.local(a.term.clone());
    let branch = |tag, payload| {
        let (left, _) = equation(at(apps(tag, [fe.clone(), a.term.clone(), payload])));
        refl(&s.term, left)
    };
    let inner = outcome_cases(
        &fe,
        &a.term,
        motive,
        failure.lam(branch("Except.error", failure.term.clone())),
        value.lam(branch("Except.ok", value.term.clone())),
        status.term.clone(),
        true,
    );
    let outer = major.lam({
        let (l, r) = equation(major.term.clone());
        eq(&s.term, l, r)
    });
    let proof = result_cases(
        &s.term,
        &fe,
        &a.term,
        outer,
        lams(&[post, status], inner),
        raw.term.clone(),
        true,
    );
    let (left, right) = equation(raw.term.clone());
    add(
        env,
        SUCCESS_FRAME_BASE,
        &[s.clone(), f, e, a, frame, raw],
        eq(&s.term, left, right),
        proof,
        true,
    )
}

#[path = "semantic_evaluation_success_frame_composition.rs"]
mod composition;
