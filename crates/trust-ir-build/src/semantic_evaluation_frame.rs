// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Structural framing of a Run, including failure poststates and force-time
//! frames. This supplies no heap ownership or physical provider fidelity.
use super::*;
pub const FRAME_OBSERVATION: &str = "TrustIR.Eval.Frame.observation";
pub const FRAME_RUN: &str = "TrustIR.Eval.Frame.run";
pub const FRAME_EXPOSE: &str = "TrustIR.Eval.Frame.expose";
pub const FRAME_PRESERVES: &str = "TrustIR.Eval.Frame.preserves";
pub const FRAME_BIND: &str = "TrustIR.Eval.Frame.bind";
pub const FRAME_FORCE_CAPTURE: &str = "TrustIR.Eval.Frame.force_capture";
pub const FRAME_DECLARATIONS: [&str; 6] = [
    FRAME_OBSERVATION,
    FRAME_RUN,
    FRAME_EXPOSE,
    FRAME_PRESERVES,
    FRAME_BIND,
    FRAME_FORCE_CAPTURE,
];

pub fn install_framing_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in FRAME_DECLARATIONS {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    recheck_theorem(env, BIND_ASSOC)?;
    recheck_theorem(env, FORCE_CAPTURE)?;
    definitions(env)?;
    expose(env)?;
    preserves(env)?;
    bind_law(env)?;
    force_capture(env)?;
    for name in [
        FRAME_EXPOSE,
        FRAME_PRESERVES,
        FRAME_BIND,
        FRAME_FORCE_CAPTURE,
    ] {
        recheck_theorem(env, name)?;
    }
    Ok(())
}
fn observation(s: &Expr, f: &Expr, e: &Expr, a: &Expr, frame: Expr, value: Expr) -> Expr {
    apps(
        FRAME_OBSERVATION,
        [s.clone(), f.clone(), e.clone(), a.clone(), frame, value],
    )
}
fn framed(s: &Expr, f: &Expr, e: &Expr, a: &Expr, value: Expr) -> Expr {
    apps(
        FRAME_RUN,
        [s.clone(), f.clone(), e.clone(), a.clone(), value],
    )
}
fn definitions(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a] = sc.types();
    let frame = sc.local(f.term.clone());
    let observed = sc.local(result(&s.term, &e.term, &a.term));
    let body = pair(
        &prod(&s.term, &f.term),
        &outcome(&e.term, &a.term),
        pair(
            &s.term,
            &f.term,
            projection(
                0,
                &s.term,
                &outcome(&e.term, &a.term),
                observed.term.clone(),
            ),
            frame.term.clone(),
        ),
        projection(
            1,
            &s.term,
            &outcome(&e.term, &a.term),
            observed.term.clone(),
        ),
    );
    add(
        env,
        FRAME_OBSERVATION,
        &[s.clone(), f.clone(), e.clone(), a.clone(), frame, observed],
        result(&prod(&s.term, &f.term), &e.term, &a.term),
        body,
        false,
    )?;
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let state = sc.local(prod(&s.term, &f.term));
    let body = observation(
        &s.term,
        &f.term,
        &e.term,
        &a.term,
        projection(1, &s.term, &f.term, state.term.clone()),
        Expr::app(
            m.term.clone(),
            projection(0, &s.term, &f.term, state.term.clone()),
        ),
    );
    add(
        env,
        FRAME_RUN,
        &[s.clone(), f.clone(), e.clone(), a.clone(), m, state],
        result(&prod(&s.term, &f.term), &e.term, &a.term),
        body,
        false,
    )
}
fn expose(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let state = sc.local(prod(&s.term, &f.term));
    let left = Expr::app(
        framed(&s.term, &f.term, &e.term, &a.term, m.term.clone()),
        state.term.clone(),
    );
    let right = observation(
        &s.term,
        &f.term,
        &e.term,
        &a.term,
        projection(1, &s.term, &f.term, state.term.clone()),
        Expr::app(
            m.term.clone(),
            projection(0, &s.term, &f.term, state.term.clone()),
        ),
    );
    let ty = result(&prod(&s.term, &f.term), &e.term, &a.term);
    add(
        env,
        FRAME_EXPOSE,
        &[s, f, e, a, m, state],
        eq(&ty, left.clone(), right),
        refl(&ty, left),
        true,
    )
}
fn preserves(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let state = sc.local(prod(&s.term, &f.term));
    let observed = Expr::app(
        framed(&s.term, &f.term, &e.term, &a.term, m.term.clone()),
        state.term.clone(),
    );
    let post = projection(
        0,
        &prod(&s.term, &f.term),
        &outcome(&e.term, &a.term),
        observed,
    );
    let left = projection(1, &s.term, &f.term, post);
    let right = projection(1, &s.term, &f.term, state.term.clone());
    add(
        env,
        FRAME_PRESERVES,
        &[s, f.clone(), e, a, m, state],
        eq(&f.term, left, right.clone()),
        refl(&f.term, right),
        true,
    )
}
fn bind_law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a, b] = sc.types();
    let sf = prod(&s.term, &f.term);
    let obs = result(&s.term, &e.term, &a.term);
    let target = result(&sf, &e.term, &b.term);
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let k = sc.local(Expr::arrow(a.term.clone(), run(&s.term, &e.term, &b.term)));
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
    let ignored = sc.local(s.term.clone());
    let ignored_frame = sc.local(sf.clone());
    let equation = |observed: Expr| {
        let source = observation(
            &s.term,
            &f.term,
            &e.term,
            &b.term,
            frame.clone(),
            bind(
                &s.term,
                &e.term,
                &a.term,
                &b.term,
                ignored.lam(observed.clone()),
                k.term.clone(),
                base_state.clone(),
            ),
        );
        let lifted = ignored_frame.lam(observation(
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
    let status = sc.local(outcome(&e.term, &a.term));
    let inner_motive = status.lam({
        let (l, r) = equation(pair(
            &s.term,
            &outcome(&e.term, &a.term),
            next.term.clone(),
            status.term.clone(),
        ));
        eq(&target, l, r)
    });
    let error_value = sc.local(e.term.clone());
    let ok_value = sc.local(a.term.clone());
    let branch = |ok: bool, value: Expr| {
        let status_value = apps(
            if ok { "Except.ok" } else { "Except.error" },
            [e.term.clone(), a.term.clone(), value],
        );
        let (left, _) = equation(pair(
            &s.term,
            &outcome(&e.term, &a.term),
            next.term.clone(),
            status_value,
        ));
        refl(&target, left)
    };
    let inner = outcome_cases(
        &e.term,
        &a.term,
        inner_motive,
        error_value.lam(branch(false, error_value.term.clone())),
        ok_value.lam(branch(true, ok_value.term.clone())),
        status.term.clone(),
        true,
    );
    let proof = result_cases(
        &s.term,
        &e.term,
        &a.term,
        motive,
        lams(&[next, status], inner),
        Expr::app(m.term.clone(), base_state),
        true,
    );
    let left = Expr::app(
        framed(
            &s.term,
            &f.term,
            &e.term,
            &b.term,
            apps(
                BIND,
                [
                    s.term.clone(),
                    e.term.clone(),
                    a.term.clone(),
                    b.term.clone(),
                    m.term.clone(),
                    k.term.clone(),
                ],
            ),
        ),
        state.term.clone(),
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
        FRAME_BIND,
        &[s, f, e, a, b, m, k, state],
        eq(&target, left, right),
        proof,
        true,
    )
}
fn force_capture(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a, ctx, lex] = sc.types();
    let code = sc.local(Expr::arrow(
        lex.term.clone(),
        Expr::arrow(ctx.term.clone(), run(&s.term, &e.term, &a.term)),
    ));
    let captured = sc.local(lex.term.clone());
    let context = sc.local(ctx.term.clone());
    let state = sc.local(prod(&s.term, &f.term));
    let l = sc.local(lex.term.clone());
    let c = sc.local(ctx.term.clone());
    let framed_code = lams(
        &[l.clone(), c.clone()],
        framed(
            &s.term,
            &f.term,
            &e.term,
            &a.term,
            Expr::apps(code.term.clone(), [l.term, c.term]),
        ),
    );
    let sf = prod(&s.term, &f.term);
    let thunk = apps(
        CAPTURE,
        [
            sf.clone(),
            e.term.clone(),
            a.term.clone(),
            ctx.term.clone(),
            lex.term.clone(),
            framed_code,
            captured.term.clone(),
        ],
    );
    let left = apps(
        FORCE,
        [
            sf.clone(),
            e.term.clone(),
            a.term.clone(),
            ctx.term.clone(),
            lex.term.clone(),
            thunk,
            context.term.clone(),
            state.term.clone(),
        ],
    );
    let right = Expr::app(
        framed(
            &s.term,
            &f.term,
            &e.term,
            &a.term,
            Expr::apps(
                code.term.clone(),
                [captured.term.clone(), context.term.clone()],
            ),
        ),
        state.term.clone(),
    );
    let ty = result(&sf, &e.term, &a.term);
    add(
        env,
        FRAME_FORCE_CAPTURE,
        &[s, f, e, a, ctx, lex, code, captured, context, state],
        eq(&ty, left.clone(), right),
        refl(&ty, left),
        true,
    )
}

/// Only an explicit checked image at the observation answer carrier permits
/// this direction. There is no converse for an arbitrary CPS computation.
pub const CPS_IMAGE_FROM: &str = "TrustIR.Eval.image_from_cps";
pub fn install_image_observation_into(
    env: &mut Environment,
) -> Result<(), SemanticEvaluationError> {
    if env.get_const(&Name::from_string(CPS_IMAGE_FROM)).is_some() {
        return Err(error(CPS_IMAGE_FROM, "owned declaration already exists"));
    }
    if env.get_const(&Name::from_string(CPS_IMAGE)).is_none() {
        return Err(error(CPS_IMAGE_FROM, "explicit image vocabulary is absent"));
    }
    recheck_theorem(env, FROM_TO_CPS)?;
    let mut sc = Scope::default();
    let [s, e, a] = sc.types();
    let obs = result(&s.term, &e.term, &a.term);
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let source = sc.local(apps(
        CPS,
        [s.term.clone(), e.term.clone(), a.term.clone(), obs.clone()],
    ));
    let image = sc.local(apps(
        CPS_IMAGE,
        [
            s.term.clone(),
            e.term.clone(),
            a.term.clone(),
            obs.clone(),
            m.term.clone(),
            source.term.clone(),
        ],
    ));
    let state = sc.local(s.term.clone());
    let next = sc.local(s.term.clone());
    let value = sc.local(a.term.clone());
    let failure = sc.local(e.term.clone());
    let ok = lams(
        &[next.clone(), value.clone()],
        pair(
            &s.term,
            &outcome(&e.term, &a.term),
            next.term.clone(),
            apps(
                "Except.ok",
                [e.term.clone(), a.term.clone(), value.term.clone()],
            ),
        ),
    );
    let err = lams(
        &[next.clone(), failure.clone()],
        pair(
            &s.term,
            &outcome(&e.term, &a.term),
            next.term.clone(),
            apps(
                "Except.error",
                [e.term.clone(), a.term.clone(), failure.term.clone()],
            ),
        ),
    );
    let left = apps(
        FROM_CPS,
        [
            s.term.clone(),
            e.term.clone(),
            a.term.clone(),
            source.term.clone(),
            state.term.clone(),
        ],
    );
    let middle = apps(
        TO_CPS,
        [
            s.term.clone(),
            e.term.clone(),
            a.term.clone(),
            obs.clone(),
            m.term.clone(),
            state.term.clone(),
            ok.clone(),
            err.clone(),
        ],
    );
    let right = Expr::app(m.term.clone(), state.term.clone());
    let h = Expr::apps(image.term.clone(), [state.term.clone(), ok, err]);
    let inverse = apps(
        FROM_TO_CPS,
        [
            s.term.clone(),
            e.term.clone(),
            a.term.clone(),
            m.term.clone(),
            state.term.clone(),
        ],
    );
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![Level::succ(u())]),
        [obs.clone(), left.clone(), middle, right.clone(), h, inverse],
    );
    add(
        env,
        CPS_IMAGE_FROM,
        &[s, e, a, m, source, image, state],
        eq(&obs, left, right),
        proof,
        true,
    )?;
    recheck_theorem(env, CPS_IMAGE_FROM)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn at0(name: &str, count: usize, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string(name), vec![Level::zero(); count]),
            args,
        )
    }
    fn nat() -> Expr {
        Expr::const_str("Nat")
    }
    fn pair0(a: Expr, b: Expr, x: Expr, y: Expr) -> Expr {
        at0("Prod.mk", 2, [a, b, x, y])
    }
    fn eq0(ty: Expr, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [ty, l, r],
        )
    }
    fn refl0(ty: Expr, x: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [ty, x],
        )
    }
    #[test]
    fn framed_run_laws_are_complete_kernel_checked_and_rooted_audited() {
        let mut env = build_environment().unwrap();
        install_framing_into(&mut env).unwrap();
        for name in [
            FRAME_EXPOSE,
            FRAME_PRESERVES,
            FRAME_BIND,
            FRAME_FORCE_CAPTURE,
        ] {
            recheck_theorem(&env, name).unwrap();
            let declaration = env.get_const(&Name::from_string(name)).unwrap();
            let value = declaration.value.as_ref().unwrap();
            let bytes = trust_ir::proof::encode_clean_expr_v1(value).unwrap();
            let decoded = trust_ir::proof::decode_clean_expr_v1(&bytes).unwrap();
            TypeChecker::new(&env)
                .check_type(&decoded, &declaration.type_)
                .unwrap();
            assert!(
                env.audit_certification(&declaration.type_, &decoded)
                    .is_certified()
            );
        }
        let count = env.num_constants();
        assert!(install_framing_into(&mut env).is_err());
        assert_eq!(count, env.num_constants());
    }
    #[test]
    fn framed_run_capture_keeps_force_time_frame_error_and_actual_poststate() {
        let mut env = build_environment().unwrap();
        env.init_nat().unwrap();
        install_framing_into(&mut env).unwrap();
        let mut sc = Scope::default();
        let lex = sc.local(nat());
        let ctx = sc.local(nat());
        let state = sc.local(nat());
        let out = at0("Except", 2, [nat(), nat()]);
        let error = at0("Except.error", 2, [nat(), nat(), ctx.term.clone()]);
        let code = lams(
            &[lex.clone(), ctx.clone(), state],
            pair0(nat(), out.clone(), lex.term, error),
        );
        let l = sc.local(nat());
        let c = sc.local(nat());
        let sf = at0("Prod", 2, [nat(), nat()]);
        let lifted_code = lams(
            &[l.clone(), c.clone()],
            at0(
                FRAME_RUN,
                1,
                [
                    nat(),
                    nat(),
                    nat(),
                    nat(),
                    Expr::apps(code, [l.term, c.term]),
                ],
            ),
        );
        let thunk = at0(
            CAPTURE,
            1,
            [
                sf.clone(),
                nat(),
                nat(),
                nat(),
                nat(),
                lifted_code,
                Expr::nat_lit(5),
            ],
        );
        let forced = at0(
            FORCE,
            1,
            [
                sf.clone(),
                nat(),
                nat(),
                nat(),
                nat(),
                thunk,
                Expr::nat_lit(4),
                pair0(nat(), nat(), Expr::nat_lit(3), Expr::nat_lit(11)),
            ],
        );
        let expected = |s: u64, f: u64, e: u64, ok: bool| {
            pair0(
                sf.clone(),
                out.clone(),
                pair0(nat(), nat(), Expr::nat_lit(s), Expr::nat_lit(f)),
                at0(
                    if ok { "Except.ok" } else { "Except.error" },
                    2,
                    [nat(), nat(), Expr::nat_lit(e)],
                ),
            )
        };
        let observation = at0("Prod", 2, [sf.clone(), out.clone()]);
        let value = expected(5, 11, 4, false);
        let goal = eq0(observation.clone(), forced.clone(), value.clone());
        let proof = refl0(observation.clone(), value);
        let checker = TypeChecker::new(&env);
        checker.check_type(&proof, &goal).unwrap();
        assert!(env.audit_certification(&goal, &proof).is_certified());
        for (s, f, e, ok) in [
            (3, 11, 4, false),
            (5, 5, 4, false),
            (5, 11, 99, false),
            (5, 11, 4, true),
        ] {
            let wrong = eq0(observation.clone(), forced.clone(), expected(s, f, e, ok));
            assert!(checker.infer_type(&wrong).is_ok());
            assert!(
                checker.check_type(&proof, &wrong).is_err(),
                "frame projection must preserve actual poststate/current frame/full error"
            );
        }
    }
    #[test]
    fn framed_run_observation_bridge_requires_the_actual_checked_image() {
        let mut env = build_environment().unwrap();
        let before = env.num_constants();
        assert!(install_image_observation_into(&mut env).is_err());
        assert_eq!(before, env.num_constants());
        install_handle_into(&mut env).unwrap();
        env.init_nat().unwrap();
        install_image_observation_into(&mut env).unwrap();
        let mut sc = Scope::default();
        let state = sc.local(nat());
        let outcome = at0("Except", 2, [nat(), nat()]);
        let obs = at0("Prod", 2, [nat(), outcome.clone()]);
        let result = |n| {
            pair0(
                nat(),
                outcome.clone(),
                Expr::nat_lit(n),
                at0("Except.error", 2, [nat(), nat(), Expr::nat_lit(4)]),
            )
        };
        let m = state.lam(result(9));
        let source = at0(TO_CPS, 1, [nat(), nat(), nat(), obs.clone(), m.clone()]);
        let s = sc.local(nat());
        let callback = Expr::arrow(nat(), Expr::arrow(nat(), obs.clone()));
        let ok = sc.local(callback.clone());
        let err = sc.local(callback);
        let h = lams(
            &[s.clone(), ok.clone(), err.clone()],
            refl0(
                obs.clone(),
                Expr::apps(source.clone(), [s.term, ok.term, err.term]),
            ),
        );
        let proof = at0(
            CPS_IMAGE_FROM,
            1,
            [
                nat(),
                nat(),
                nat(),
                m,
                source.clone(),
                h.clone(),
                Expr::nat_lit(3),
            ],
        );
        let observed = at0(
            FROM_CPS,
            1,
            [nat(), nat(), nat(), source.clone(), Expr::nat_lit(3)],
        );
        let goal = eq0(obs.clone(), observed.clone(), result(9));
        let bytes = trust_ir::proof::encode_clean_expr_v1(&proof).unwrap();
        let proof = trust_ir::proof::decode_clean_expr_v1(&bytes).unwrap();
        let checker = TypeChecker::new(&env);
        checker.check_type(&proof, &goal).unwrap();
        assert!(env.audit_certification(&goal, &proof).is_certified());
        let wrong_m = state.lam(result(8));
        let wrong = at0(
            CPS_IMAGE_FROM,
            1,
            [nat(), nat(), nat(), wrong_m, source, h, Expr::nat_lit(3)],
        );
        let wrong_goal = eq0(obs, observed, result(8));
        assert!(checker.infer_type(&wrong_goal).is_ok());
        assert!(
            checker.check_type(&wrong, &wrong_goal).is_err(),
            "image evidence for a different Run must not authorize a CPS converse"
        );
        drop(checker);
        let count = env.num_constants();
        assert!(install_image_observation_into(&mut env).is_err());
        assert_eq!(count, env.num_constants());
    }
    #[test]
    fn framed_run_last_owned_name_collision_refuses_before_mutation() {
        let mut env = build_environment().unwrap();
        let ty = eq0(
            Expr::const_str("Bool"),
            Expr::const_str("Bool.false"),
            Expr::const_str("Bool.false"),
        );
        let value = refl0(Expr::const_str("Bool"), Expr::const_str("Bool.false"));
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(FRAME_FORCE_CAPTURE),
            level_params: vec![],
            type_: ty,
            value,
        })
        .unwrap();
        let before = env.num_constants();
        assert!(install_framing_into(&mut env).is_err());
        assert_eq!(before, env.num_constants());
        assert!(env.get_const(&Name::from_string(FRAME_RUN)).is_none());
    }
}
