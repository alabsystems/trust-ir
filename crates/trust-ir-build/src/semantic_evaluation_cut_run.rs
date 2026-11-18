// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Decode a checked first-order cut computation. None denotes the actual
//! backedge continuation; Some/error retains the complete return observation.
//! An arbitrary fixed-answer CPS return does not establish this image premise.
use super::*;
pub const RUN_TO_PULSE: &str = "TrustIR.Eval.Loop.run_to_pulse";
pub const RUN_TO_PULSE_CPS: &str = "TrustIR.Eval.Loop.run_to_pulse_cps";
pub const IMAGE_TO_PULSE: &str = "TrustIR.Eval.Loop.image_to_pulse";
pub const IMAGE_TO_PULSE_OBSERVATION: &str = "TrustIR.Eval.Loop.image_to_pulse_observation";
fn option_type(a: &Expr) -> Expr {
    Expr::app(c("Option"), a.clone())
}
fn pulse_type(s: &Expr, e: &Expr, a: &Expr) -> Expr {
    sum(s, &result(s, e, a))
}
fn tag_cases(a: &Expr, motive: Expr, none: Expr, some: Expr, tag: Expr) -> Expr {
    tag_cases_at(a, motive, none, some, tag, Level::succ(u()))
}
fn tag_cases_at(
    a: &Expr,
    motive: Expr,
    none: Expr,
    some: Expr,
    tag: Expr,
    result_level: Level,
) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Option.rec"), vec![result_level, u()]),
        [a.clone(), motive, none, some, tag],
    )
}
fn channels(sc: &mut Scope, s: &Expr, e: &Expr, a: &Expr) -> (Expr, Expr) {
    let pulse = pulse_type(s, e, a);
    let done = result(s, e, a);
    let next = sc.local(s.clone());
    let tag = sc.local(option_type(a));
    let value = sc.local(a.clone());
    let failure = sc.local(e.clone());
    let success = lams(
        &[next.clone(), tag.clone()],
        tag_cases(
            a,
            tag.lam(pulse),
            side(s, &done, false, next.term.clone()),
            value.lam(side(
                s,
                &done,
                true,
                pair(
                    s,
                    &outcome(e, a),
                    next.term.clone(),
                    apps("Except.ok", [e.clone(), a.clone(), value.term.clone()]),
                ),
            )),
            tag.term.clone(),
        ),
    );
    let error = lams(
        &[next.clone(), failure.clone()],
        side(
            s,
            &done,
            true,
            pair(
                s,
                &outcome(e, a),
                next.term.clone(),
                apps("Except.error", [e.clone(), a.clone(), failure.term.clone()]),
            ),
        ),
    );
    (success, error)
}
fn decode(s: &Expr, e: &Expr, a: &Expr, observation: Expr) -> Expr {
    apps(RUN_TO_PULSE, [s.clone(), e.clone(), a.clone(), observation])
}
pub fn install_cut_run_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in [RUN_TO_PULSE, RUN_TO_PULSE_CPS, IMAGE_TO_PULSE] {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    recheck_theorem(env, super::super::CPS_IMAGE_HANDLE)?;
    env.init_option().map_err(|e| error(RUN_TO_PULSE, e))?;
    env.init_sum().map_err(|e| error(RUN_TO_PULSE, e))?;
    definition(env)?;
    bridge(env)?;
    transfer(env)?;
    recheck_theorem(env, RUN_TO_PULSE_CPS)?;
    recheck_theorem(env, IMAGE_TO_PULSE)
}
fn definition(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a] = sc.types();
    let opt = option_type(&a.term);
    let pulse = pulse_type(&s.term, &e.term, &a.term);
    let done = result(&s.term, &e.term, &a.term);
    let observed = sc.local(result(&s.term, &e.term, &opt));
    let next = sc.local(s.term.clone());
    let o = sc.local(outcome(&e.term, &opt));
    let tag = sc.local(opt.clone());
    let value = sc.local(a.term.clone());
    let failure = sc.local(e.term.clone());
    let matched = outcome_cases(
        &e.term,
        &opt,
        o.lam(pulse.clone()),
        failure.lam(side(
            &s.term,
            &done,
            true,
            pair(
                &s.term,
                &outcome(&e.term, &a.term),
                next.term.clone(),
                apps(
                    "Except.error",
                    [e.term.clone(), a.term.clone(), failure.term.clone()],
                ),
            ),
        )),
        tag.lam(tag_cases(
            &a.term,
            tag.lam(pulse.clone()),
            side(&s.term, &done, false, next.term.clone()),
            value.lam(side(
                &s.term,
                &done,
                true,
                pair(
                    &s.term,
                    &outcome(&e.term, &a.term),
                    next.term.clone(),
                    apps(
                        "Except.ok",
                        [e.term.clone(), a.term.clone(), value.term.clone()],
                    ),
                ),
            )),
            tag.term.clone(),
        )),
        o.term.clone(),
        false,
    );
    let value = result_cases(
        &s.term,
        &e.term,
        &opt,
        observed.lam(pulse.clone()),
        lams(&[next, o], matched),
        observed.term.clone(),
        false,
    );
    add(env, RUN_TO_PULSE, &[s, e, a, observed], pulse, value, false)
}
fn bridge(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a] = sc.types();
    let opt = option_type(&a.term);
    let pulse = pulse_type(&s.term, &e.term, &a.term);
    let m = sc.local(run(&s.term, &e.term, &opt));
    let state = sc.local(s.term.clone());
    let (ok, err) = channels(&mut sc, &s.term, &e.term, &a.term);
    let left = to_cps(
        &s.term,
        &e.term,
        &opt,
        &pulse,
        m.term.clone(),
        state.term.clone(),
        ok,
        err,
    );
    let right = decode(
        &s.term,
        &e.term,
        &a.term,
        Expr::app(m.term.clone(), state.term.clone()),
    );
    let proof = refl(&pulse, right.clone());
    add(
        env,
        RUN_TO_PULSE_CPS,
        &[s, e, a, m, state],
        eq(&pulse, left, right),
        proof,
        true,
    )
}
fn transfer(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a] = sc.types();
    let opt = option_type(&a.term);
    let pulse = pulse_type(&s.term, &e.term, &a.term);
    let m = sc.local(run(&s.term, &e.term, &opt));
    let f = sc.local(cps(&s.term, &e.term, &opt, &pulse));
    let image = sc.local(apps(
        super::super::CPS_IMAGE,
        [
            s.term.clone(),
            e.term.clone(),
            opt.clone(),
            pulse.clone(),
            m.term.clone(),
            f.term.clone(),
        ],
    ));
    let state = sc.local(s.term.clone());
    let (ok, err) = channels(&mut sc, &s.term, &e.term, &a.term);
    let left = Expr::apps(
        f.term.clone(),
        [state.term.clone(), ok.clone(), err.clone()],
    );
    let middle = to_cps(
        &s.term,
        &e.term,
        &opt,
        &pulse,
        m.term.clone(),
        state.term.clone(),
        ok.clone(),
        err.clone(),
    );
    let right = decode(
        &s.term,
        &e.term,
        &a.term,
        Expr::app(m.term.clone(), state.term.clone()),
    );
    let first = Expr::apps(image.term.clone(), [state.term.clone(), ok, err]);
    let second = apps(
        RUN_TO_PULSE_CPS,
        [
            s.term.clone(),
            e.term.clone(),
            a.term.clone(),
            m.term.clone(),
            state.term.clone(),
        ],
    );
    let proof = trans(&pulse, left.clone(), middle, right.clone(), first, second);
    add(
        env,
        IMAGE_TO_PULSE,
        &[s, e, a, m, f, image, state],
        eq(&pulse, left, right),
        proof,
        true,
    )
}

/// Observe an exact checked cut image through an arbitrary terminal context at
/// its original answer type. All arguments are explicit, in this order:
/// `S E V A run code image finish residual state`. With
/// `D = Prod S (Except E V)`, `finish : D -> A` and `residual : S -> A`, the
/// result is the pointwise observation law consumed by CPS loop transport:
///
/// ```text
/// code state
///   (fun post tag => Option.cases (residual post)
///      (fun value => finish (post, Except.ok value)) tag)
///   (fun post error => finish (post, Except.error error))
/// = Sum.rec (fun _ => A) residual finish (run_to_pulse (run state))
/// ```
/// Install after `install_cut_run_into`. The exact image function, run, state,
/// parameters and answer type remain unchanged. This is a forward image law;
/// it supplies no image premise, termination witness or CPS converse.
/// Collisions refuse before mutation; discard the environment on a later error.
pub fn install_cut_observation_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    if env
        .get_const(&Name::from_string(IMAGE_TO_PULSE_OBSERVATION))
        .is_some()
    {
        return Err(error(
            IMAGE_TO_PULSE_OBSERVATION,
            "owned declaration already exists",
        ));
    }
    recheck_theorem(env, IMAGE_TO_PULSE)?;
    observation(env)?;
    recheck_theorem(env, IMAGE_TO_PULSE_OBSERVATION)?;
    let name = Name::from_string(IMAGE_TO_PULSE_OBSERVATION);
    if !env.axiom_deps(&name).is_some_and(|deps| deps.is_empty())
        || !env
            .foundational_axiom_deps(&name)
            .is_some_and(|deps| deps.is_empty())
        || !env
            .trust_marker_deps(&name)
            .is_some_and(|deps| deps.is_empty())
    {
        return Err(error(
            IMAGE_TO_PULSE_OBSERVATION,
            "missing or nonempty axiom or trust-marker closure",
        ));
    }
    Ok(())
}

fn observation_channels(
    sc: &mut Scope,
    s: &Expr,
    e: &Expr,
    v: &Expr,
    answer: &Expr,
    residual: Expr,
    finish: Expr,
) -> (Expr, Expr) {
    let post = sc.local(s.clone());
    let tag = sc.local(option_type(v));
    let value = sc.local(v.clone());
    let failure = sc.local(e.clone());
    let terminal = |constructor, payload| {
        Expr::app(
            finish.clone(),
            pair(
                s,
                &outcome(e, v),
                post.term.clone(),
                apps(constructor, [e.clone(), v.clone(), payload]),
            ),
        )
    };
    let yes = lams(
        &[post.clone(), tag.clone()],
        tag_cases(
            v,
            tag.lam(answer.clone()),
            Expr::app(residual, post.term.clone()),
            value.lam(terminal("Except.ok", value.term.clone())),
            tag.term.clone(),
        ),
    );
    let no = lams(
        &[post.clone(), failure.clone()],
        terminal("Except.error", failure.term.clone()),
    );
    (yes, no)
}

fn observation(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, v, a] = sc.types();
    let opt = option_type(&v.term);
    let done = result(&s.term, &e.term, &v.term);
    let pulse = pulse_type(&s.term, &e.term, &v.term);
    let m = sc.local(run(&s.term, &e.term, &opt));
    let f = sc.local(cps(&s.term, &e.term, &opt, &a.term));
    let image = sc.local(apps(
        super::super::CPS_IMAGE,
        [
            s.term.clone(),
            e.term.clone(),
            opt.clone(),
            a.term.clone(),
            m.term.clone(),
            f.term.clone(),
        ],
    ));
    let finish = sc.local(Expr::arrow(done.clone(), a.term.clone()));
    let residual = sc.local(Expr::arrow(s.term.clone(), a.term.clone()));
    let state = sc.local(s.term.clone());
    let (yes, no) = observation_channels(
        &mut sc,
        &s.term,
        &e.term,
        &v.term,
        &a.term,
        residual.term.clone(),
        finish.term.clone(),
    );
    let selected = sc.local(pulse.clone());
    let ignored = sc.local(pulse);
    let mapper = selected.lam(cases(
        &s.term,
        &done,
        ignored.lam(a.term.clone()),
        residual.term.clone(),
        finish.term.clone(),
        selected.term.clone(),
        false,
    ));
    let mapped = |raw| Expr::app(mapper.clone(), decode(&s.term, &e.term, &v.term, raw));
    let converted = |computation| {
        to_cps(
            &s.term,
            &e.term,
            &opt,
            &a.term,
            computation,
            state.term.clone(),
            yes.clone(),
            no.clone(),
        )
    };
    let unused = sc.local(s.term.clone());
    let equation = |raw: Expr| eq(&a.term, converted(unused.lam(raw.clone())), mapped(raw));
    let post = sc.local(s.term.clone());
    let failure = sc.local(e.term.clone());
    let tag = sc.local(opt.clone());
    let value = sc.local(v.term.clone());
    let packed = |constructor, payload| {
        pair(
            &s.term,
            &outcome(&e.term, &opt),
            post.term.clone(),
            apps(constructor, [e.term.clone(), opt.clone(), payload]),
        )
    };
    let finished = |constructor, payload| {
        Expr::app(
            finish.term.clone(),
            pair(
                &s.term,
                &outcome(&e.term, &v.term),
                post.term.clone(),
                apps(constructor, [e.term.clone(), v.term.clone(), payload]),
            ),
        )
    };
    // Prebuild these generalized branches before the existing Fn-based result
    // eliminator borrows the scope. Option equality eliminates only into Prop;
    // the original data decoder still uses the unchanged Type-u recursor.
    let failed = lams(
        &[post.clone(), failure.clone()],
        refl(&a.term, finished("Except.error", failure.term.clone())),
    );
    let normal = lams(
        &[post.clone(), tag.clone()],
        tag_cases_at(
            &v.term,
            tag.lam(equation(packed("Except.ok", tag.term.clone()))),
            refl(&a.term, Expr::app(residual.term.clone(), post.term.clone())),
            value.lam(refl(&a.term, finished("Except.ok", value.term.clone()))),
            tag.term.clone(),
            Level::zero(),
        ),
    );
    let evaluated = Expr::app(m.term.clone(), state.term.clone());
    let through = prove_result_cases(
        &mut sc,
        &s.term,
        &e.term,
        &opt,
        evaluated.clone(),
        equation,
        |post, failure| Expr::apps(failed.clone(), [post, failure]),
        |post, tag| Expr::apps(normal.clone(), [post, tag]),
    );
    let left = Expr::apps(
        f.term.clone(),
        [state.term.clone(), yes.clone(), no.clone()],
    );
    let middle = converted(m.term.clone());
    let right = mapped(evaluated);
    let first = Expr::apps(image.term.clone(), [state.term.clone(), yes, no]);
    let proof = trans(&a.term, left.clone(), middle, right.clone(), first, through);
    let goal = eq(&a.term, left, right);
    add(
        env,
        IMAGE_TO_PULSE_OBSERVATION,
        &[s, e, v, a, m, f, image, finish, residual, state],
        goal,
        proof,
        true,
    )
}

#[cfg(test)]
#[path = "semantic_evaluation_cut_observation_tests.rs"]
mod observation_tests;

#[cfg(test)]
mod tests {
    use super::*;
    fn z(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(
            c(name).instantiate_level_params(&[(Name::from_string("u"), Level::zero())]),
            args,
        )
    }
    fn two(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string(name), vec![Level::zero(), Level::zero()]),
            args,
        )
    }
    fn check(env: &Environment, ty: Expr, left: Expr, right: Expr) -> bool {
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [ty.clone(), left, right.clone()],
        );
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [ty, right],
        );
        let tc = TypeChecker::new(env);
        let _checked_goal_type = tc.infer_type(&goal).unwrap();
        let _checked_proof_type = tc.infer_type(&proof).unwrap();
        tc.check_type(&proof, &goal).is_ok()
    }
    #[test]
    fn cps_cut_run_image_bridge_is_kernel_checked_with_explicit_image_premise() {
        let mut env = build_environment().unwrap();
        super::super::super::install_handle_into(&mut env).unwrap();
        install_loop_into(&mut env).unwrap();
        install_cut_run_into(&mut env).unwrap();
        recheck_theorem(&env, RUN_TO_PULSE_CPS).unwrap();
        recheck_theorem(&env, IMAGE_TO_PULSE).unwrap();
        assert!(install_cut_run_into(&mut env).is_err());
    }
    #[test]
    fn cps_cut_run_tags_keep_actual_continue_success_error_and_poststate_distinct() {
        let mut env = build_environment().unwrap();
        super::super::super::install_handle_into(&mut env).unwrap();
        install_loop_into(&mut env).unwrap();
        install_cut_run_into(&mut env).unwrap();
        let nat = Expr::const_str("Nat");
        let boolean = Expr::const_str("Bool");
        let opt = z("Option", [boolean.clone()]);
        let outcome = z("Except", [boolean.clone(), boolean.clone()]);
        let done = two("Prod", [nat.clone(), outcome.clone()]);
        let pulse = two("Sum", [nat.clone(), done.clone()]);
        let pair = |s: Expr, o| two("Prod.mk", [nat.clone(), outcome.clone(), s, o]);
        let input = |s, tag| {
            two(
                "Prod.mk",
                [
                    nat.clone(),
                    z("Except", [boolean.clone(), opt.clone()]),
                    Expr::nat_lit(s),
                    tag,
                ],
            )
        };
        let continuation = input(
            1,
            z(
                "Except.ok",
                [
                    boolean.clone(),
                    opt.clone(),
                    z("Option.none", [boolean.clone()]),
                ],
            ),
        );
        let actual = z(
            RUN_TO_PULSE,
            [nat.clone(), boolean.clone(), boolean.clone(), continuation],
        );
        let expected = two("Sum.inl", [nat.clone(), done.clone(), Expr::nat_lit(1)]);
        assert!(check(&env, pulse.clone(), actual.clone(), expected));
        let success = z(
            "Except.ok",
            [
                boolean.clone(),
                boolean.clone(),
                Expr::const_str("Bool.true"),
            ],
        );
        let completed = two(
            "Sum.inr",
            [
                nat.clone(),
                done.clone(),
                pair(Expr::nat_lit(1), success.clone()),
            ],
        );
        assert!(!check(&env, pulse.clone(), actual, completed));
        let supplied = input(
            2,
            z(
                "Except.ok",
                [
                    boolean.clone(),
                    opt.clone(),
                    z(
                        "Option.some",
                        [boolean.clone(), Expr::const_str("Bool.true")],
                    ),
                ],
            ),
        );
        let actual = z(
            RUN_TO_PULSE,
            [nat.clone(), boolean.clone(), boolean.clone(), supplied],
        );
        let expected = two(
            "Sum.inr",
            [nat.clone(), done.clone(), pair(Expr::nat_lit(2), success)],
        );
        assert!(check(&env, pulse.clone(), actual, expected));
        let failure = z(
            "Except.error",
            [
                boolean.clone(),
                boolean.clone(),
                Expr::const_str("Bool.false"),
            ],
        );
        let supplied = input(
            3,
            z(
                "Except.error",
                [boolean.clone(), opt.clone(), Expr::const_str("Bool.false")],
            ),
        );
        let actual = z(
            RUN_TO_PULSE,
            [nat.clone(), boolean.clone(), boolean, supplied],
        );
        let expected = two(
            "Sum.inr",
            [
                nat.clone(),
                done.clone(),
                pair(Expr::nat_lit(3), failure.clone()),
            ],
        );
        assert!(check(&env, pulse.clone(), actual.clone(), expected));
        let stale = two(
            "Sum.inr",
            [nat.clone(), done, pair(Expr::nat_lit(2), failure)],
        );
        assert!(!check(&env, pulse, actual, stale));
    }
}
