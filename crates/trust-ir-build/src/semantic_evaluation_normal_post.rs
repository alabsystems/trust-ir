// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Turn a checked success-conditional observation into an actual normal post.
//! The observation carrier is arbitrary. Errors keep their complete raw result;
//! this rule imposes no error postcondition or whole-state frame invariant.
use super::*;

pub const NORMAL_POST: &str = "TrustIR.Eval.NormalResult.post";
pub const NORMAL_OBSERVATION: &str = "TrustIR.Eval.NormalResult.observation";
pub const NORMAL_OBSERVATION_POST: &str = "TrustIR.Eval.NormalResult.observation_post";
const OWNED: [&str; 3] = [NORMAL_POST, NORMAL_OBSERVATION, NORMAL_OBSERVATION_POST];

/// Install these optional, value-polymorphic definitions and checked theorem:
///
/// ```text
/// post S E A p (state, error e) = True
/// post S E A p (state, ok a)    = p state a
/// observation S E A M measure expected (state, error e) = expected
/// observation S E A M measure expected (state, ok a)    = measure state
/// observation_post S E A M measure expected raw
///   (h : observation S E A M measure expected raw = expected) :
///   post S E A (fun state value => measure state = expected) raw
/// ```
/// All arguments are explicit; S, E, A and M inhabit Type u. The equality
/// premise is mandatory and refers to this exact raw result. A name collision
/// rejects before mutation; discard the environment on a later failure. This
/// library supplies no primitive behavior, termination or compiler admission.
pub fn install_normal_post_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in OWNED {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    env.init_eq().map_err(|e| error(NORMAL_POST, e))?;
    env.init_prod().map_err(|e| error(NORMAL_POST, e))?;
    env.init_except_t().map_err(|e| error(NORMAL_POST, e))?;
    env.init_true_false().map_err(|e| error(NORMAL_POST, e))?;
    definitions(env)?;
    law(env)?;
    recheck_theorem(env, NORMAL_OBSERVATION_POST)?;
    let name = Name::from_string(NORMAL_OBSERVATION_POST);
    if !env.axiom_deps(&name).is_some_and(|deps| deps.is_empty())
        || !env
            .foundational_axiom_deps(&name)
            .is_some_and(|deps| deps.is_empty())
        || !env
            .trust_marker_deps(&name)
            .is_some_and(|deps| deps.is_empty())
    {
        return Err(error(
            NORMAL_OBSERVATION_POST,
            "missing or nonempty authority closure",
        ));
    }
    Ok(())
}

fn post(s: &Expr, e: &Expr, a: &Expr, predicate: Expr, raw: Expr) -> Expr {
    apps(
        NORMAL_POST,
        [s.clone(), e.clone(), a.clone(), predicate, raw],
    )
}
fn observation(
    s: &Expr,
    e: &Expr,
    a: &Expr,
    m: &Expr,
    measure: Expr,
    expected: Expr,
    raw: Expr,
) -> Expr {
    apps(
        NORMAL_OBSERVATION,
        [
            s.clone(),
            e.clone(),
            a.clone(),
            m.clone(),
            measure,
            expected,
            raw,
        ],
    )
}
fn definitions(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, m] = sc.types();
    let state = sc.local(s.term.clone());
    let value = sc.local(a.term.clone());
    let predicate = sc.local(pis(
        &[state.clone(), value.clone()],
        Expr::sort(Level::zero()),
    ));
    let raw = sc.local(result(&s.term, &e.term, &a.term));
    let status = sc.local(outcome(&e.term, &a.term));
    let major = sc.local(raw.ty.clone());
    let failure = sc.local(e.term.clone());
    // A proposition is a value of Sort 0, so these eliminators return Sort 0
    // at level 1, independently of the universe of the raw state and payload.
    let inner = Expr::apps(
        Expr::const_(
            Name::from_string("Except.rec"),
            vec![Level::succ(Level::zero()), u(), u()],
        ),
        [
            e.term.clone(),
            a.term.clone(),
            status.lam(Expr::sort(Level::zero())),
            failure.lam(Expr::const_str("True")),
            value.lam(Expr::apps(
                predicate.term.clone(),
                [state.term.clone(), value.term.clone()],
            )),
            status.term.clone(),
        ],
    );
    let body = Expr::apps(
        Expr::const_(
            Name::from_string("Prod.rec"),
            vec![Level::succ(Level::zero()), u(), u()],
        ),
        [
            s.term.clone(),
            outcome(&e.term, &a.term),
            major.lam(Expr::sort(Level::zero())),
            lams(&[state.clone(), status.clone()], inner),
            raw.term.clone(),
        ],
    );
    add(
        env,
        NORMAL_POST,
        &[s.clone(), e.clone(), a.clone(), predicate, raw.clone()],
        Expr::sort(Level::zero()),
        body,
        false,
    )?;

    let measure = sc.local(Expr::arrow(s.term.clone(), m.term.clone()));
    let expected = sc.local(m.term.clone());
    let body = outcome_cases(
        &e.term,
        &a.term,
        status.lam(m.term.clone()),
        failure.lam(expected.term.clone()),
        value.lam(Expr::app(
            measure.term.clone(),
            projection(0, &s.term, &outcome(&e.term, &a.term), raw.term.clone()),
        )),
        projection(1, &s.term, &outcome(&e.term, &a.term), raw.term.clone()),
        false,
    );
    add(
        env,
        NORMAL_OBSERVATION,
        &[s, e, a, m.clone(), measure, expected, raw],
        m.term,
        body,
        false,
    )
}
fn law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, m] = sc.types();
    let measure = sc.local(Expr::arrow(s.term.clone(), m.term.clone()));
    let expected = sc.local(m.term.clone());
    let raw = sc.local(result(&s.term, &e.term, &a.term));
    let state = sc.local(s.term.clone());
    let value = sc.local(a.term.clone());
    let predicate = lams(
        &[state.clone(), value.clone()],
        eq(
            &m.term,
            Expr::app(measure.term.clone(), state.term.clone()),
            expected.term.clone(),
        ),
    );
    let equality = |raw: Expr| {
        eq(
            &m.term,
            observation(
                &s.term,
                &e.term,
                &a.term,
                &m.term,
                measure.term.clone(),
                expected.term.clone(),
                raw,
            ),
            expected.term.clone(),
        )
    };
    let implication = |raw: Expr| {
        Expr::arrow(
            equality(raw.clone()),
            post(&s.term, &e.term, &a.term, predicate.clone(), raw),
        )
    };
    let premise = sc.local(equality(raw.term.clone()));
    let major = sc.local(raw.ty.clone());
    let status = sc.local(outcome(&e.term, &a.term));
    let pair = |status| {
        pair(
            &s.term,
            &outcome(&e.term, &a.term),
            state.term.clone(),
            status,
        )
    };
    let failure = sc.local(e.term.clone());
    let failure_h = sc.local(equality(pair(apps(
        "Except.error",
        [e.term.clone(), a.term.clone(), failure.term.clone()],
    ))));
    let normal_h = sc.local(equality(pair(apps(
        "Except.ok",
        [e.term.clone(), a.term.clone(), value.term.clone()],
    ))));
    let inside = outcome_cases(
        &e.term,
        &a.term,
        status.lam(implication(pair(status.term.clone()))),
        lams(&[failure, failure_h], Expr::const_str("True.intro")),
        lams(&[value, normal_h.clone()], normal_h.term),
        status.term.clone(),
        true,
    );
    let all = result_cases(
        &s.term,
        &e.term,
        &a.term,
        major.lam(implication(major.term.clone())),
        lams(&[state, status], inside),
        raw.term.clone(),
        true,
    );
    add(
        env,
        NORMAL_OBSERVATION_POST,
        &[
            s.clone(),
            e.clone(),
            a.clone(),
            m,
            measure,
            expected,
            raw.clone(),
            premise.clone(),
        ],
        post(&s.term, &e.term, &a.term, predicate, raw.term),
        Expr::app(all, premise.term),
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    fn at(name: &str, count: usize, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string(name), vec![Level::zero(); count]),
            args,
        )
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
    fn environment() -> Environment {
        let mut env = Environment::default();
        env.set_option("maxHeartbeats".into(), Some(HEARTBEAT_LIMIT.to_string()));
        env.set_option(
            "tcMaxCacheEntries".into(),
            Some(CACHE_ENTRY_LIMIT.to_string()),
        );
        install_normal_post_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env.init_bool().unwrap();
        env.init_option().unwrap();
        env
    }
    fn check(env: &Environment, proof: &Expr, goal: &Expr) -> Result<(), String> {
        let mut tc = TypeChecker::with_mode(env, env.mode());
        tc.set_heartbeat_limit(HEARTBEAT_LIMIT);
        tc.set_max_cache_entries(CACHE_ENTRY_LIMIT);
        tc.check_type(proof, goal).map_err(|e| format!("{e:?}"))
    }
    fn reject(env: &Environment, proof: &Expr, goal: &Expr) {
        let reason = check(env, proof, goal).expect_err("changed or missing premise must refuse");
        assert!(
            reason.contains("TypeMismatch") && !reason.contains("BudgetExhausted"),
            "{reason}"
        );
    }
    fn n() -> Expr {
        Expr::const_str("Nat")
    }
    fn boolean(b: bool) -> Expr {
        Expr::const_str(if b { "Bool.true" } else { "Bool.false" })
    }
    fn state_type() -> Expr {
        at("Prod", 2, [n(), bool_ty()])
    }
    fn state(counter: u64, flag: bool) -> Expr {
        at(
            "Prod.mk",
            2,
            [n(), bool_ty(), Expr::nat_lit(counter), boolean(flag)],
        )
    }
    fn observation_type() -> Expr {
        at("Option", 1, [n()])
    }
    fn some(counter: u64) -> Expr {
        at("Option.some", 1, [n(), Expr::nat_lit(counter)])
    }
    fn measure() -> Expr {
        Expr::lam(
            BinderInfo::Default,
            state_type(),
            at(
                "Option.some",
                1,
                [n(), at("Prod.fst", 2, [n(), bool_ty(), Expr::bvar(0)])],
            ),
        )
    }
    fn raw(counter: u64, flag: bool, failure: Option<(u64, bool)>) -> Expr {
        let status = match failure {
            Some((code, detail)) => at(
                "Except.error",
                2,
                [state_type(), bool_ty(), state(code, detail)],
            ),
            None => at("Except.ok", 2, [state_type(), bool_ty(), boolean(false)]),
        };
        at(
            "Prod.mk",
            2,
            [
                state_type(),
                at("Except", 2, [state_type(), bool_ty()]),
                state(counter, flag),
                status,
            ],
        )
    }
    fn observer(expected: Expr, raw: Expr) -> Expr {
        at(
            NORMAL_OBSERVATION,
            1,
            [
                state_type(),
                state_type(),
                bool_ty(),
                observation_type(),
                measure(),
                expected,
                raw,
            ],
        )
    }
    fn premise(expected: Expr) -> Expr {
        reflexive(observation_type(), expected)
    }
    fn rule(expected: Expr, raw: Expr, h: Expr) -> Expr {
        at(
            NORMAL_OBSERVATION_POST,
            1,
            [
                state_type(),
                state_type(),
                bool_ty(),
                observation_type(),
                measure(),
                expected,
                raw,
                h,
            ],
        )
    }
    fn goal(expected: Expr, raw: Expr) -> Expr {
        let predicate = Expr::lam(
            BinderInfo::Default,
            state_type(),
            Expr::lam(
                BinderInfo::Default,
                bool_ty(),
                equality(
                    observation_type(),
                    Expr::app(measure(), Expr::bvar(1)),
                    expected,
                ),
            ),
        );
        at(
            NORMAL_POST,
            1,
            [state_type(), state_type(), bool_ty(), predicate, raw],
        )
    }
    #[test]
    fn optional_rule_is_checked_without_axioms_and_collision_is_nonmutating() {
        let mut env = environment();
        recheck_theorem(&env, NORMAL_OBSERVATION_POST).unwrap();
        let count = env.num_constants();
        assert!(install_normal_post_into(&mut env).is_err());
        assert_eq!(count, env.num_constants());
        assert!(
            build_environment()
                .unwrap()
                .get_const(&Name::from_string(NORMAL_POST))
                .is_none()
        );
    }
    #[test]
    fn every_owned_name_collision_rejects_before_prerequisites_or_options_change() {
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
            let before = (env.num_constants(), env.generation());
            let refused = install_normal_post_into(&mut env).unwrap_err();
            assert_eq!(refused.declaration, name);
            assert_eq!(before, (env.num_constants(), env.generation()));
            assert_eq!(env.get_option("maxHeartbeats"), Some(&Some("1".into())));
        }
    }
    #[test]
    fn observation_carrier_can_itself_contain_types_in_a_higher_universe() {
        let env = environment();
        let one = Level::succ(Level::zero());
        let carrier = Expr::sort(one.clone());
        let call = |name: &str, levels: Vec<Level>, args: Vec<Expr>| {
            Expr::apps(Expr::const_(Name::from_string(name), levels), args)
        };
        let status = call(
            "Except",
            vec![one.clone(); 2],
            vec![carrier.clone(), carrier.clone()],
        );
        let result = call(
            "Prod.mk",
            vec![one.clone(); 2],
            vec![
                carrier.clone(),
                status,
                n(),
                call(
                    "Except.ok",
                    vec![one.clone(); 2],
                    vec![carrier.clone(), carrier.clone(), bool_ty()],
                ),
            ],
        );
        let identity = Expr::lam(BinderInfo::Default, carrier.clone(), Expr::bvar(0));
        let h = call(
            "Eq.refl",
            vec![Level::succ(one.clone())],
            vec![carrier.clone(), n()],
        );
        let proof = call(
            NORMAL_OBSERVATION_POST,
            vec![one.clone()],
            vec![
                carrier.clone(),
                carrier.clone(),
                carrier.clone(),
                carrier.clone(),
                identity,
                n(),
                result.clone(),
                h,
            ],
        );
        let predicate = Expr::lam(
            BinderInfo::Default,
            carrier.clone(),
            Expr::lam(
                BinderInfo::Default,
                carrier.clone(),
                call(
                    "Eq",
                    vec![Level::succ(one.clone())],
                    vec![carrier.clone(), Expr::bvar(1), n()],
                ),
            ),
        );
        let goal = call(
            NORMAL_POST,
            vec![one],
            vec![carrier.clone(), carrier.clone(), carrier, predicate, result],
        );
        check(&env, &proof, &goal).unwrap();
    }
    #[test]
    fn non_nat_observation_establishes_actual_changed_poststate_without_whole_state_equality() {
        let env = environment();
        let result = raw(7, true, None);
        let expected = some(7);
        let h = premise(expected.clone());
        check(
            &env,
            &h,
            &equality(
                observation_type(),
                observer(expected.clone(), result.clone()),
                expected.clone(),
            ),
        )
        .unwrap();
        let proof = rule(expected.clone(), result.clone(), h.clone());
        check(&env, &proof, &goal(expected.clone(), result.clone())).unwrap();
        // A former state, changed counter, wrong expected observation, and an
        // omitted equality premise cannot replace the actual returned state.
        reject(&env, &proof, &goal(some(3), result.clone()));
        reject(
            &env,
            &rule(expected.clone(), raw(8, true, None), h),
            &goal(expected.clone(), raw(8, true, None)),
        );
        let partial = at(
            NORMAL_OBSERVATION_POST,
            1,
            [
                state_type(),
                state_type(),
                bool_ty(),
                observation_type(),
                measure(),
                expected.clone(),
                result.clone(),
            ],
        );
        reject(&env, &partial, &goal(expected, result));
        reject(
            &env,
            &proof,
            &equality(state_type(), state(7, true), state(3, false)),
        );
        // The observer deliberately forgets the flag; this never licenses a
        // stronger equality of complete states with the same measured counter.
        reject(
            &env,
            &proof,
            &equality(state_type(), state(7, true), state(7, false)),
        );
    }
    #[test]
    fn error_observation_keeps_actual_raw_state_and_error_payload_unconstrained() {
        let env = environment();
        for failure in [(91, false), (93, true)] {
            let result = raw(11, true, Some(failure));
            let expected = some(7);
            let h = premise(expected.clone());
            check(
                &env,
                &h,
                &equality(
                    observation_type(),
                    observer(expected.clone(), result.clone()),
                    expected.clone(),
                ),
            )
            .unwrap();
            check(
                &env,
                &rule(expected.clone(), result.clone(), h),
                &goal(expected, result),
            )
            .unwrap();
        }
        // Switching the same changed state to normal return must re-establish
        // the observation; a fallback equality from an error is insufficient.
        reject(
            &env,
            &rule(some(7), raw(11, true, None), premise(some(7))),
            &goal(some(7), raw(11, true, None)),
        );
    }
}
