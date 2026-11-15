// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! A continuation rule for a GENUINE CPS image of a conditionally framed Run.
//! Every image, Run property, initial relation and callback premise is explicit.
use super::*;
pub const SUCCESS_FRAME_CPS_RULE: &str = "TrustIR.Eval.SuccessFrame.cps_rule";
fn project(s: &Expr, f: &Expr, e: &Expr, a: &Expr, target: Expr, value: Expr) -> Expr {
    apps(
        SUCCESS_FRAME_PROJECTION,
        [s.clone(), f.clone(), e.clone(), a.clone(), target, value],
    )
}
pub fn install_success_cps_rule_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    if env
        .get_const(&Name::from_string(SUCCESS_FRAME_CPS_RULE))
        .is_some()
    {
        return Err(error(
            SUCCESS_FRAME_CPS_RULE,
            "owned declaration already exists",
        ));
    }
    recheck_theorem(env, CPS_IMAGE_HANDLE)?;
    recheck_theorem(env, SUCCESS_FRAME_CPS_OBSERVER)?;
    law(env)?;
    recheck_theorem(env, SUCCESS_FRAME_CPS_RULE)
}
fn law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a] = sc.types();
    let sf = prod(&s.term, &f.term);
    let m = sc.local(run(&sf, &e.term, &a.term));
    let code = sc.local(cps(&sf, &e.term, &a.term, &f.term));
    let image = sc.local(apps(
        CPS_IMAGE,
        [
            sf.clone(),
            e.term.clone(),
            a.term.clone(),
            f.term.clone(),
            m.term.clone(),
            code.term.clone(),
        ],
    ));
    let probe = sc.local(sf.clone());
    let frame = |state: Expr| projection(1, &s.term, &f.term, state);
    let preserves = sc.local(probe.pi(eq(
        &f.term,
        project(
            &s.term,
            &f.term,
            &e.term,
            &a.term,
            frame(probe.term.clone()),
            Expr::app(m.term.clone(), probe.term.clone()),
        ),
        frame(probe.term.clone()),
    )));
    let yes = sc.local(continuation(&sf, &a.term, &f.term));
    let no = sc.local(continuation(&sf, &e.term, &f.term));
    let target = sc.local(f.term.clone());
    let state = sc.local(sf.clone());
    let initial = frame(state.term.clone());
    let pre = sc.local(eq(&f.term, initial.clone(), target.term.clone()));
    let post = sc.local(sf.clone());
    let value = sc.local(a.term.clone());
    let failure = sc.local(e.term.clone());
    let related = sc.local(eq(&f.term, frame(post.term.clone()), target.term.clone()));
    let hy = sc.local(post.pi(value.pi(related.pi(eq(
        &f.term,
        Expr::apps(yes.term.clone(), [post.term.clone(), value.term.clone()]),
        target.term.clone(),
    )))));
    let hn = sc.local(post.pi(failure.pi(eq(
        &f.term,
        Expr::apps(no.term.clone(), [post.term.clone(), failure.term.clone()]),
        target.term.clone(),
    ))));
    let raw = sc.local(result(&sf, &e.term, &a.term));
    let ignored = sc.local(sf.clone());
    let converted = |computation: Expr| {
        apps(
            TO_CPS,
            [
                sf.clone(),
                e.term.clone(),
                a.term.clone(),
                f.term.clone(),
                computation,
                state.term.clone(),
                yes.term.clone(),
                no.term.clone(),
            ],
        )
    };
    let equation = |observed: Expr| {
        eq(
            &f.term,
            converted(ignored.lam(observed)),
            target.term.clone(),
        )
    };
    let premise = |observed: Expr| {
        eq(
            &f.term,
            project(
                &s.term,
                &f.term,
                &e.term,
                &a.term,
                initial.clone(),
                observed,
            ),
            initial.clone(),
        )
    };
    let motive = raw.lam(Expr::arrow(
        premise(raw.term.clone()),
        equation(raw.term.clone()),
    ));
    let status = sc.local(outcome(&e.term, &a.term));
    let packed = |status: Expr| pair(&sf, &outcome(&e.term, &a.term), post.term.clone(), status);
    let inner_motive = status.lam(Expr::arrow(
        premise(packed(status.term.clone())),
        equation(packed(status.term.clone())),
    ));
    let failed = packed(apps(
        "Except.error",
        [e.term.clone(), a.term.clone(), failure.term.clone()],
    ));
    let failure_h = sc.local(premise(failed));
    let error_proof = failure.lam(failure_h.lam(Expr::apps(
        hn.term.clone(),
        [post.term.clone(), failure.term.clone()],
    )));
    let normal = packed(apps(
        "Except.ok",
        [e.term.clone(), a.term.clone(), value.term.clone()],
    ));
    let normal_h = sc.local(premise(normal));
    let related_post = trans(
        &f.term,
        frame(post.term.clone()),
        initial.clone(),
        target.term.clone(),
        normal_h.term.clone(),
        pre.term.clone(),
    );
    let normal_proof = value.lam(normal_h.lam(Expr::apps(
        hy.term.clone(),
        [post.term.clone(), value.term.clone(), related_post],
    )));
    let inner = outcome_cases(
        &e.term,
        &a.term,
        inner_motive,
        error_proof,
        normal_proof,
        status.term.clone(),
        true,
    );
    let cases = result_cases(
        &sf,
        &e.term,
        &a.term,
        motive,
        lams(&[post, status], inner),
        Expr::app(m.term.clone(), state.term.clone()),
        true,
    );
    let through = Expr::app(cases, Expr::app(preserves.term.clone(), state.term.clone()));
    let actual = Expr::apps(
        code.term.clone(),
        [state.term.clone(), yes.term.clone(), no.term.clone()],
    );
    let middle = converted(m.term.clone());
    let first = Expr::apps(
        image.term.clone(),
        [state.term.clone(), yes.term.clone(), no.term.clone()],
    );
    let proof = trans(
        &f.term,
        actual.clone(),
        middle,
        target.term.clone(),
        first,
        through,
    );
    let goal = eq(&f.term, actual, target.term.clone());
    add(
        env,
        SUCCESS_FRAME_CPS_RULE,
        &[
            s, f, e, a, m, code, image, preserves, yes, no, target, state, pre, hy, hn,
        ],
        goal,
        proof,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    fn environment() -> Environment {
        let mut env = build_environment().unwrap();
        install_handle_into(&mut env).unwrap();
        install_success_framing_into(&mut env).unwrap();
        install_success_cps_rule_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env
    }
    #[test]
    fn success_frame_cps_rule_requires_original_dependencies_and_refuses_collision() {
        let mut missing = build_environment().unwrap();
        let n = missing.num_constants();
        assert!(install_success_cps_rule_into(&mut missing).is_err());
        assert_eq!(missing.num_constants(), n);
        let mut env = environment();
        let n = env.num_constants();
        assert!(install_success_cps_rule_into(&mut env).is_err());
        assert_eq!(env.num_constants(), n);
    }
    #[test]
    fn success_frame_cps_rule_checks_both_actual_outcomes_without_restoring_error_worlds() {
        check(false, 0);
        check(true, 0);
    }
    #[test]
    fn success_frame_cps_rule_refuses_ungrounded_image_callbacks_and_initial_relation() {
        for mode in 1..=4 {
            check(mode == 3, mode);
        }
    }
    fn check(failing: bool, bad: usize) {
        let env = environment();
        let nat = Expr::const_str("Nat");
        let sf = prod(&nat, &nat);
        let mut sc = Scope::default();
        let state = sc.local(sf.clone());
        let post = sc.local(sf.clone());
        let value = sc.local(nat.clone());
        let failure = sc.local(nat.clone());
        let image_ok = sc.local(continuation(&sf, &nat, &nat));
        let image_err = sc.local(continuation(&sf, &nat, &nat));
        let frame = |state: Expr| projection(1, &nat, &nat, state);
        let actual_post = pair(
            &nat,
            &nat,
            Expr::nat_lit(if failing { 4 } else { 3 }),
            if failing {
                Expr::nat_lit(13)
            } else {
                frame(state.term.clone())
            },
        );
        let m = state.lam(pair(
            &sf,
            &outcome(&nat, &nat),
            actual_post.clone(),
            apps(
                if failing { "Except.error" } else { "Except.ok" },
                [
                    nat.clone(),
                    nat.clone(),
                    Expr::nat_lit(if failing { 7 } else { 0 }),
                ],
            ),
        ));
        let converted = apps(
            TO_CPS,
            [sf.clone(), nat.clone(), nat.clone(), nat.clone(), m.clone()],
        );
        let code = if bad == 1 {
            lams(
                &[state.clone(), image_ok.clone(), image_err.clone()],
                Expr::nat_lit(9),
            )
        } else {
            converted.clone()
        };
        let image = lams(
            &[state.clone(), image_ok.clone(), image_err.clone()],
            refl(
                &nat,
                Expr::apps(
                    converted,
                    [
                        state.term.clone(),
                        image_ok.term.clone(),
                        image_err.term.clone(),
                    ],
                ),
            ),
        );
        let preserves = state.lam(refl(&nat, frame(state.term.clone())));
        let target = Expr::nat_lit(if bad == 4 { 9 } else { 2 });
        let yes = lams(
            &[post.clone(), value.clone()],
            if bad == 2 {
                Expr::nat_lit(9)
            } else {
                frame(post.term.clone())
            },
        );
        let no = lams(
            &[post.clone(), failure.clone()],
            if bad == 3 {
                frame(post.term.clone())
            } else {
                target.clone()
            },
        );
        let related = sc.local(eq(&nat, frame(post.term.clone()), target.clone()));
        let hy = lams(
            &[post.clone(), value, related.clone()],
            related.term.clone(),
        );
        let hn = lams(&[post, failure], refl(&nat, target.clone()));
        let input = pair(&nat, &nat, Expr::nat_lit(0), Expr::nat_lit(2));
        let pre = refl(&nat, Expr::nat_lit(2));
        let proof = apps(
            SUCCESS_FRAME_CPS_RULE,
            [
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                m.clone(),
                code.clone(),
                image,
                preserves,
                yes.clone(),
                no.clone(),
                target.clone(),
                input.clone(),
                pre,
                hy,
                hn,
            ],
        );
        let actual = Expr::apps(code, [input, yes, no]);
        let claim = eq(&nat, actual, target);
        let levels = [(Name::from_string("u"), Level::zero())];
        let proof = proof.instantiate_level_params(&levels);
        let claim = claim.instantiate_level_params(&levels);
        let checker = TypeChecker::new(&env);
        assert!(checker.infer_sort(&claim).unwrap().is_zero());
        let bytes = trust_ir::proof::encode_clean_expr_v1(&proof).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_v1(&bytes).unwrap();
        if bad != 0 {
            assert!(matches!(
                checker.check_type(&decoded, &claim),
                Err(clean_kernel::tc::TypeError::TypeMismatch { .. })
            ));
        } else {
            checker.check_type(&decoded, &claim).unwrap();
            assert!(env.audit_certification(&claim, &decoded).is_certified());
            if failing {
                let world = Expr::app(m, pair(&nat, &nat, Expr::nat_lit(0), Expr::nat_lit(2)));
                let expected = pair(
                    &sf,
                    &outcome(&nat, &nat),
                    actual_post,
                    apps("Except.error", [nat.clone(), nat.clone(), Expr::nat_lit(7)]),
                );
                let exact = eq(&result(&sf, &nat, &nat), world, expected.clone())
                    .instantiate_level_params(&levels);
                let witness =
                    refl(&result(&sf, &nat, &nat), expected).instantiate_level_params(&levels);
                checker.check_type(&witness, &exact).unwrap();
            }
        }
    }
}
