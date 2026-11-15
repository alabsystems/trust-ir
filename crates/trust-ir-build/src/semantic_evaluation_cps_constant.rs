// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Observe a genuine CPS image through two explicitly constant callbacks.
//! No invariant is required of either actual returned state or error payload.
use super::*;
pub const CPS_IMAGE_CONSTANT_OBSERVER: &str = "TrustIR.Eval.cps_image_constant_observer";

pub fn install_image_constant_observer_into(
    env: &mut Environment,
) -> Result<(), SemanticEvaluationError> {
    if env
        .get_const(&Name::from_string(CPS_IMAGE_CONSTANT_OBSERVER))
        .is_some()
    {
        return Err(error(
            CPS_IMAGE_CONSTANT_OBSERVER,
            "owned declaration already exists",
        ));
    }
    recheck_theorem(env, CPS_IMAGE_HANDLE)?;
    law(env)?;
    recheck_theorem(env, CPS_IMAGE_CONSTANT_OBSERVER)
}

fn law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, r] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let code = sc.local(cps(&s.term, &e.term, &a.term, &r.term));
    let image = sc.local(apps(
        CPS_IMAGE,
        [
            s.term.clone(),
            e.term.clone(),
            a.term.clone(),
            r.term.clone(),
            m.term.clone(),
            code.term.clone(),
        ],
    ));
    let yes = sc.local(continuation(&s.term, &a.term, &r.term));
    let no = sc.local(continuation(&s.term, &e.term, &r.term));
    let target = sc.local(r.term.clone());
    let input = sc.local(s.term.clone());
    let post = sc.local(s.term.clone());
    let value = sc.local(a.term.clone());
    let failure = sc.local(e.term.clone());
    let hy = sc.local(post.pi(value.pi(eq(
        &r.term,
        Expr::apps(yes.term.clone(), [post.term.clone(), value.term.clone()]),
        target.term.clone(),
    ))));
    let hn = sc.local(post.pi(failure.pi(eq(
        &r.term,
        Expr::apps(no.term.clone(), [post.term.clone(), failure.term.clone()]),
        target.term.clone(),
    ))));
    let raw = sc.local(result(&s.term, &e.term, &a.term));
    let ignored = sc.local(s.term.clone());
    let converted = |computation: Expr| {
        apps(
            TO_CPS,
            [
                s.term.clone(),
                e.term.clone(),
                a.term.clone(),
                r.term.clone(),
                computation,
                input.term.clone(),
                yes.term.clone(),
                no.term.clone(),
            ],
        )
    };
    let equation = |observed: Expr| {
        eq(
            &r.term,
            converted(ignored.lam(observed)),
            target.term.clone(),
        )
    };
    let motive = raw.lam(equation(raw.term.clone()));
    let status = sc.local(outcome(&e.term, &a.term));
    let packed = |status: Expr| {
        pair(
            &s.term,
            &outcome(&e.term, &a.term),
            post.term.clone(),
            status,
        )
    };
    let inner_motive = status.lam(equation(packed(status.term.clone())));
    let failed = failure.lam(Expr::apps(
        hn.term.clone(),
        [post.term.clone(), failure.term.clone()],
    ));
    let normal = value.lam(Expr::apps(
        hy.term.clone(),
        [post.term.clone(), value.term.clone()],
    ));
    let inner = outcome_cases(
        &e.term,
        &a.term,
        inner_motive,
        failed,
        normal,
        status.term.clone(),
        true,
    );
    let through = result_cases(
        &s.term,
        &e.term,
        &a.term,
        motive,
        lams(&[post, status], inner),
        Expr::app(m.term.clone(), input.term.clone()),
        true,
    );
    let actual = Expr::apps(
        code.term.clone(),
        [input.term.clone(), yes.term.clone(), no.term.clone()],
    );
    let middle = converted(m.term.clone());
    let first = Expr::apps(
        image.term.clone(),
        [input.term.clone(), yes.term.clone(), no.term.clone()],
    );
    let proof = trans(
        &r.term,
        actual.clone(),
        middle,
        target.term.clone(),
        first,
        through,
    );
    let goal = eq(&r.term, actual, target.term.clone());
    add(
        env,
        CPS_IMAGE_CONSTANT_OBSERVER,
        &[s, e, a, r, m, code, image, yes, no, target, input, hy, hn],
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
        install_image_constant_observer_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env
    }
    #[test]
    fn cps_image_replay_constant_observer_requires_dependency_and_refuses_collision() {
        let mut missing = build_environment().unwrap();
        let count = missing.num_constants();
        assert!(install_image_constant_observer_into(&mut missing).is_err());
        assert_eq!(missing.num_constants(), count);
        let mut env = environment();
        let count = env.num_constants();
        assert!(install_image_constant_observer_into(&mut env).is_err());
        assert_eq!(env.num_constants(), count);
    }
    #[test]
    fn cps_image_replay_constant_observer_retains_both_changed_poststates_and_payloads() {
        check(false, 0);
        check(true, 0);
    }
    #[test]
    fn cps_image_replay_constant_observer_refuses_ungrounded_image_and_either_callback() {
        for bad in 1..=3 {
            check(bad == 3, bad);
        }
    }
    fn check(failing: bool, bad: usize) {
        let env = environment();
        let nat = Expr::const_str("Nat");
        let mut sc = Scope::default();
        let state = sc.local(nat.clone());
        let post = sc.local(nat.clone());
        let value = sc.local(nat.clone());
        let failure = sc.local(nat.clone());
        let image_yes = sc.local(continuation(&nat, &nat, &nat));
        let image_no = sc.local(continuation(&nat, &nat, &nat));
        let outcome = apps(
            if failing { "Except.error" } else { "Except.ok" },
            [
                nat.clone(),
                nat.clone(),
                Expr::nat_lit(if failing { 7 } else { 5 }),
            ],
        );
        let observed = pair(&nat, &super::outcome(&nat, &nat), Expr::nat_lit(9), outcome);
        let m = state.lam(observed.clone());
        let converted = apps(
            TO_CPS,
            [
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                m.clone(),
            ],
        );
        let code = if bad == 1 {
            lams(
                &[state.clone(), image_yes.clone(), image_no.clone()],
                Expr::nat_lit(11),
            )
        } else {
            converted.clone()
        };
        let image = lams(
            &[state.clone(), image_yes.clone(), image_no.clone()],
            refl(
                &nat,
                Expr::apps(
                    converted,
                    [
                        state.term.clone(),
                        image_yes.term.clone(),
                        image_no.term.clone(),
                    ],
                ),
            ),
        );
        let target = Expr::nat_lit(2);
        let yes = lams(
            &[post.clone(), value.clone()],
            if bad == 2 {
                post.term.clone()
            } else {
                target.clone()
            },
        );
        let no = lams(
            &[post.clone(), failure.clone()],
            if bad == 3 {
                post.term.clone()
            } else {
                target.clone()
            },
        );
        let hy = lams(&[post.clone(), value], refl(&nat, target.clone()));
        let hn = lams(&[post, failure], refl(&nat, target.clone()));
        let input = Expr::nat_lit(0);
        let proof = apps(
            CPS_IMAGE_CONSTANT_OBSERVER,
            [
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                m.clone(),
                code.clone(),
                image,
                yes.clone(),
                no.clone(),
                target.clone(),
                input.clone(),
                hy,
                hn,
            ],
        );
        let claim = eq(&nat, Expr::apps(code, [input.clone(), yes, no]), target);
        let levels = [(Name::from_string("u"), Level::zero())];
        let claim = claim.instantiate_level_params(&levels);
        let proof = proof.instantiate_level_params(&levels);
        let checker = TypeChecker::new(&env);
        assert!(checker.infer_sort(&claim).unwrap().is_zero());
        let bytes = trust_ir::proof::encode_clean_expr_v1(&proof).unwrap();
        let proof = trust_ir::proof::decode_clean_expr_v1(&bytes).unwrap();
        if bad != 0 {
            assert!(matches!(
                checker.check_type(&proof, &claim),
                Err(clean_kernel::tc::TypeError::TypeMismatch { .. })
            ));
        } else {
            checker.check_type(&proof, &claim).unwrap();
            assert!(env.audit_certification(&claim, &proof).is_certified());
            let world_claim = eq(
                &result(&nat, &nat, &nat),
                Expr::app(m, input),
                observed.clone(),
            )
            .instantiate_level_params(&levels);
            let world_proof =
                refl(&result(&nat, &nat, &nat), observed).instantiate_level_params(&levels);
            checker.check_type(&world_proof, &world_claim).unwrap();
            assert!(
                env.audit_certification(&world_claim, &world_proof)
                    .is_certified()
            );
        }
    }
}
