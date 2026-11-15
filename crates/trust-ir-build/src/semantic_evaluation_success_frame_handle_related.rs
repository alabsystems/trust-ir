// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Handle composition with an explicitly related normal state and an error
//! observer valid for EVERY actual error state. No state restoration follows.
use super::*;
pub const SUCCESS_FRAME_HANDLE_RELATED_OBSERVER: &str =
    "TrustIR.Eval.SuccessFrame.handle_related_observer";
pub fn install_success_handle_related_into(
    env: &mut Environment,
) -> Result<(), SemanticEvaluationError> {
    if env
        .get_const(&Name::from_string(SUCCESS_FRAME_HANDLE_RELATED_OBSERVER))
        .is_some()
    {
        return Err(error(
            SUCCESS_FRAME_HANDLE_RELATED_OBSERVER,
            "owned declaration already exists",
        ));
    }
    recheck_theorem(env, CPS_IMAGE_HANDLE)?;
    recheck_theorem(env, SUCCESS_FRAME_CPS_OBSERVER)?;
    law(env)?;
    recheck_theorem(env, SUCCESS_FRAME_HANDLE_RELATED_OBSERVER)
}
fn project(s: &Expr, f: &Expr, e: &Expr, a: &Expr, target: Expr, result: Expr) -> Expr {
    apps(
        SUCCESS_FRAME_PROJECTION,
        [s.clone(), f.clone(), e.clone(), a.clone(), target, result],
    )
}
fn handled(
    sf: &Expr,
    e: &Expr,
    a: &Expr,
    fe: &Expr,
    b: &Expr,
    m: Expr,
    yes: Expr,
    no: Expr,
    state: Expr,
) -> Expr {
    apps(
        HANDLE,
        [
            sf.clone(),
            e.clone(),
            a.clone(),
            fe.clone(),
            b.clone(),
            m,
            yes,
            no,
            state,
        ],
    )
}
fn law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a, fe, b] = sc.types();
    let sf = prod(&s.term, &f.term);
    let m = sc.local(run(&sf, &e.term, &a.term));
    let yes = sc.local(Expr::arrow(a.term.clone(), run(&sf, &fe.term, &b.term)));
    let no = sc.local(Expr::arrow(e.term.clone(), run(&sf, &fe.term, &b.term)));
    let target = sc.local(f.term.clone());
    let input = sc.local(sf.clone());
    let frame = |state: Expr| projection(1, &s.term, &f.term, state);
    let initial = frame(input.term.clone());
    let probe = sc.local(sf.clone());
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
    let pre = sc.local(eq(&f.term, initial.clone(), target.term.clone()));
    let post = sc.local(sf.clone());
    let value = sc.local(a.term.clone());
    let failure = sc.local(e.term.clone());
    let relation = sc.local(eq(&f.term, frame(post.term.clone()), target.term.clone()));
    let observed = |handler: Expr, arg: Expr| {
        project(
            &s.term,
            &f.term,
            &fe.term,
            &b.term,
            target.term.clone(),
            Expr::apps(handler, [arg, post.term.clone()]),
        )
    };
    let hy = sc.local(value.pi(post.pi(relation.pi(eq(
        &f.term,
        observed(yes.term.clone(), value.term.clone()),
        target.term.clone(),
    )))));
    let hn = sc.local(failure.pi(post.pi(eq(
        &f.term,
        observed(no.term.clone(), failure.term.clone()),
        target.term.clone(),
    ))));
    let raw = sc.local(result(&sf, &e.term, &a.term));
    let ignored = sc.local(sf.clone());
    let premise = |data: Expr| {
        eq(
            &f.term,
            project(&s.term, &f.term, &e.term, &a.term, initial.clone(), data),
            initial.clone(),
        )
    };
    let equation = |data: Expr| {
        eq(
            &f.term,
            project(
                &s.term,
                &f.term,
                &fe.term,
                &b.term,
                target.term.clone(),
                handled(
                    &sf,
                    &e.term,
                    &a.term,
                    &fe.term,
                    &b.term,
                    ignored.lam(data),
                    yes.term.clone(),
                    no.term.clone(),
                    input.term.clone(),
                ),
            ),
            target.term.clone(),
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
    let error_h = sc.local(premise(failed));
    let error_proof = failure.lam(error_h.lam(Expr::apps(
        hn.term.clone(),
        [failure.term.clone(), post.term.clone()],
    )));
    let normal = packed(apps(
        "Except.ok",
        [e.term.clone(), a.term.clone(), value.term.clone()],
    ));
    let normal_h = sc.local(premise(normal));
    let related = trans(
        &f.term,
        frame(post.term.clone()),
        initial,
        target.term.clone(),
        normal_h.term.clone(),
        pre.term.clone(),
    );
    let normal_proof = value.lam(normal_h.lam(Expr::apps(
        hy.term.clone(),
        [value.term.clone(), post.term.clone(), related],
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
        Expr::app(m.term.clone(), input.term.clone()),
        true,
    );
    let proof = Expr::app(cases, Expr::app(preserves.term.clone(), input.term.clone()));
    let goal = eq(
        &f.term,
        project(
            &s.term,
            &f.term,
            &fe.term,
            &b.term,
            target.term.clone(),
            handled(
                &sf,
                &e.term,
                &a.term,
                &fe.term,
                &b.term,
                m.term.clone(),
                yes.term.clone(),
                no.term.clone(),
                input.term.clone(),
            ),
        ),
        target.term.clone(),
    );
    add(
        env,
        SUCCESS_FRAME_HANDLE_RELATED_OBSERVER,
        &[
            s, f, e, a, fe, b, m, yes, no, target, input, preserves, pre, hy, hn,
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
        install_success_handle_related_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env
    }
    #[test]
    fn success_frame_handle_related_requires_dependencies_and_refuses_collision() {
        let mut env = build_environment().unwrap();
        let count = env.num_constants();
        assert!(install_success_handle_related_into(&mut env).is_err());
        assert_eq!(env.num_constants(), count);
        let mut env = environment();
        let count = env.num_constants();
        assert!(install_success_handle_related_into(&mut env).is_err());
        assert_eq!(env.num_constants(), count);
    }
    #[test]
    fn success_frame_handle_related_checks_normal_relation_and_keeps_replacement_error_world() {
        check(false, 0);
        check(true, 0);
    }
    #[test]
    fn success_frame_handle_related_refuses_bad_run_precondition_normal_and_recovering_error_handlers()
     {
        for bad in 1..=4 {
            check(bad == 4, bad);
        }
    }
    fn check(failing: bool, bad: usize) {
        let env = environment();
        let nat = Expr::const_str("Nat");
        let sf = prod(&nat, &nat);
        let mut sc = Scope::default();
        let input = sc.local(sf.clone());
        let post = sc.local(sf.clone());
        let value = sc.local(nat.clone());
        let failure = sc.local(nat.clone());
        let frame = |state: Expr| projection(1, &nat, &nat, state);
        let m = input.lam(pair(
            &sf,
            &outcome(&nat, &nat),
            pair(
                &nat,
                &nat,
                Expr::nat_lit(3),
                if failing || bad == 1 {
                    Expr::nat_lit(13)
                } else {
                    frame(input.term.clone())
                },
            ),
            apps(
                if failing { "Except.error" } else { "Except.ok" },
                [
                    nat.clone(),
                    nat.clone(),
                    Expr::nat_lit(if failing { 11 } else { 5 }),
                ],
            ),
        ));
        let target = Expr::nat_lit(if bad == 2 { 9 } else { 2 });
        let yes = lams(
            &[value.clone(), post.clone()],
            pair(
                &sf,
                &outcome(&nat, &nat),
                pair(
                    &nat,
                    &nat,
                    Expr::nat_lit(9),
                    if bad == 3 {
                        Expr::nat_lit(17)
                    } else {
                        frame(post.term.clone())
                    },
                ),
                apps("Except.ok", [nat.clone(), nat.clone(), Expr::nat_lit(5)]),
            ),
        );
        let no = lams(
            &[failure.clone(), post.clone()],
            pair(
                &sf,
                &outcome(&nat, &nat),
                pair(&nat, &nat, Expr::nat_lit(9), Expr::nat_lit(17)),
                apps(
                    if bad == 4 {
                        "Except.ok"
                    } else {
                        "Except.error"
                    },
                    [
                        nat.clone(),
                        nat.clone(),
                        Expr::nat_lit(if bad == 4 { 5 } else { 7 }),
                    ],
                ),
            ),
        );
        let preserves = input.lam(refl(&nat, frame(input.term.clone())));
        let relation = sc.local(eq(&nat, frame(post.term.clone()), target.clone()));
        let hy = lams(
            &[value, post.clone(), relation.clone()],
            relation.term.clone(),
        );
        let hn = lams(&[failure, post], refl(&nat, target.clone()));
        let state = pair(&nat, &nat, Expr::nat_lit(0), Expr::nat_lit(2));
        let proof = apps(
            SUCCESS_FRAME_HANDLE_RELATED_OBSERVER,
            [
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                m.clone(),
                yes.clone(),
                no.clone(),
                target.clone(),
                state.clone(),
                preserves,
                refl(&nat, Expr::nat_lit(2)),
                hy,
                hn,
            ],
        );
        let actual = handled(&sf, &nat, &nat, &nat, &nat, m, yes, no, state);
        let claim = eq(
            &nat,
            project(&nat, &nat, &nat, &nat, target.clone(), actual.clone()),
            target,
        );
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
            let expected = pair(
                &sf,
                &outcome(&nat, &nat),
                pair(
                    &nat,
                    &nat,
                    Expr::nat_lit(9),
                    Expr::nat_lit(if failing { 17 } else { 2 }),
                ),
                apps(
                    if failing { "Except.error" } else { "Except.ok" },
                    [
                        nat.clone(),
                        nat.clone(),
                        Expr::nat_lit(if failing { 7 } else { 5 }),
                    ],
                ),
            );
            let exact = eq(&result(&sf, &nat, &nat), actual, expected.clone())
                .instantiate_level_params(&levels);
            let exact_proof =
                refl(&result(&sf, &nat, &nat), expected).instantiate_level_params(&levels);
            checker.check_type(&exact_proof, &exact).unwrap();
            assert!(env.audit_certification(&exact, &exact_proof).is_certified());
        }
    }
}
