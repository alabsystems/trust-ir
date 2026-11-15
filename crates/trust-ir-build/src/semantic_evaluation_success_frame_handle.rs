// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Actual poststates and heterogeneous errors in constant-observer handling.
//! Neither the first Run nor either handler acquires physical provider authority.
use super::*;
pub const SUCCESS_FRAME_HANDLE_CONSTANT_OBSERVER: &str =
    "TrustIR.Eval.SuccessFrame.handle_constant_observer";

pub fn install_success_handle_observer_into(
    env: &mut Environment,
) -> Result<(), SemanticEvaluationError> {
    if env
        .get_const(&Name::from_string(SUCCESS_FRAME_HANDLE_CONSTANT_OBSERVER))
        .is_some()
    {
        return Err(error(
            SUCCESS_FRAME_HANDLE_CONSTANT_OBSERVER,
            "owned declaration already exists",
        ));
    }
    // Required original vocabularies are checked before any mutation.
    recheck_theorem(env, TO_CPS_HANDLE)?;
    recheck_theorem(env, SUCCESS_FRAME_CPS_OBSERVER)?;
    law(env)?;
    recheck_theorem(env, SUCCESS_FRAME_HANDLE_CONSTANT_OBSERVER)
}
fn observed(s: &Expr, f: &Expr, e: &Expr, a: &Expr, target: Expr, value: Expr) -> Expr {
    apps(
        SUCCESS_FRAME_PROJECTION,
        [s.clone(), f.clone(), e.clone(), a.clone(), target, value],
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
    let value = sc.local(a.term.clone());
    let failure = sc.local(e.term.clone());
    let post = sc.local(sf.clone());
    let predicate = |handler: Expr, arg: Expr| {
        eq(
            &f.term,
            observed(
                &s.term,
                &f.term,
                &fe.term,
                &b.term,
                target.term.clone(),
                Expr::apps(handler, [arg, post.term.clone()]),
            ),
            target.term.clone(),
        )
    };
    let hy = sc.local(value.pi(post.pi(predicate(yes.term.clone(), value.term.clone()))));
    let hn = sc.local(failure.pi(post.pi(predicate(no.term.clone(), failure.term.clone()))));
    let state = sc.local(sf.clone());
    let raw = sc.local(result(&sf, &e.term, &a.term));
    let ignored = sc.local(sf.clone());
    let equation = |observed_value: Expr| {
        eq(
            &f.term,
            observed(
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
                    ignored.lam(observed_value),
                    yes.term.clone(),
                    no.term.clone(),
                    state.term.clone(),
                ),
            ),
            target.term.clone(),
        )
    };
    let motive = raw.lam(equation(raw.term.clone()));
    let status = sc.local(outcome(&e.term, &a.term));
    let inner_motive = status.lam(equation(pair(
        &sf,
        &outcome(&e.term, &a.term),
        post.term.clone(),
        status.term.clone(),
    )));
    let inner = outcome_cases(
        &e.term,
        &a.term,
        inner_motive,
        failure.lam(Expr::apps(
            hn.term.clone(),
            [failure.term.clone(), post.term.clone()],
        )),
        value.lam(Expr::apps(
            hy.term.clone(),
            [value.term.clone(), post.term.clone()],
        )),
        status.term.clone(),
        true,
    );
    let proof = result_cases(
        &sf,
        &e.term,
        &a.term,
        motive,
        lams(&[post, status], inner),
        Expr::app(m.term.clone(), state.term.clone()),
        true,
    );
    let goal = eq(
        &f.term,
        observed(
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
                state.term.clone(),
            ),
        ),
        target.term.clone(),
    );
    add(
        env,
        SUCCESS_FRAME_HANDLE_CONSTANT_OBSERVER,
        &[s, f, e, a, fe, b, m, yes, no, target, hy, hn, state],
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
        install_success_handle_observer_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env
    }
    #[test]
    fn success_frame_handle_observer_requires_original_dependencies_and_refuses_collision() {
        let mut missing = build_environment().unwrap();
        let count = missing.num_constants();
        assert!(install_success_handle_observer_into(&mut missing).is_err());
        assert_eq!(missing.num_constants(), count);
        let mut env = environment();
        let count = env.num_constants();
        assert!(install_success_handle_observer_into(&mut env).is_err());
        assert_eq!(env.num_constants(), count);
    }
    #[test]
    fn success_frame_handle_observer_retains_actual_worlds_and_heterogeneous_error_dispatch() {
        check(false, 0);
        check(true, 0);
    }
    #[test]
    fn success_frame_handle_observer_refuses_either_missing_handler_observer_premise() {
        check(false, 1);
        check(true, 2);
    }
    fn audit(env: &Environment, proof: Expr, claim: Expr, reject: bool) {
        let levels = [(Name::from_string("u"), Level::zero())];
        let proof = proof.instantiate_level_params(&levels);
        let claim = claim.instantiate_level_params(&levels);
        let checker = TypeChecker::new(env);
        assert!(checker.infer_sort(&claim).unwrap().is_zero());
        let wire = trust_ir::proof::encode_clean_expr_v1(&proof).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_v1(&wire).unwrap();
        if reject {
            assert!(matches!(
                checker.check_type(&decoded, &claim),
                Err(clean_kernel::tc::TypeError::TypeMismatch { .. })
            ));
        } else {
            checker.check_type(&decoded, &claim).unwrap();
            assert!(env.audit_certification(&claim, &decoded).is_certified());
        }
    }
    fn check(first_error: bool, bad: usize) {
        let env = environment();
        let nat = Expr::const_str("Nat");
        let boolean = Expr::const_str("Bool");
        let sf = prod(&nat, &nat);
        let mut sc = Scope::default();
        let state = sc.local(sf.clone());
        let post = sc.local(sf.clone());
        let value = sc.local(nat.clone());
        let failure = sc.local(nat.clone());
        let actual_post = pair(
            &nat,
            &nat,
            Expr::nat_lit(if first_error { 4 } else { 3 }),
            Expr::nat_lit(if first_error { 13 } else { 9 }),
        );
        let m = state.lam(pair(
            &sf,
            &outcome(&nat, &nat),
            actual_post.clone(),
            apps(
                if first_error {
                    "Except.error"
                } else {
                    "Except.ok"
                },
                [
                    nat.clone(),
                    nat.clone(),
                    Expr::nat_lit(if first_error { 7 } else { 0 }),
                ],
            ),
        ));
        let make = |normal: bool, truth: bool| {
            pair(
                &sf,
                &outcome(&boolean, &nat),
                post.term.clone(),
                apps(
                    if normal { "Except.ok" } else { "Except.error" },
                    [
                        boolean.clone(),
                        nat.clone(),
                        if normal {
                            Expr::nat_lit(0)
                        } else {
                            Expr::const_str(if truth { "Bool.true" } else { "Bool.false" })
                        },
                    ],
                ),
            )
        };
        let yes = value.lam(post.lam(make(bad == 1, true)));
        let no = failure.lam(post.lam(make(bad == 2, false)));
        let target = Expr::nat_lit(2);
        let hy = value.lam(post.lam(refl(&nat, target.clone())));
        let hn = failure.lam(post.lam(refl(&nat, target.clone())));
        let input = pair(&nat, &nat, Expr::nat_lit(0), target.clone());
        let proof = apps(
            SUCCESS_FRAME_HANDLE_CONSTANT_OBSERVER,
            [
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                boolean.clone(),
                nat.clone(),
                m.clone(),
                yes.clone(),
                no.clone(),
                target.clone(),
                hy,
                hn,
                input.clone(),
            ],
        );
        let actual = handled(&sf, &nat, &nat, &boolean, &nat, m, yes, no, input.clone());
        let claim = eq(
            &nat,
            observed(&nat, &nat, &boolean, &nat, target.clone(), actual.clone()),
            target,
        );
        audit(&env, proof, claim, bad != 0);
        if bad == 0 {
            let expected = pair(
                &sf,
                &outcome(&boolean, &nat),
                actual_post,
                apps(
                    "Except.error",
                    [
                        boolean.clone(),
                        nat.clone(),
                        Expr::const_str(if first_error {
                            "Bool.false"
                        } else {
                            "Bool.true"
                        }),
                    ],
                ),
            );
            audit(
                &env,
                refl(&result(&sf, &boolean, &nat), expected.clone()),
                eq(&result(&sf, &boolean, &nat), actual.clone(), expected),
                false,
            );
            let stale = pair(
                &sf,
                &outcome(&boolean, &nat),
                input,
                apps(
                    "Except.error",
                    [
                        boolean.clone(),
                        nat.clone(),
                        Expr::const_str(if first_error {
                            "Bool.true"
                        } else {
                            "Bool.false"
                        }),
                    ],
                ),
            );
            audit(
                &env,
                refl(&result(&sf, &boolean, &nat), stale.clone()),
                eq(&result(&sf, &boolean, &nat), actual, stale),
                true,
            );
        }
    }
}
