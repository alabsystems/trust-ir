// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Conditional framing of actual Runs, with explicit premises for each operand.
//! Failure worlds are retained unchanged. This supplies no arbitrary-CPS inverse.
use super::*;

pub(super) fn install(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a, b] = sc.types();
    let sf = prod(&s.term, &f.term);
    let m = sc.local(run(&sf, &e.term, &a.term));
    let k = sc.local(Expr::arrow(a.term.clone(), run(&sf, &e.term, &b.term)));
    let probe = sc.local(sf.clone());
    let argument = sc.local(a.term.clone());
    let frame = |state: Expr| projection(1, &s.term, &f.term, state);
    let observe = |value_ty: &Expr, initial: Expr, observed: Expr| {
        project(&s.term, &f.term, &e.term, value_ty, initial, observed)
    };
    let hm = sc.local(probe.pi(eq(
        &f.term,
        observe(
            &a.term,
            frame(probe.term.clone()),
            Expr::app(m.term.clone(), probe.term.clone()),
        ),
        frame(probe.term.clone()),
    )));
    let hk = sc.local(argument.pi(probe.pi(eq(
        &f.term,
        observe(
            &b.term,
            frame(probe.term.clone()),
            Expr::apps(k.term.clone(), [argument.term.clone(), probe.term.clone()]),
        ),
        frame(probe.term.clone()),
    ))));
    let state = sc.local(sf.clone());
    let initial = frame(state.term.clone());
    let raw = sc.local(result(&sf, &e.term, &a.term));
    let ignored = sc.local(sf.clone());
    let equation = |observed: Expr| {
        eq(
            &f.term,
            observe(
                &b.term,
                initial.clone(),
                bind(
                    &sf,
                    &e.term,
                    &a.term,
                    &b.term,
                    ignored.lam(observed),
                    k.term.clone(),
                    state.term.clone(),
                ),
            ),
            initial.clone(),
        )
    };
    let premise = |observed: Expr| {
        eq(
            &f.term,
            observe(&a.term, initial.clone(), observed),
            initial.clone(),
        )
    };
    let motive = raw.lam(Expr::arrow(
        premise(raw.term.clone()),
        equation(raw.term.clone()),
    ));
    let post = sc.local(sf.clone());
    let status = sc.local(outcome(&e.term, &a.term));
    let packed = |status: Expr| pair(&sf, &outcome(&e.term, &a.term), post.term.clone(), status);
    let inner_motive = status.lam(Expr::arrow(
        premise(packed(status.term.clone())),
        equation(packed(status.term.clone())),
    ));
    let failure = sc.local(e.term.clone());
    let failed = packed(apps(
        "Except.error",
        [e.term.clone(), a.term.clone(), failure.term.clone()],
    ));
    let failure_h = sc.local(premise(failed));
    let failure_proof = failure.lam(failure_h.lam(refl(&f.term, initial.clone())));
    let value = sc.local(a.term.clone());
    let succeeded = packed(apps(
        "Except.ok",
        [e.term.clone(), a.term.clone(), value.term.clone()],
    ));
    let success_h = sc.local(premise(succeeded));
    let next_frame = frame(post.term.clone());
    let next = Expr::apps(k.term.clone(), [value.term.clone(), post.term.clone()]);
    let at_next = observe(&b.term, next_frame.clone(), next.clone());
    let at_initial = observe(&b.term, initial.clone(), next.clone());
    let variable_frame = sc.local(f.term.clone());
    let change_frame = congr_arg(
        &f.term,
        &f.term,
        next_frame.clone(),
        initial.clone(),
        variable_frame.lam(observe(&b.term, variable_frame.term.clone(), next)),
        success_h.term.clone(),
    );
    let reverse = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(u())]),
        [
            f.term.clone(),
            at_next.clone(),
            at_initial.clone(),
            change_frame,
        ],
    );
    let next_preserves = Expr::apps(hk.term.clone(), [value.term.clone(), post.term.clone()]);
    let through_next = trans(
        &f.term,
        at_initial.clone(),
        at_next,
        next_frame.clone(),
        reverse,
        next_preserves,
    );
    let complete = trans(
        &f.term,
        at_initial,
        next_frame,
        initial.clone(),
        through_next,
        success_h.term.clone(),
    );
    let success_proof = value.lam(success_h.lam(complete));
    let inner = outcome_cases(
        &e.term,
        &a.term,
        inner_motive,
        failure_proof,
        success_proof,
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
    let proof = Expr::app(cases, Expr::app(hm.term.clone(), state.term.clone()));
    let goal = eq(
        &f.term,
        observe(
            &b.term,
            initial.clone(),
            bind(
                &sf,
                &e.term,
                &a.term,
                &b.term,
                m.term.clone(),
                k.term.clone(),
                state.term.clone(),
            ),
        ),
        initial,
    );
    add(
        env,
        SUCCESS_FRAME_BIND_PRESERVES,
        &[s, f, e, a, b, m, k, hm, hk, state],
        goal,
        proof,
        true,
    )?;
    constant_observer(env)
}

fn constant_observer(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, f, e, a, b] = sc.types();
    let sf = prod(&s.term, &f.term);
    let m = sc.local(run(&sf, &e.term, &a.term));
    let k = sc.local(Expr::arrow(a.term.clone(), run(&sf, &e.term, &b.term)));
    let initial = sc.local(f.term.clone());
    let post = sc.local(sf.clone());
    let value = sc.local(a.term.clone());
    let hk = sc.local(value.pi(post.pi(eq(
        &f.term,
        project(
            &s.term,
            &f.term,
            &e.term,
            &b.term,
            initial.term.clone(),
            Expr::apps(k.term.clone(), [value.term.clone(), post.term.clone()]),
        ),
        initial.term.clone(),
    ))));
    let state = sc.local(sf.clone());
    let raw = sc.local(result(&sf, &e.term, &a.term));
    let ignored = sc.local(sf.clone());
    let equation = |observed: Expr| {
        eq(
            &f.term,
            project(
                &s.term,
                &f.term,
                &e.term,
                &b.term,
                initial.term.clone(),
                bind(
                    &sf,
                    &e.term,
                    &a.term,
                    &b.term,
                    ignored.lam(observed),
                    k.term.clone(),
                    state.term.clone(),
                ),
            ),
            initial.term.clone(),
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
    let failure = sc.local(e.term.clone());
    let inner = outcome_cases(
        &e.term,
        &a.term,
        inner_motive,
        failure.lam(refl(&f.term, initial.term.clone())),
        value.lam(Expr::apps(
            hk.term.clone(),
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
        project(
            &s.term,
            &f.term,
            &e.term,
            &b.term,
            initial.term.clone(),
            bind(
                &sf,
                &e.term,
                &a.term,
                &b.term,
                m.term.clone(),
                k.term.clone(),
                state.term.clone(),
            ),
        ),
        initial.term.clone(),
    );
    add(
        env,
        SUCCESS_FRAME_BIND_CONSTANT_OBSERVER,
        &[s, f, e, a, b, m, k, initial, hk, state],
        goal,
        proof,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn success_frame_conditional_bind_checks_normal_and_changed_failure_worlds() {
        check(false, false, false);
        check(true, false, false);
    }
    #[test]
    fn success_frame_conditional_bind_refuses_missing_continuation_frame_premise() {
        check(false, true, false);
    }
    #[test]
    fn success_frame_conditional_bind_refuses_missing_first_run_frame_premise() {
        check(false, false, true);
    }
    #[test]
    fn success_frame_cleanup_observer_needs_no_first_run_frame_premise() {
        let env = observer_environment();
        let nat = Expr::const_str("Nat");
        let sf = prod(&nat, &nat);
        let mut sc = Scope::default();
        let cleanup = sc.local(run(&sf, &nat, &nat));
        let pending = sc.local(nat.clone());
        let state = sc.local(sf.clone());
        let post = sc.local(sf.clone());
        let value = sc.local(nat.clone());
        let initial = projection(1, &nat, &nat, state.term.clone());
        let tail = value.lam(post.lam(pair(
            &sf,
            &outcome(&nat, &nat),
            post.term.clone(),
            apps(
                "Except.error",
                [nat.clone(), nat.clone(), pending.term.clone()],
            ),
        )));
        let hk = value.lam(post.lam(refl(&nat, initial.clone())));
        let proof = apps(
            SUCCESS_FRAME_BIND_CONSTANT_OBSERVER,
            [
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                cleanup.term.clone(),
                tail.clone(),
                initial.clone(),
                hk,
                state.term.clone(),
            ],
        );
        let goal = eq(
            &nat,
            project(
                &nat,
                &nat,
                &nat,
                &nat,
                initial.clone(),
                bind(
                    &sf,
                    &nat,
                    &nat,
                    &nat,
                    cleanup.term.clone(),
                    tail,
                    state.term.clone(),
                ),
            ),
            initial,
        );
        let vars = [cleanup, pending, state];
        audit(&env, lams(&vars, proof), pis(&vars, goal), false);
    }
    #[test]
    fn success_frame_cleanup_observer_retains_both_actual_error_worlds_and_payloads() {
        observer_case(false, false);
        observer_case(true, false);
    }
    #[test]
    fn success_frame_cleanup_observer_rejects_a_normal_tail_with_changed_frame() {
        observer_case(false, true);
    }
    fn observer_environment() -> Environment {
        let mut env = build_environment().unwrap();
        install_success_framing_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env
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
    fn observer_case(first_error: bool, bad_tail: bool) {
        let env = observer_environment();
        let nat = Expr::const_str("Nat");
        let sf = prod(&nat, &nat);
        let status = outcome(&nat, &nat);
        let mut sc = Scope::default();
        let state = sc.local(sf.clone());
        let value = sc.local(nat.clone());
        let post = sc.local(sf.clone());
        let changed = pair(
            &nat,
            &nat,
            Expr::nat_lit(if first_error { 4 } else { 3 }),
            Expr::nat_lit(if first_error { 13 } else { 9 }),
        );
        let cleanup = state.lam(pair(
            &sf,
            &status,
            changed.clone(),
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
        let tail = value.lam(post.lam(pair(
            &sf,
            &status,
            if bad_tail {
                changed.clone()
            } else {
                post.term.clone()
            },
            apps(
                if bad_tail {
                    "Except.ok"
                } else {
                    "Except.error"
                },
                [nat.clone(), nat.clone(), Expr::nat_lit(11)],
            ),
        )));
        let initial = Expr::nat_lit(2);
        let input = pair(&nat, &nat, Expr::nat_lit(0), initial.clone());
        let hk = value.lam(post.lam(refl(&nat, initial.clone())));
        let proof = apps(
            SUCCESS_FRAME_BIND_CONSTANT_OBSERVER,
            [
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                cleanup.clone(),
                tail.clone(),
                initial.clone(),
                hk,
                input.clone(),
            ],
        );
        let actual = bind(&sf, &nat, &nat, &nat, cleanup, tail, input);
        let claim = eq(
            &nat,
            project(&nat, &nat, &nat, &nat, initial.clone(), actual.clone()),
            initial,
        );
        audit(&env, proof, claim, bad_tail);
        if !bad_tail {
            let expected = pair(
                &sf,
                &status,
                changed.clone(),
                apps(
                    "Except.error",
                    [
                        nat.clone(),
                        nat.clone(),
                        Expr::nat_lit(if first_error { 7 } else { 11 }),
                    ],
                ),
            );
            audit(
                &env,
                refl(&result(&sf, &nat, &nat), expected.clone()),
                eq(&result(&sf, &nat, &nat), actual.clone(), expected),
                false,
            );
            let wrong = pair(
                &sf,
                &status,
                changed,
                apps(
                    "Except.error",
                    [
                        nat.clone(),
                        nat.clone(),
                        Expr::nat_lit(if first_error { 11 } else { 7 }),
                    ],
                ),
            );
            audit(
                &env,
                refl(&result(&sf, &nat, &nat), wrong.clone()),
                eq(&result(&sf, &nat, &nat), actual, wrong),
                true,
            );
        }
    }
    fn check(failing: bool, bad_continuation: bool, bad_first: bool) {
        let mut env = build_environment().unwrap();
        install_success_framing_into(&mut env).unwrap();
        env.init_nat().unwrap();
        let nat = Expr::const_str("Nat");
        let sf = prod(&nat, &nat);
        let mut sc = Scope::default();
        let state = sc.local(sf.clone());
        let value = sc.local(nat.clone());
        let input = sc.local(sf.clone());
        let frame = |state: Expr| projection(1, &nat, &nat, state);
        let changed = pair(&nat, &nat, Expr::nat_lit(3u64), Expr::nat_lit(9u64));
        let result_at = |post: Expr, failed: bool| {
            pair(
                &sf,
                &outcome(&nat, &nat),
                post,
                apps(
                    if failed { "Except.error" } else { "Except.ok" },
                    [nat.clone(), nat.clone(), Expr::nat_lit(0u64)],
                ),
            )
        };
        let m = state.lam(result_at(
            if failing || bad_first {
                changed.clone()
            } else {
                state.term.clone()
            },
            failing,
        ));
        let k = value.lam(state.lam(result_at(
            if bad_continuation {
                changed
            } else {
                state.term.clone()
            },
            false,
        )));
        let hm = state.lam(refl(&nat, frame(state.term.clone())));
        let hk = value.lam(state.lam(refl(&nat, frame(state.term.clone()))));
        let proof = apps(
            SUCCESS_FRAME_BIND_PRESERVES,
            [
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                nat.clone(),
                m.clone(),
                k.clone(),
                hm,
                hk,
                input.term.clone(),
            ],
        );
        let goal = eq(
            &nat,
            project(
                &nat,
                &nat,
                &nat,
                &nat,
                frame(input.term.clone()),
                bind(&sf, &nat, &nat, &nat, m, k, input.term.clone()),
            ),
            frame(input.term.clone()),
        );
        let levels = [(Name::from_string("u"), Level::zero())];
        let claim = input.pi(goal).instantiate_level_params(&levels);
        let proof = input.lam(proof).instantiate_level_params(&levels);
        let checker = TypeChecker::new(&env);
        assert!(checker.infer_sort(&claim).unwrap().is_zero());
        let bytes = trust_ir::proof::encode_clean_expr_v1(&proof).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_v1(&bytes).unwrap();
        if bad_continuation || bad_first {
            assert!(matches!(
                checker.check_type(&decoded, &claim),
                Err(clean_kernel::tc::TypeError::TypeMismatch { .. })
            ));
        } else {
            checker.check_type(&decoded, &claim).unwrap();
            assert!(env.audit_certification(&claim, &decoded).is_certified());
        }
    }
}
