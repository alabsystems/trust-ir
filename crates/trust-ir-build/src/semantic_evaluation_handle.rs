// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! First-order error handling and its checked CPS image. Both callbacks receive
//! the actual post-state. This does not assert that arbitrary provider CPS is
//! in that image, nor that a handler terminates in a physical implementation.
use super::*;

pub const HANDLE: &str = "TrustIR.Eval.handle";
pub const TO_CPS_HANDLE: &str = "TrustIR.Eval.to_cps_handle";

/// Extend an already checked evaluation vocabulary. Name collisions reject
/// before mutation. On any later error discard the partially extended env.
pub fn install_handle_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in [HANDLE, TO_CPS_HANDLE, CPS_IMAGE, CPS_IMAGE_HANDLE] {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    for theorem in THEOREMS {
        recheck_theorem(env, theorem)?;
    }
    definition(env)?;
    image(env)?;
    image_definition(env)?;
    image_composition(env)?;
    recheck_theorem(env, TO_CPS_HANDLE)?;
    recheck_theorem(env, CPS_IMAGE_HANDLE)
}

fn handle(s: &Expr, e: &Expr, a: &Expr, f: &Expr, b: &Expr, m: Expr, yes: Expr, no: Expr) -> Expr {
    apps(
        HANDLE,
        [
            s.clone(),
            e.clone(),
            a.clone(),
            f.clone(),
            b.clone(),
            m,
            yes,
            no,
        ],
    )
}

fn definition(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, f, b] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let yes = sc.local(Expr::arrow(a.term.clone(), run(&s.term, &f.term, &b.term)));
    let no = sc.local(Expr::arrow(e.term.clone(), run(&s.term, &f.term, &b.term)));
    let state = sc.local(s.term.clone());
    let observed = sc.local(result(&s.term, &e.term, &a.term));
    let next = sc.local(s.term.clone());
    let o = sc.local(outcome(&e.term, &a.term));
    let failure = sc.local(e.term.clone());
    let value = sc.local(a.term.clone());
    let rty = result(&s.term, &f.term, &b.term);
    let body = result_cases(
        &s.term,
        &e.term,
        &a.term,
        observed.lam(rty.clone()),
        lams(
            &[next.clone(), o.clone()],
            outcome_cases(
                &e.term,
                &a.term,
                o.lam(rty),
                failure.lam(Expr::apps(
                    no.term.clone(),
                    [failure.term.clone(), next.term.clone()],
                )),
                value.lam(Expr::apps(
                    yes.term.clone(),
                    [value.term.clone(), next.term.clone()],
                )),
                o.term.clone(),
                false,
            ),
        ),
        Expr::app(m.term.clone(), state.term.clone()),
        false,
    );
    add(
        env,
        HANDLE,
        &[s.clone(), e.clone(), a, f.clone(), b.clone(), m, yes, no],
        run(&s.term, &f.term, &b.term),
        state.lam(body),
        false,
    )
}

fn image(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, f, b, answer] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let yes = sc.local(Expr::arrow(a.term.clone(), run(&s.term, &f.term, &b.term)));
    let no = sc.local(Expr::arrow(e.term.clone(), run(&s.term, &f.term, &b.term)));
    let state = sc.local(s.term.clone());
    let ok = sc.local(continuation(&s.term, &b.term, &answer.term));
    let err = sc.local(continuation(&s.term, &f.term, &answer.term));
    let next = sc.local(s.term.clone());
    let value = sc.local(a.term.clone());
    let failure = sc.local(e.term.clone());
    let continued = |handler: Expr, next: Expr, value: Expr| {
        to_cps(
            &s.term,
            &f.term,
            &b.term,
            &answer.term,
            Expr::app(handler, value),
            next,
            ok.term.clone(),
            err.term.clone(),
        )
    };
    let yes_cps = lams(
        &[next.clone(), value.clone()],
        continued(yes.term.clone(), next.term.clone(), value.term.clone()),
    );
    let no_cps = lams(
        &[next.clone(), failure.clone()],
        continued(no.term.clone(), next.term.clone(), failure.term.clone()),
    );
    let equation = |computation: Expr| {
        eq(
            &answer.term,
            to_cps(
                &s.term,
                &f.term,
                &b.term,
                &answer.term,
                handle(
                    &s.term,
                    &e.term,
                    &a.term,
                    &f.term,
                    &b.term,
                    computation.clone(),
                    yes.term.clone(),
                    no.term.clone(),
                ),
                state.term.clone(),
                ok.term.clone(),
                err.term.clone(),
            ),
            to_cps(
                &s.term,
                &e.term,
                &a.term,
                &answer.term,
                computation,
                state.term.clone(),
                yes_cps.clone(),
                no_cps.clone(),
            ),
        )
    };
    let ignored = sc.local(s.term.clone());
    let proof = prove_result_cases(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        Expr::app(m.term.clone(), state.term.clone()),
        |r| equation(ignored.lam(r)),
        |next, error| refl(&answer.term, continued(no.term.clone(), next, error)),
        |next, value| refl(&answer.term, continued(yes.term.clone(), next, value)),
    );
    let statement = equation(m.term.clone());
    add(
        env,
        TO_CPS_HANDLE,
        &[s, e, a, f, b, answer, m, yes, no, state, ok, err],
        statement,
        proof,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cps_handle_image_is_kernel_checked_and_audited() {
        let mut env = build_environment().unwrap();
        install_handle_into(&mut env).unwrap();
        recheck_theorem(&env, TO_CPS_HANDLE).unwrap();
        assert!(install_handle_into(&mut env).is_err());
    }
}

// Prospective checked image-composition extension. Not authority until installed,
// kernel checked and audited with the actual endpoint evidence.
pub const CPS_IMAGE: &str = "TrustIR.Eval.CpsImage";
pub const CPS_IMAGE_HANDLE: &str = "TrustIR.Eval.cps_image_handle";

fn image_type(s: &Expr, e: &Expr, a: &Expr, r: &Expr, m: Expr, f: Expr) -> Expr {
    apps(
        CPS_IMAGE,
        [s.clone(), e.clone(), a.clone(), r.clone(), m, f],
    )
}
fn image_definition(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, r] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let f = sc.local(cps(&s.term, &e.term, &a.term, &r.term));
    let state = sc.local(s.term.clone());
    let ok = sc.local(continuation(&s.term, &a.term, &r.term));
    let err = sc.local(continuation(&s.term, &e.term, &r.term));
    let property = eq(
        &r.term,
        Expr::apps(
            f.term.clone(),
            [state.term.clone(), ok.term.clone(), err.term.clone()],
        ),
        to_cps(
            &s.term,
            &e.term,
            &a.term,
            &r.term,
            m.term.clone(),
            state.term.clone(),
            ok.term.clone(),
            err.term.clone(),
        ),
    );
    add(
        env,
        CPS_IMAGE,
        &[s, e, a, r, m, f],
        Expr::sort(Level::zero()),
        pis(&[state, ok, err], property),
        false,
    )
}
fn image_composition(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, ferr, b, r] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let f = sc.local(cps(&s.term, &e.term, &a.term, &r.term));
    let yes = sc.local(Expr::arrow(
        a.term.clone(),
        run(&s.term, &ferr.term, &b.term),
    ));
    let no = sc.local(Expr::arrow(
        e.term.clone(),
        run(&s.term, &ferr.term, &b.term),
    ));
    let ky = sc.local(Expr::arrow(
        a.term.clone(),
        cps(&s.term, &ferr.term, &b.term, &r.term),
    ));
    let kn = sc.local(Expr::arrow(
        e.term.clone(),
        cps(&s.term, &ferr.term, &b.term, &r.term),
    ));
    let hm = sc.local(image_type(
        &s.term,
        &e.term,
        &a.term,
        &r.term,
        m.term.clone(),
        f.term.clone(),
    ));
    let x = sc.local(a.term.clone());
    let error = sc.local(e.term.clone());
    let hy = sc.local(x.pi(image_type(
        &s.term,
        &ferr.term,
        &b.term,
        &r.term,
        Expr::app(yes.term.clone(), x.term.clone()),
        Expr::app(ky.term.clone(), x.term.clone()),
    )));
    let hn = sc.local(error.pi(image_type(
        &s.term,
        &ferr.term,
        &b.term,
        &r.term,
        Expr::app(no.term.clone(), error.term.clone()),
        Expr::app(kn.term.clone(), error.term.clone()),
    )));
    let state = sc.local(s.term.clone());
    let ok = sc.local(continuation(&s.term, &b.term, &r.term));
    let err = sc.local(continuation(&s.term, &ferr.term, &r.term));
    let next = sc.local(s.term.clone());
    let yes_cps = lams(
        &[next.clone(), x.clone()],
        Expr::apps(
            ky.term.clone(),
            [
                x.term.clone(),
                next.term.clone(),
                ok.term.clone(),
                err.term.clone(),
            ],
        ),
    );
    let no_cps = lams(
        &[next.clone(), error.clone()],
        Expr::apps(
            kn.term.clone(),
            [
                error.term.clone(),
                next.term.clone(),
                ok.term.clone(),
                err.term.clone(),
            ],
        ),
    );
    let converted = |computation: Expr| {
        to_cps(
            &s.term,
            &e.term,
            &a.term,
            &r.term,
            computation,
            state.term.clone(),
            yes_cps.clone(),
            no_cps.clone(),
        )
    };
    let handled = |computation: Expr| {
        to_cps(
            &s.term,
            &ferr.term,
            &b.term,
            &r.term,
            handle(
                &s.term,
                &e.term,
                &a.term,
                &ferr.term,
                &b.term,
                computation,
                yes.term.clone(),
                no.term.clone(),
            ),
            state.term.clone(),
            ok.term.clone(),
            err.term.clone(),
        )
    };
    let start = Expr::apps(
        f.term.clone(),
        [state.term.clone(), yes_cps.clone(), no_cps.clone()],
    );
    let middle = converted(m.term.clone());
    let finish = handled(m.term.clone());
    let first = Expr::apps(
        hm.term.clone(),
        [state.term.clone(), yes_cps.clone(), no_cps.clone()],
    );
    let ignored = sc.local(s.term.clone());
    let second = prove_result_cases(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        Expr::app(m.term.clone(), state.term.clone()),
        |observed| {
            let computation = ignored.lam(observed);
            eq(
                &r.term,
                converted(computation.clone()),
                handled(computation),
            )
        },
        |next, error| {
            Expr::apps(
                hn.term.clone(),
                [error, next, ok.term.clone(), err.term.clone()],
            )
        },
        |next, value| {
            Expr::apps(
                hy.term.clone(),
                [value, next, ok.term.clone(), err.term.clone()],
            )
        },
    );
    let proof = trans(
        &r.term,
        start.clone(),
        middle,
        finish.clone(),
        first,
        second,
    );
    let statement = eq(&r.term, start, finish);
    add(
        env,
        CPS_IMAGE_HANDLE,
        &[
            s, e, a, ferr, b, r, m, f, yes, no, ky, kn, hm, hy, hn, state, ok, err,
        ],
        statement,
        proof,
        true,
    )
}

#[cfg(test)]
mod hostile_tests {
    use super::*;
    fn z(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(
            c(name).instantiate_level_params(&[(Name::from_string("u"), Level::zero())]),
            args,
        )
    }
    fn product(a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Prod"),
                vec![Level::zero(), Level::zero()],
            ),
            [a, b],
        )
    }
    fn pair0(a: Expr, b: Expr, x: Expr, y: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Prod.mk"),
                vec![Level::zero(), Level::zero()],
            ),
            [a, b, x, y],
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
    fn cps_handle_image_preserves_heterogeneous_error_and_actual_post_state() {
        let mut env = build_environment().unwrap();
        env.init_nat().unwrap();
        install_handle_into(&mut env).unwrap();
        let nat = Expr::const_str("Nat");
        let boolean = Expr::const_str("Bool");
        let false_ = Expr::const_str("Bool.false");
        let true_ = Expr::const_str("Bool.true");
        let mut sc = Scope::default();
        let state = sc.local(nat.clone());
        let value = sc.local(nat.clone());
        let failure = sc.local(boolean.clone());
        let input_outcome = z("Except", [boolean.clone(), nat.clone()]);
        let m = state.lam(pair0(
            nat.clone(),
            input_outcome,
            Expr::nat_lit(1),
            z(
                "Except.error",
                [boolean.clone(), nat.clone(), false_.clone()],
            ),
        ));
        let yes = value.lam(z(
            PURE,
            [nat.clone(), nat.clone(), boolean.clone(), true_.clone()],
        ));
        let no = failure.lam(z(
            FAIL,
            [nat.clone(), nat.clone(), boolean.clone(), Expr::nat_lit(99)],
        ));
        let computation = z(
            HANDLE,
            [
                nat.clone(),
                boolean.clone(),
                nat.clone(),
                nat.clone(),
                boolean.clone(),
                m.clone(),
                yes,
                no,
            ],
        );
        let actual = Expr::app(computation, Expr::nat_lit(0));
        let out = z("Except", [nat.clone(), boolean.clone()]);
        let result_type = product(nat.clone(), out.clone());
        let expected = |post, error| {
            pair0(
                nat.clone(),
                out.clone(),
                Expr::nat_lit(post),
                z(
                    "Except.error",
                    [nat.clone(), boolean.clone(), Expr::nat_lit(error)],
                ),
            )
        };
        assert!(check(
            &env,
            result_type.clone(),
            actual.clone(),
            expected(1, 99)
        ));
        assert!(!check(
            &env,
            result_type.clone(),
            actual.clone(),
            expected(0, 99)
        ));
        assert!(!check(&env, result_type, actual, expected(1, 98)));
        // An arbitrary fixed-answer provider that discards both callbacks is
        // not silently admitted to the first-order image.
        let ok = sc.local(continuation(&nat, &nat, &boolean));
        let err = sc.local(continuation(&nat, &boolean, &boolean));
        let discarded = lams(&[state.clone(), ok, err], false_);
        let a = sc.local(nat.clone());
        let e = sc.local(boolean.clone());
        let success = lams(&[state.clone(), a], true_.clone());
        let error = lams(&[state, e], true_);
        let left = Expr::apps(
            discarded,
            [Expr::nat_lit(0), success.clone(), error.clone()],
        );
        let right = z(
            TO_CPS,
            [
                nat.clone(),
                boolean.clone(),
                nat,
                boolean.clone(),
                m,
                Expr::nat_lit(0),
                success,
                error,
            ],
        );
        assert!(!check(&env, boolean, left, right));
    }
    #[test]
    fn cps_handle_image_last_name_collision_mutates_nothing() {
        let mut env = Environment::default();
        env.add_decl(Declaration::Definition {
            name: Name::from_string(CPS_IMAGE_HANDLE),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            is_reducible: true,
        })
        .unwrap();
        let generation = env.generation();
        let count = env.num_constants();
        assert_eq!(
            install_handle_into(&mut env).unwrap_err().declaration,
            CPS_IMAGE_HANDLE
        );
        assert_eq!(env.generation(), generation);
        assert_eq!(env.num_constants(), count);
    }
}
