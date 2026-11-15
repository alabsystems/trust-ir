// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Tail-aware finite traversal. Error/done values may retain the exact remaining
//! cursor and cleanup context; no cursor state is erased to apply completion.
use super::*;
pub const DOMAIN_TAIL_STEP: &str = "TrustIR.Eval.Domain.Tail.step";
pub const DOMAIN_TAIL_FOLD: &str = "TrustIR.Eval.Domain.Tail.fold";
pub const DOMAIN_TAIL_COMPLETE: &str = "TrustIR.Eval.Domain.Tail.complete";

/// Extend an already checked domain vocabulary. Collisions preflight before
/// mutation; later errors require discarding the partially extended environment.
pub fn install_tail_domain_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in [DOMAIN_TAIL_STEP, DOMAIN_TAIL_FOLD, DOMAIN_TAIL_COMPLETE] {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    recheck_theorem(env, DOMAIN_COMPLETE)?;
    install_fold(env)?;
    install_step(env)?;
    install_complete(env)?;
    recheck_theorem(env, DOMAIN_TAIL_COMPLETE)
}

/// Recursion on the source list is the specification, not an SSA unroll. Early
/// completion (including an error observation in D) skips all remaining rows.
fn install_fold(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, d, a] = sc.types();
    let pulse = sum(&s.term, &d.term);
    let body = sc.local(Expr::arrow(
        a.term.clone(),
        Expr::arrow(list(&a.term), Expr::arrow(s.term.clone(), pulse.clone())),
    ));
    let finish = sc.local(Expr::arrow(s.term.clone(), d.term.clone()));
    let xs = sc.local(list(&a.term));
    let ignored = sc.local(list(&a.term));
    let head = sc.local(a.term.clone());
    let tail = sc.local(list(&a.term));
    let previous = sc.local(finish.ty.clone());
    let state = sc.local(s.term.clone());
    let p = sc.local(pulse);
    let done = sc.local(d.term.clone());
    let next = lams(
        &[head.clone(), tail.clone(), previous.clone(), state.clone()],
        cases(
            &s.term,
            &d.term,
            p.lam(d.term.clone()),
            previous.term,
            done.lam(done.term.clone()),
            Expr::apps(
                body.term.clone(),
                [head.term, tail.term.clone(), state.term],
            ),
            false,
        ),
    );
    let term = list_rec(
        &a.term,
        ignored.lam(finish.ty.clone()),
        finish.term.clone(),
        next,
        xs.term.clone(),
        Level::succ(u()),
    );
    add(
        env,
        DOMAIN_TAIL_FOLD,
        &[s, d.clone(), a, body, finish, xs],
        Expr::arrow(state.ty, d.term),
        term,
        false,
    )
}

fn install_step(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, d, a] = sc.types();
    let domain = list(&a.term);
    let cursor = prod(&s.term, &domain);
    let pulse = sum(&cursor, &d.term);
    let body = sc.local(Expr::arrow(
        a.term.clone(),
        Expr::arrow(
            list(&a.term),
            Expr::arrow(s.term.clone(), sum(&s.term, &d.term)),
        ),
    ));
    let finish = sc.local(Expr::arrow(s.term.clone(), d.term.clone()));
    let input = sc.local(cursor.clone());
    let state = sc.local(s.term.clone());
    let ignored = sc.local(domain.clone());
    let zero = state.lam(side(
        &cursor,
        &d.term,
        true,
        Expr::app(finish.term.clone(), state.term.clone()),
    ));
    let head = sc.local(a.term.clone());
    let tail = sc.local(domain.clone());
    let previous = sc.local(Expr::arrow(s.term.clone(), pulse.clone()));
    let source_pulse = sc.local(sum(&s.term, &d.term));
    let updated = sc.local(s.term.clone());
    let done = sc.local(d.term.clone());
    let next = lams(
        &[head.clone(), tail.clone(), previous, state.clone()],
        cases(
            &s.term,
            &d.term,
            source_pulse.lam(pulse.clone()),
            updated.lam(side(
                &cursor,
                &d.term,
                false,
                pair(&s.term, &domain, updated.term.clone(), tail.term.clone()),
            )),
            done.lam(side(&cursor, &d.term, true, done.term.clone())),
            Expr::apps(
                body.term.clone(),
                [head.term, tail.term.clone(), state.term],
            ),
            false,
        ),
    );
    let term = Expr::app(
        list_rec(
            &a.term,
            ignored.lam(Expr::arrow(s.term.clone(), pulse.clone())),
            zero,
            next,
            projection(1, &s.term, &domain, input.term.clone()),
            Level::succ(u()),
        ),
        projection(0, &s.term, &domain, input.term.clone()),
    );
    add(
        env,
        DOMAIN_TAIL_STEP,
        &[s, d, a, body, finish, input],
        pulse,
        term,
        false,
    )
}

fn install_complete(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, d, a] = sc.types();
    let domain = list(&a.term);
    let cursor = prod(&s.term, &domain);
    let pulse = sum(&cursor, &d.term);
    let row_pulse = sum(&s.term, &d.term);
    let body = sc.local(Expr::arrow(
        a.term.clone(),
        Expr::arrow(
            list(&a.term),
            Expr::arrow(s.term.clone(), row_pulse.clone()),
        ),
    ));
    let finish = sc.local(Expr::arrow(s.term.clone(), d.term.clone()));
    let xs = sc.local(domain.clone());
    let state = sc.local(s.term.clone());
    let step = Expr::apps(
        c(DOMAIN_TAIL_STEP),
        [
            s.term.clone(),
            d.term.clone(),
            a.term.clone(),
            body.term.clone(),
            finish.term.clone(),
        ],
    );
    let fold = |xs: Expr, state: Expr| {
        Expr::app(
            walk(
                DOMAIN_TAIL_FOLD,
                &s.term,
                &d.term,
                &a.term,
                body.term.clone(),
                finish.term.clone(),
                xs,
            ),
            state,
        )
    };
    let statement = |xs: Expr, state: Expr| {
        eq(
            &pulse,
            prefix(
                &cursor,
                &d.term,
                step.clone(),
                successor(length(&a.term, xs.clone())),
                pair(&s.term, &domain, state.clone(), xs.clone()),
            ),
            side(&cursor, &d.term, true, fold(xs, state)),
        )
    };
    let initial = sc.local(s.term.clone());
    let zero = initial.lam(refl(
        &pulse,
        side(
            &cursor,
            &d.term,
            true,
            Expr::app(finish.term.clone(), initial.term.clone()),
        ),
    ));
    let head = sc.local(a.term.clone());
    let tail = sc.local(domain.clone());
    let q = sc.local(s.term.clone());
    let ih = sc.local(q.pi(statement(tail.term.clone(), q.term.clone())));
    let current = sc.local(s.term.clone());
    let item = sc.local(row_pulse.clone());
    let updated = sc.local(s.term.clone());
    let done = sc.local(d.term.clone());
    let next_cursor = sc.local(cursor.clone());
    let cursor_pulse = sc.local(pulse.clone());
    let source_map = |value: Expr| {
        let step_pulse = cases(
            &s.term,
            &d.term,
            item.lam(pulse.clone()),
            updated.lam(side(
                &cursor,
                &d.term,
                false,
                pair(&s.term, &domain, updated.term.clone(), tail.term.clone()),
            )),
            done.lam(side(&cursor, &d.term, true, done.term.clone())),
            value,
            false,
        );
        // Retain the actual nested eliminators from prefix(step ...).
        // Fusing them for an unknown provider pulse would need a theorem.
        cases(
            &cursor,
            &d.term,
            cursor_pulse.lam(pulse.clone()),
            next_cursor.lam(prefix(
                &cursor,
                &d.term,
                step.clone(),
                successor(length(&a.term, tail.term.clone())),
                next_cursor.term.clone(),
            )),
            done.lam(side(&cursor, &d.term, true, done.term.clone())),
            step_pulse,
            false,
        )
    };
    let target_map = |value: Expr| {
        cases(
            &s.term,
            &d.term,
            item.lam(d.term.clone()),
            updated.lam(fold(tail.term.clone(), updated.term.clone())),
            done.lam(done.term.clone()),
            value,
            false,
        )
    };
    let motive = item.lam(eq(
        &pulse,
        source_map(item.term.clone()),
        side(&cursor, &d.term, true, target_map(item.term.clone())),
    ));
    let induction = cases(
        &s.term,
        &d.term,
        motive,
        updated.lam(Expr::app(ih.term.clone(), updated.term.clone())),
        done.lam(refl(
            &pulse,
            side(&cursor, &d.term, true, done.term.clone()),
        )),
        Expr::apps(
            body.term.clone(),
            [head.term.clone(), tail.term.clone(), current.term.clone()],
        ),
        true,
    );
    let next = lams(&[head, tail, ih, current], induction);
    let index = sc.local(domain.clone());
    let input = sc.local(s.term.clone());
    let motive = index.lam(input.pi(statement(index.term.clone(), input.term.clone())));
    let proof = Expr::app(
        list_rec(&a.term, motive, zero, next, xs.term.clone(), Level::zero()),
        state.term.clone(),
    );
    add(
        env,
        DOMAIN_TAIL_COMPLETE,
        &[
            s.clone(),
            d.clone(),
            a.clone(),
            body.clone(),
            finish.clone(),
            xs.clone(),
            state.clone(),
        ],
        statement(xs.term, state.term),
        proof,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn finite_tail_domain_completion_retains_remaining_cursor_and_early_errors() {
        let mut env = Environment::default();
        install_domain_into(&mut env).unwrap();
        install_tail_domain_into(&mut env).unwrap();
        recheck_theorem(&env, DOMAIN_TAIL_COMPLETE).unwrap();
        assert!(install_tail_domain_into(&mut env).is_err());
    }
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
    fn two(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string(name), vec![Level::zero(), Level::zero()]),
            args,
        )
    }
    fn eq_check(env: &Environment, ty: Expr, left: Expr, right: Expr) -> bool {
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
    fn finite_tail_domain_early_error_retains_poststate_and_actual_remaining_tail() {
        let mut env = Environment::default();
        install_domain_into(&mut env).unwrap();
        install_tail_domain_into(&mut env).unwrap();
        let nat = Expr::const_str("Nat");
        let rows_type = z("List", [nat.clone()]);
        let nil = z("List.nil", [nat.clone()]);
        let tail = z("List.cons", [nat.clone(), Expr::nat_lit(1), nil.clone()]);
        let rows = z("List.cons", [nat.clone(), Expr::nat_lit(0), tail.clone()]);
        let done = two("Prod", [nat.clone(), rows_type.clone()]);
        let cursor = two("Prod", [nat.clone(), rows_type.clone()]);
        let pulse = two("Sum", [cursor.clone(), done.clone()]);
        let pair =
            |state: Expr, rows: Expr| two("Prod.mk", [nat.clone(), rows_type.clone(), state, rows]);
        let mut sc = Scope::default();
        let head = sc.local(nat.clone());
        let rest = sc.local(rows_type.clone());
        let state = sc.local(nat.clone());
        let body = lams(
            &[head, rest.clone(), state.clone()],
            two(
                "Sum.inr",
                [
                    nat.clone(),
                    done.clone(),
                    pair(
                        Expr::app(Expr::const_str("Nat.succ"), state.term.clone()),
                        rest.term.clone(),
                    ),
                ],
            ),
        );
        let finish = state.lam(pair(state.term.clone(), nil));
        let step = z(
            DOMAIN_TAIL_STEP,
            [nat.clone(), done.clone(), nat.clone(), body, finish],
        );
        let fuel = Expr::app(
            Expr::const_str("Nat.succ"),
            z(DOMAIN_LENGTH, [nat.clone(), rows.clone()]),
        );
        let actual = z(
            LOOP_PREFIX,
            [
                cursor.clone(),
                done.clone(),
                step,
                fuel,
                pair(Expr::nat_lit(7), rows.clone()),
            ],
        );
        let result = |s, rows| {
            two(
                "Sum.inr",
                [cursor.clone(), done.clone(), pair(Expr::nat_lit(s), rows)],
            )
        };
        assert!(eq_check(
            &env,
            pulse.clone(),
            actual.clone(),
            result(8, tail.clone())
        ));
        assert!(!eq_check(
            &env,
            pulse.clone(),
            actual.clone(),
            result(7, tail)
        ));
        assert!(!eq_check(&env, pulse, actual, result(8, rows)));
    }
}
