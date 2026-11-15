// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Prefix transport across explicit source/target state and observation maps.
//! The endpoint-derived commuting-step proof remains an explicit premise.
use super::*;
pub const LOOP_MAP_PULSE: &str = "TrustIR.Eval.Loop.map_pulse";
pub const LOOP_MAP_PREFIX: &str = "TrustIR.Eval.Loop.map_prefix";
pub const LOOP_MAP_COMPLETE: &str = "TrustIR.Eval.Loop.map_complete";

pub fn install_loop_map_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in [LOOP_MAP_PULSE, LOOP_MAP_PREFIX, LOOP_MAP_COMPLETE] {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    recheck_theorem(env, LOOP_PREFIX_CONGR)?;
    definition(env)?;
    naturality(env)?;
    completion(env)?;
    recheck_theorem(env, LOOP_MAP_PREFIX)?;
    recheck_theorem(env, LOOP_MAP_COMPLETE)
}
fn mapped(
    s: &Expr,
    t: &Expr,
    d: &Expr,
    e: &Expr,
    encode: Expr,
    observe: Expr,
    pulse: Expr,
) -> Expr {
    Expr::apps(
        c(LOOP_MAP_PULSE),
        [
            s.clone(),
            t.clone(),
            d.clone(),
            e.clone(),
            encode,
            observe,
            pulse,
        ],
    )
}
fn definition(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, t, d, e] = sc.types();
    let encode = sc.local(Expr::arrow(s.term.clone(), t.term.clone()));
    let observe = sc.local(Expr::arrow(d.term.clone(), e.term.clone()));
    let p = sc.local(sum(&s.term, &d.term));
    let state = sc.local(s.term.clone());
    let done = sc.local(d.term.clone());
    let value = cases(
        &s.term,
        &d.term,
        p.lam(sum(&t.term, &e.term)),
        state.lam(side(
            &t.term,
            &e.term,
            false,
            Expr::app(encode.term.clone(), state.term.clone()),
        )),
        done.lam(side(
            &t.term,
            &e.term,
            true,
            Expr::app(observe.term.clone(), done.term.clone()),
        )),
        p.term.clone(),
        false,
    );
    add(
        env,
        LOOP_MAP_PULSE,
        &[s, t.clone(), d, e.clone(), encode, observe, p],
        sum(&t.term, &e.term),
        value,
        false,
    )
}
fn naturality(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, t, d, e] = sc.types();
    let source_pulse = sum(&s.term, &d.term);
    let target_pulse = sum(&t.term, &e.term);
    let encode = sc.local(Expr::arrow(s.term.clone(), t.term.clone()));
    let observe = sc.local(Expr::arrow(d.term.clone(), e.term.clone()));
    let f = sc.local(Expr::arrow(s.term.clone(), source_pulse.clone()));
    let g = sc.local(Expr::arrow(t.term.clone(), target_pulse.clone()));
    let map = |p| {
        mapped(
            &s.term,
            &t.term,
            &d.term,
            &e.term,
            encode.term.clone(),
            observe.term.clone(),
            p,
        )
    };
    let state = sc.local(s.term.clone());
    let step = sc.local(state.pi(eq(
        &target_pulse,
        map(Expr::app(f.term.clone(), state.term.clone())),
        Expr::app(
            g.term.clone(),
            Expr::app(encode.term.clone(), state.term.clone()),
        ),
    )));
    let n = sc.local(Expr::const_str("Nat"));
    let statement = |n: Expr, state: Expr| {
        eq(
            &target_pulse,
            map(prefix(
                &s.term,
                &d.term,
                f.term.clone(),
                n.clone(),
                state.clone(),
            )),
            prefix(
                &t.term,
                &e.term,
                g.term.clone(),
                n,
                Expr::app(encode.term.clone(), state),
            ),
        )
    };
    let zero = state.lam(refl(
        &target_pulse,
        side(
            &t.term,
            &e.term,
            false,
            Expr::app(encode.term.clone(), state.term.clone()),
        ),
    ));
    let k = sc.local(n.ty.clone());
    let next_state = sc.local(s.term.clone());
    let ih = sc.local(next_state.pi(statement(k.term.clone(), next_state.term.clone())));
    let source_done = sc.local(d.term.clone());
    let target_state = sc.local(t.term.clone());
    let target_done = sc.local(e.term.clone());
    let source_input = sc.local(source_pulse.clone());
    let target_input = sc.local(target_pulse.clone());
    let source_resume = |p| {
        cases(
            &s.term,
            &d.term,
            source_input.lam(source_pulse.clone()),
            next_state.lam(prefix(
                &s.term,
                &d.term,
                f.term.clone(),
                k.term.clone(),
                next_state.term.clone(),
            )),
            source_done.lam(side(&s.term, &d.term, true, source_done.term.clone())),
            p,
            false,
        )
    };
    let target_resume = |p| {
        cases(
            &t.term,
            &e.term,
            target_input.lam(target_pulse.clone()),
            target_state.lam(prefix(
                &t.term,
                &e.term,
                g.term.clone(),
                k.term.clone(),
                target_state.term.clone(),
            )),
            target_done.lam(side(&t.term, &e.term, true, target_done.term.clone())),
            p,
            false,
        )
    };
    let source_observed = Expr::app(f.term.clone(), state.term.clone());
    let first = cases(
        &s.term,
        &d.term,
        source_input.lam(eq(
            &target_pulse,
            map(source_resume(source_input.term.clone())),
            target_resume(map(source_input.term.clone())),
        )),
        next_state.lam(Expr::app(ih.term.clone(), next_state.term.clone())),
        source_done.lam(refl(
            &target_pulse,
            side(
                &t.term,
                &e.term,
                true,
                Expr::app(observe.term.clone(), source_done.term.clone()),
            ),
        )),
        source_observed.clone(),
        true,
    );
    let target_observed = Expr::app(
        g.term.clone(),
        Expr::app(encode.term.clone(), state.term.clone()),
    );
    let second = congr_arg(
        &target_pulse,
        &target_pulse,
        map(source_observed.clone()),
        target_observed.clone(),
        target_input.lam(target_resume(target_input.term.clone())),
        Expr::app(step.term.clone(), state.term.clone()),
    );
    let proof = trans(
        &target_pulse,
        map(source_resume(source_observed.clone())),
        target_resume(map(source_observed)),
        target_resume(target_observed),
        first,
        second,
    );
    let next = lams(&[k, ih, state.clone()], proof);
    let index = sc.local(n.ty.clone());
    let input = sc.local(s.term.clone());
    let induction = Expr::app(
        Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [
                index.lam(input.pi(statement(index.term.clone(), input.term.clone()))),
                zero,
                next,
                n.term.clone(),
            ],
        ),
        state.term.clone(),
    );
    let goal = statement(n.term.clone(), state.term.clone());
    add(
        env,
        LOOP_MAP_PREFIX,
        &[s, t, d, e, encode, observe, f, g, step, n, state],
        goal,
        induction,
        true,
    )
}
fn completion(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, t, d, e] = sc.types();
    let sp = sum(&s.term, &d.term);
    let tp = sum(&t.term, &e.term);
    let encode = sc.local(Expr::arrow(s.term.clone(), t.term.clone()));
    let observe = sc.local(Expr::arrow(d.term.clone(), e.term.clone()));
    let f = sc.local(Expr::arrow(s.term.clone(), sp.clone()));
    let g = sc.local(Expr::arrow(t.term.clone(), tp.clone()));
    let state = sc.local(s.term.clone());
    let map = |p| {
        mapped(
            &s.term,
            &t.term,
            &d.term,
            &e.term,
            encode.term.clone(),
            observe.term.clone(),
            p,
        )
    };
    let step = sc.local(state.pi(eq(
        &tp,
        map(Expr::app(f.term.clone(), state.term.clone())),
        Expr::app(
            g.term.clone(),
            Expr::app(encode.term.clone(), state.term.clone()),
        ),
    )));
    let n = sc.local(Expr::const_str("Nat"));
    let done = sc.local(d.term.clone());
    let source = prefix(
        &s.term,
        &d.term,
        f.term.clone(),
        n.term.clone(),
        state.term.clone(),
    );
    let source_done = side(&s.term, &d.term, true, done.term.clone());
    let h = sc.local(eq(&sp, source.clone(), source_done.clone()));
    let target = prefix(
        &t.term,
        &e.term,
        g.term.clone(),
        n.term.clone(),
        Expr::app(encode.term.clone(), state.term.clone()),
    );
    let result = side(
        &t.term,
        &e.term,
        true,
        Expr::app(observe.term.clone(), done.term.clone()),
    );
    let law = Expr::apps(
        c(LOOP_MAP_PREFIX),
        [
            s.term.clone(),
            t.term.clone(),
            d.term.clone(),
            e.term.clone(),
            encode.term.clone(),
            observe.term.clone(),
            f.term.clone(),
            g.term.clone(),
            step.term.clone(),
            n.term.clone(),
            state.term.clone(),
        ],
    );
    let reversed = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(u())]),
        [tp.clone(), map(source.clone()), target.clone(), law],
    );
    let x = sc.local(sp.clone());
    let mapped_done = congr_arg(
        &sp,
        &tp,
        source.clone(),
        source_done,
        x.lam(map(x.term.clone())),
        h.term.clone(),
    );
    let proof = trans(
        &tp,
        target.clone(),
        map(source),
        result.clone(),
        reversed,
        mapped_done,
    );
    add(
        env,
        LOOP_MAP_COMPLETE,
        &[s, t, d, e, encode, observe, f, g, step, n, state, done, h],
        eq(&tp, target, result),
        proof,
        true,
    )
}

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
    fn reject(env: &Environment, ty: Expr, left: Expr, right: Expr) {
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
        assert!(tc.check_type(&proof, &goal).is_err());
    }
    #[test]
    fn loop_map_prefix_and_explicit_completion_are_kernel_checked() {
        let mut env = Environment::default();
        install_loop_into(&mut env).unwrap();
        install_loop_map_into(&mut env).unwrap();
        recheck_theorem(&env, LOOP_MAP_PREFIX).unwrap();
        recheck_theorem(&env, LOOP_MAP_COMPLETE).unwrap();
        assert!(install_loop_map_into(&mut env).is_err());
    }
    #[test]
    fn loop_map_rejects_stale_embedded_state_and_changed_done_observation() {
        let mut env = Environment::default();
        install_loop_into(&mut env).unwrap();
        install_loop_map_into(&mut env).unwrap();
        env.init_prod().unwrap();
        env.init_bool().unwrap();
        let nat = Expr::const_str("Nat");
        let boolean = Expr::const_str("Bool");
        let target = two("Prod", [nat.clone(), nat.clone()]);
        let pulse = two("Sum", [target.clone(), nat.clone()]);
        let mut sc = Scope::default();
        let n = sc.local(nat.clone());
        let b = sc.local(boolean.clone());
        let pair = |n| {
            two(
                "Prod.mk",
                [
                    nat.clone(),
                    nat.clone(),
                    Expr::nat_lit(n),
                    Expr::nat_lit(99),
                ],
            )
        };
        let encode = n.lam(two(
            "Prod.mk",
            [nat.clone(), nat.clone(), n.term.clone(), Expr::nat_lit(99)],
        ));
        let observe = b.lam(Expr::apps(
            Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                b.lam(nat.clone()),
                Expr::nat_lit(0),
                Expr::nat_lit(1),
                b.term.clone(),
            ],
        ));
        let source_continue = two("Sum.inl", [nat.clone(), boolean.clone(), Expr::nat_lit(1)]);
        let mapped = z(
            LOOP_MAP_PULSE,
            [
                nat.clone(),
                target.clone(),
                boolean.clone(),
                nat.clone(),
                encode.clone(),
                observe.clone(),
                source_continue,
            ],
        );
        let stale = two("Sum.inl", [target.clone(), nat.clone(), pair(0)]);
        reject(&env, pulse.clone(), mapped, stale);
        let source_done = two(
            "Sum.inr",
            [nat.clone(), boolean.clone(), Expr::const_str("Bool.true")],
        );
        let mapped = z(
            LOOP_MAP_PULSE,
            [
                nat.clone(),
                target.clone(),
                boolean,
                nat.clone(),
                encode,
                observe,
                source_done,
            ],
        );
        let changed = two("Sum.inr", [target, nat, Expr::nat_lit(0)]);
        reject(&env, pulse, mapped, changed);
    }
}
