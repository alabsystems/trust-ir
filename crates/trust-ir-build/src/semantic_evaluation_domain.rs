// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Finite, first-order domain traversal. The supplied list still requires an
//! endpoint-derived membership/coverage contract, and a physical provider still
//! owes fidelity and readiness. No CPS callback is silently assumed total.
use super::*;

#[path = "semantic_evaluation_cursor.rs"]
mod cursor;
pub use cursor::{
    DOMAIN_AT, DOMAIN_AT_COVER, DOMAIN_AT_END, DOMAIN_AT_MEMBERS, DOMAIN_AT_SOUND,
    install_indexed_domain_into,
};

#[path = "semantic_evaluation_domain_tail.rs"]
mod tail;
pub use tail::{
    DOMAIN_TAIL_COMPLETE, DOMAIN_TAIL_FOLD, DOMAIN_TAIL_STEP, install_tail_domain_into,
};

#[path = "semantic_evaluation_domain_enumeration.rs"]
mod enumeration;
pub use enumeration::{
    DOMAIN_ENUMERATE, DOMAIN_ENUMERATE_AT, DOMAIN_ENUMERATE_END, DOMAIN_ENUMERATE_LENGTH,
    DOMAIN_ENUMERATE_NONE, DOMAIN_ENUMERATE_SOME, install_enumerated_domain_into,
};

pub const DOMAIN_LENGTH: &str = "TrustIR.Eval.Domain.length";
pub const DOMAIN_STEP: &str = "TrustIR.Eval.Domain.step";
pub const DOMAIN_FOLD: &str = "TrustIR.Eval.Domain.fold";
pub const DOMAIN_COMPLETE: &str = "TrustIR.Eval.Domain.complete";

fn list(a: &Expr) -> Expr {
    Expr::app(c("List"), a.clone())
}
fn successor(n: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), n)
}
fn list_rec(a: &Expr, motive: Expr, zero: Expr, next: Expr, xs: Expr, level: Level) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.rec"), vec![level, u()]),
        [a.clone(), motive, zero, next, xs],
    )
}
fn length(a: &Expr, xs: Expr) -> Expr {
    Expr::apps(c(DOMAIN_LENGTH), [a.clone(), xs])
}
fn walk(name: &str, s: &Expr, d: &Expr, a: &Expr, body: Expr, finish: Expr, input: Expr) -> Expr {
    Expr::apps(
        c(name),
        [s.clone(), d.clone(), a.clone(), body, finish, input],
    )
}

fn install_length(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [a] = sc.types();
    let xs = sc.local(list(&a.term));
    let ignored = sc.local(list(&a.term));
    let head = sc.local(a.term.clone());
    let tail = sc.local(list(&a.term));
    let previous = sc.local(Expr::const_str("Nat"));
    let term = list_rec(
        &a.term,
        ignored.lam(Expr::const_str("Nat")),
        Expr::nat_lit(0),
        lams(&[head, tail, previous.clone()], successor(previous.term)),
        xs.term.clone(),
        Level::succ(Level::zero()),
    );
    add(
        env,
        DOMAIN_LENGTH,
        &[a, xs],
        Expr::const_str("Nat"),
        term,
        false,
    )
}

/// Recursion on the source list is the specification, not an SSA unroll. Early
/// completion (including an error observation in D) skips all remaining rows.
fn install_fold(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, d, a] = sc.types();
    let pulse = sum(&s.term, &d.term);
    let body = sc.local(Expr::arrow(
        a.term.clone(),
        Expr::arrow(s.term.clone(), pulse.clone()),
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
        &[head.clone(), tail, previous.clone(), state.clone()],
        cases(
            &s.term,
            &d.term,
            p.lam(d.term.clone()),
            previous.term,
            done.lam(done.term.clone()),
            Expr::apps(body.term.clone(), [head.term, state.term]),
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
        DOMAIN_FOLD,
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
        Expr::arrow(s.term.clone(), sum(&s.term, &d.term)),
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
                pair(&s.term, &domain, updated.term.clone(), tail.term),
            )),
            done.lam(side(&cursor, &d.term, true, done.term.clone())),
            Expr::apps(body.term.clone(), [head.term, state.term]),
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
        DOMAIN_STEP,
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
        Expr::arrow(s.term.clone(), row_pulse.clone()),
    ));
    let finish = sc.local(Expr::arrow(s.term.clone(), d.term.clone()));
    let xs = sc.local(domain.clone());
    let state = sc.local(s.term.clone());
    let step = Expr::apps(
        c(DOMAIN_STEP),
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
                DOMAIN_FOLD,
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
        Expr::apps(body.term.clone(), [head.term.clone(), current.term.clone()]),
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
        DOMAIN_COMPLETE,
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

/// Owns both the loop-prefix vocabulary and this finite-domain extension.
/// Call on an environment without either inventory; collisions fail closed.
pub fn install_domain_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in [DOMAIN_LENGTH, DOMAIN_STEP, DOMAIN_FOLD, DOMAIN_COMPLETE] {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    install_loop_into(env)?;
    env.init_prod().map_err(|e| error(DOMAIN_STEP, e))?;
    env.init_list().map_err(|e| error(DOMAIN_STEP, e))?;
    install_length(env)?;
    install_fold(env)?;
    install_step(env)?;
    install_complete(env)?;
    recheck_theorem(env, DOMAIN_COMPLETE)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn finite_domain_symbolic_completion_requires_no_fixed_unroll_or_witness_axiom() {
        let mut env = Environment::default();
        install_domain_into(&mut env).unwrap();
        recheck_theorem(&env, DOMAIN_COMPLETE).unwrap();
        assert!(install_domain_into(&mut env).is_err());
    }
}
