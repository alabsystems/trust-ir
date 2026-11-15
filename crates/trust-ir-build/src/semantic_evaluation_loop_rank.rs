// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Complete a first-order pulse loop from a decreasing natural-number invariant.
//!
//! `Inv n s` is a consumer-owned invariant, not an inferred termination claim.
//! At zero the consumer must prove that the ACTUAL step returns a terminal
//! payload. At a successor, every ACTUAL continuation must establish `Inv n`
//! for its returned state. A terminal payload may include any complete state,
//! success or failure observation. It is never replaced by a Boolean verdict.
//! The theorem uses Nat induction, not a bounded set of concrete executions.
//! It does not authenticate a source/SSA interpretation or a runtime provider.

use super::*;

pub const LOOP_RANK_COMPLETE: &str = "TrustIR.Eval.Loop.rank_complete";

fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn succ(n: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), n)
}
fn exists(d: &Expr, predicate: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Exists"), vec![Level::succ(u())]),
        [d.clone(), predicate],
    )
}
fn witness(d: &Expr, predicate: Expr, value: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Exists.intro"), vec![Level::succ(u())]),
        [d.clone(), predicate, value, proof],
    )
}
fn eliminate(d: &Expr, predicate: Expr, conclusion: Expr, proof: Expr, branch: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Exists.elim"), vec![Level::succ(u())]),
        [d.clone(), predicate, conclusion, proof, branch],
    )
}

/// Install the ranked completion theorem over the existing loop vocabulary.
/// The loop definitions must already have been installed and kernel-checked.
/// A caller still needs a checked zero case, every backedge's decrease, and
/// an invariant at the original entry. No supplied proof is trusted here.
pub fn install_ranked_loop_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    if env
        .get_const(&Name::from_string(LOOP_RANK_COMPLETE))
        .is_some()
    {
        return Err(error(
            LOOP_RANK_COMPLETE,
            "owned declaration already exists",
        ));
    }
    recheck_theorem(env, LOOP_PREFIX_CONGR)?;
    env.init_exists()
        .map_err(|e| error(LOOP_RANK_COMPLETE, e))?;
    completion(env)?;
    recheck_theorem(env, LOOP_RANK_COMPLETE)
}

fn next_map(sc: &mut Scope, s: &Expr, d: &Expr, step: Expr, count: Expr) -> Expr {
    let pulse = sum(s, d);
    let observed = sc.local(pulse.clone());
    let ignored = sc.local(pulse.clone());
    let next = sc.local(s.clone());
    let done = sc.local(d.clone());
    observed.lam(cases(
        s,
        d,
        ignored.lam(pulse),
        next.lam(prefix(s, d, step, count, next.term.clone())),
        done.lam(side(s, d, true, done.term.clone())),
        observed.term.clone(),
        false,
    ))
}

fn completion(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, d] = sc.types();
    let pulse = sum(&s.term, &d.term);
    let step = sc.local(Expr::arrow(s.term.clone(), pulse.clone()));
    let invariant = sc.local(Expr::arrow(
        nat(),
        Expr::arrow(s.term.clone(), Expr::sort(Level::zero())),
    ));
    let inv = |n: Expr, state: Expr| Expr::apps(invariant.term.clone(), [n, state]);
    let terminal_predicate = |sc: &mut Scope, observed: Expr| {
        let done = sc.local(d.term.clone());
        done.lam(eq(
            &pulse,
            observed,
            side(&s.term, &d.term, true, done.term.clone()),
        ))
    };
    let complete = |sc: &mut Scope, n: Expr, state: Expr| {
        exists(
            &d.term,
            terminal_predicate(
                sc,
                prefix(&s.term, &d.term, step.term.clone(), succ(n), state),
            ),
        )
    };

    let zero_state = sc.local(s.term.clone());
    let zero_inv = sc.local(inv(Expr::nat_lit(0), zero_state.term.clone()));
    let zero_case_type = pis(
        &[zero_state.clone(), zero_inv.clone()],
        exists(
            &d.term,
            terminal_predicate(
                &mut sc,
                Expr::app(step.term.clone(), zero_state.term.clone()),
            ),
        ),
    );
    let zero_case = sc.local(zero_case_type);
    let lower = sc.local(nat());
    let current = sc.local(s.term.clone());
    let next = sc.local(s.term.clone());
    let current_inv = sc.local(inv(succ(lower.term.clone()), current.term.clone()));
    let continued = sc.local(eq(
        &pulse,
        Expr::app(step.term.clone(), current.term.clone()),
        side(&s.term, &d.term, false, next.term.clone()),
    ));
    let decreases = sc.local(pis(
        &[
            lower.clone(),
            current.clone(),
            next.clone(),
            current_inv.clone(),
            continued.clone(),
        ],
        inv(lower.term.clone(), next.term.clone()),
    ));
    let n = sc.local(nat());
    let state = sc.local(s.term.clone());
    let entry = sc.local(inv(n.term.clone(), state.term.clone()));

    // Zero: use the actual terminal step witness and retain that exact payload.
    let initial = sc.local(s.term.clone());
    let initial_inv = sc.local(inv(Expr::nat_lit(0), initial.term.clone()));
    let zero_done = sc.local(d.term.clone());
    let actual_zero = Expr::app(step.term.clone(), initial.term.clone());
    let zero_terminal = side(&s.term, &d.term, true, zero_done.term.clone());
    let zero_equality = sc.local(eq(&pulse, actual_zero.clone(), zero_terminal.clone()));
    let zero_result = prefix(
        &s.term,
        &d.term,
        step.term.clone(),
        succ(Expr::nat_lit(0)),
        initial.term.clone(),
    );
    let zero_predicate = terminal_predicate(&mut sc, zero_result);
    let zero_map = next_map(
        &mut sc,
        &s.term,
        &d.term,
        step.term.clone(),
        Expr::nat_lit(0),
    );
    let zero_proof = witness(
        &d.term,
        zero_predicate.clone(),
        zero_done.term.clone(),
        congr_arg(
            &pulse,
            &pulse,
            actual_zero.clone(),
            zero_terminal,
            zero_map,
            zero_equality.term.clone(),
        ),
    );
    let zero = lams(
        &[initial.clone(), initial_inv.clone()],
        eliminate(
            &d.term,
            terminal_predicate(&mut sc, actual_zero),
            exists(&d.term, zero_predicate),
            Expr::apps(zero_case.term.clone(), [initial.term, initial_inv.term]),
            lams(&[zero_done, zero_equality], zero_proof),
        ),
    );

    // Successor: split the actual pulse. Only a continuation consumes rank.
    let k = sc.local(nat());
    let ih_state = sc.local(s.term.clone());
    let ih_inv = sc.local(inv(k.term.clone(), ih_state.term.clone()));
    let ih_type = pis(
        &[ih_state.clone(), ih_inv],
        complete(&mut sc, k.term.clone(), ih_state.term),
    );
    let ih = sc.local(ih_type);
    let here = sc.local(s.term.clone());
    let here_inv = sc.local(inv(succ(k.term.clone()), here.term.clone()));
    let actual = Expr::app(step.term.clone(), here.term.clone());
    let result = prefix(
        &s.term,
        &d.term,
        step.term.clone(),
        succ(succ(k.term.clone())),
        here.term.clone(),
    );
    let result_predicate = terminal_predicate(&mut sc, result.clone());
    let conclusion = exists(&d.term, result_predicate.clone());
    let mapper = next_map(
        &mut sc,
        &s.term,
        &d.term,
        step.term.clone(),
        succ(k.term.clone()),
    );

    let resumed = sc.local(s.term.clone());
    let left = side(&s.term, &d.term, false, resumed.term.clone());
    let left_equality = sc.local(eq(&pulse, actual.clone(), left.clone()));
    let lowered = Expr::apps(
        decreases.term.clone(),
        [
            k.term.clone(),
            here.term.clone(),
            resumed.term.clone(),
            here_inv.term.clone(),
            left_equality.term.clone(),
        ],
    );
    let tail = prefix(
        &s.term,
        &d.term,
        step.term.clone(),
        succ(k.term.clone()),
        resumed.term.clone(),
    );
    let tail_predicate = terminal_predicate(&mut sc, tail.clone());
    let returned = sc.local(d.term.clone());
    let returned_terminal = side(&s.term, &d.term, true, returned.term.clone());
    let tail_equality = sc.local(eq(&pulse, tail.clone(), returned_terminal.clone()));
    let left_proof = witness(
        &d.term,
        result_predicate.clone(),
        returned.term.clone(),
        trans(
            &pulse,
            result.clone(),
            tail,
            returned_terminal,
            congr_arg(
                &pulse,
                &pulse,
                actual.clone(),
                left,
                mapper.clone(),
                left_equality.term.clone(),
            ),
            tail_equality.term.clone(),
        ),
    );
    let left_branch = lams(
        &[resumed.clone(), left_equality],
        eliminate(
            &d.term,
            tail_predicate,
            conclusion.clone(),
            Expr::apps(ih.term.clone(), [resumed.term, lowered]),
            lams(&[returned, tail_equality], left_proof),
        ),
    );
    let returned = sc.local(d.term.clone());
    let right = side(&s.term, &d.term, true, returned.term.clone());
    let right_equality = sc.local(eq(&pulse, actual.clone(), right.clone()));
    let right_branch = lams(
        &[returned.clone(), right_equality.clone()],
        witness(
            &d.term,
            result_predicate,
            returned.term,
            congr_arg(
                &pulse,
                &pulse,
                actual.clone(),
                right,
                mapper,
                right_equality.term,
            ),
        ),
    );
    let observed = sc.local(pulse.clone());
    let equal_observed = sc.local(eq(&pulse, actual.clone(), observed.term.clone()));
    let branch = cases(
        &s.term,
        &d.term,
        observed.lam(equal_observed.pi(conclusion)),
        left_branch,
        right_branch,
        actual.clone(),
        true,
    );
    let successor = lams(
        &[k.clone(), ih, here, here_inv],
        Expr::app(branch, refl(&pulse, actual)),
    );

    let count = sc.local(nat());
    let item = sc.local(s.term.clone());
    let item_inv = sc.local(inv(count.term.clone(), item.term.clone()));
    let motive = count.lam(pis(
        &[item.clone(), item_inv],
        complete(&mut sc, count.term.clone(), item.term),
    ));
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [
            motive,
            zero,
            successor,
            n.term.clone(),
            state.term.clone(),
            entry.term.clone(),
        ],
    );
    let statement = complete(&mut sc, n.term.clone(), state.term.clone());
    add(
        env,
        LOOP_RANK_COMPLETE,
        &[s, d, step, invariant, zero_case, decreases, n, state, entry],
        statement,
        proof,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn decreasing_rank_completes_by_kernel_checked_induction() {
        let mut env = Environment::default();
        install_loop_into(&mut env).unwrap();
        install_ranked_loop_into(&mut env).unwrap();
        recheck_theorem(&env, LOOP_RANK_COMPLETE).unwrap();
        assert!(install_ranked_loop_into(&mut env).is_err());
    }
}
