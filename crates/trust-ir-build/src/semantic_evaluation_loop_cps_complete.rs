// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Transfer a proved terminal pulse to the actual CPS prefix's exact answer.
//! Both the all-resume observation law and the terminal-prefix proof remain
//! mandatory. This supplies no termination, source or provider assumption.
use super::*;

pub const LOOP_CPS_COMPLETE_TRANSFER: &str = "TrustIR.Eval.Loop.cps_complete_transfer";

/// Install after `install_cps_observation_into`. The theorem retains the full
/// terminal payload and holds for every residual continuation. A consumer may
/// obtain its terminal premise from `LOOP_RANK_COMPLETE`, but a finite prefix
/// alone is insufficient. Collisions refuse before mutation; discard the
/// environment after any later error, as with the other additive installers.
pub fn install_cps_completion_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    if env
        .get_const(&Name::from_string(LOOP_CPS_COMPLETE_TRANSFER))
        .is_some()
    {
        return Err(error(
            LOOP_CPS_COMPLETE_TRANSFER,
            "owned declaration already exists",
        ));
    }
    recheck_theorem(env, LOOP_CPS_PREFIX_OBSERVATION)?;
    completion(env)?;
    recheck_theorem(env, LOOP_CPS_COMPLETE_TRANSFER)
}

fn completion(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, d] = sc.types();
    let a = sc.local(Expr::sort(Level::succ(u())));
    let pulse_ty = sum(&s.term, &d.term);
    let continuation_ty = Expr::arrow(s.term.clone(), a.term.clone());
    let actual = sc.local(Expr::arrow(
        continuation_ty.clone(),
        continuation_ty.clone(),
    ));
    let pulse = sc.local(Expr::arrow(s.term.clone(), pulse_ty.clone()));
    let finish = sc.local(Expr::arrow(d.term.clone(), a.term.clone()));
    let continued = sc.local(continuation_ty.clone());
    let state = sc.local(s.term.clone());
    let ignored = sc.local(pulse_ty.clone());
    let observed = sc.local(pis(
        &[continued.clone(), state.clone()],
        eq(
            &a.term,
            Expr::apps(
                actual.term.clone(),
                [continued.term.clone(), state.term.clone()],
            ),
            cases(
                &s.term,
                &d.term,
                ignored.lam(a.term.clone()),
                continued.term,
                finish.term.clone(),
                Expr::app(pulse.term.clone(), state.term),
                false,
            ),
        ),
    ));
    let residual = sc.local(continuation_ty);
    let count = sc.local(Expr::const_str("Nat"));
    let initial = sc.local(s.term.clone());
    let result = sc.local(d.term.clone());
    let prefix = prefix(
        &s.term,
        &d.term,
        pulse.term.clone(),
        count.term.clone(),
        initial.term.clone(),
    );
    let done = side(&s.term, &d.term, true, result.term.clone());
    let terminal = sc.local(eq(&pulse_ty, prefix.clone(), done.clone()));
    let selected = sc.local(pulse_ty.clone());
    let ignored = sc.local(pulse_ty.clone());
    let mapper = selected.lam(cases(
        &s.term,
        &d.term,
        ignored.lam(a.term.clone()),
        residual.term.clone(),
        finish.term.clone(),
        selected.term.clone(),
        false,
    ));
    let actual_prefix = Expr::apps(
        c(LOOP_CPS_PREFIX),
        [
            s.term.clone(),
            a.term.clone(),
            actual.term.clone(),
            residual.term.clone(),
            count.term.clone(),
            initial.term.clone(),
        ],
    );
    let observation = Expr::apps(
        c(LOOP_CPS_PREFIX_OBSERVATION),
        [
            s.term.clone(),
            d.term.clone(),
            a.term.clone(),
            actual.term.clone(),
            pulse.term.clone(),
            finish.term.clone(),
            observed.term.clone(),
            residual.term.clone(),
            count.term.clone(),
            initial.term.clone(),
        ],
    );
    let answer = Expr::app(finish.term.clone(), result.term.clone());
    let proof = trans(
        &a.term,
        actual_prefix.clone(),
        Expr::app(mapper.clone(), prefix.clone()),
        answer.clone(),
        observation,
        congr_arg(
            &pulse_ty,
            &a.term,
            prefix,
            done,
            mapper,
            terminal.term.clone(),
        ),
    );
    let goal = eq(&a.term, actual_prefix, answer);
    add(
        env,
        LOOP_CPS_COMPLETE_TRANSFER,
        &[
            s, d, a, actual, pulse, finish, observed, residual, count, initial, result, terminal,
        ],
        goal,
        proof,
        true,
    )
}
