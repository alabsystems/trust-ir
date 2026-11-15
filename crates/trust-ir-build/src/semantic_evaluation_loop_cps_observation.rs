// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! A pointwise observation law transports an actual CPS step to pulse prefixes.
//! The observation premise is mandatory and kernel-checked; no CPS converse or
//! function-extensionality axiom is assumed.
use super::*;

/// `S D A actual pulse finish observed residual n state`. The premise
/// `observed` quantifies over every resume continuation and every state.
/// Its conclusion maps the actual finite prefix through the supplied pulse.
pub const LOOP_CPS_PREFIX_OBSERVATION: &str = "TrustIR.Eval.Loop.cps_prefix_observation";

/// Install after `install_cps_loop_into`. Collisions refuse before mutation;
/// later errors require discarding the environment. Existing declarations and
/// caller limits are preserved. The stored proof is kernel-checked and audited.
pub fn install_cps_observation_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    if env
        .get_const(&Name::from_string(LOOP_CPS_PREFIX_OBSERVATION))
        .is_some()
    {
        return Err(error(
            LOOP_CPS_PREFIX_OBSERVATION,
            "owned declaration already exists",
        ));
    }
    recheck_theorem(env, LOOP_CPS_PREFIX_FROM_PULSE)?;
    observation(env)?;
    recheck_theorem(env, LOOP_CPS_PREFIX_OBSERVATION)
}

fn actual_prefix(s: &Expr, a: &Expr, step: Expr, residual: Expr, count: Expr) -> Expr {
    Expr::apps(
        c(LOOP_CPS_PREFIX),
        [s.clone(), a.clone(), step, residual, count],
    )
}

fn observation(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
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
    let map = |sc: &mut Scope, observed: Expr, continued: Expr| {
        let ignored = sc.local(pulse_ty.clone());
        cases(
            &s.term,
            &d.term,
            ignored.lam(a.term.clone()),
            continued,
            finish.term.clone(),
            observed,
            false,
        )
    };
    let continued = sc.local(continuation_ty.clone());
    let state = sc.local(s.term.clone());
    let observation_type = pis(
        &[continued.clone(), state.clone()],
        eq(
            &a.term,
            Expr::apps(
                actual.term.clone(),
                [continued.term.clone(), state.term.clone()],
            ),
            map(
                &mut sc,
                Expr::app(pulse.term.clone(), state.term),
                continued.term,
            ),
        ),
    );
    let observed = sc.local(observation_type);
    let residual = sc.local(continuation_ty);
    let count = sc.local(Expr::const_str("Nat"));
    let statement = |sc: &mut Scope, n: Expr, state: Expr| {
        let left = Expr::app(
            actual_prefix(
                &s.term,
                &a.term,
                actual.term.clone(),
                residual.term.clone(),
                n.clone(),
            ),
            state.clone(),
        );
        let right = map(
            sc,
            prefix(&s.term, &d.term, pulse.term.clone(), n, state),
            residual.term.clone(),
        );
        eq(&a.term, left, right)
    };
    let initial = sc.local(s.term.clone());
    let zero = initial.lam(refl(
        &a.term,
        Expr::app(residual.term.clone(), initial.term.clone()),
    ));
    let k = sc.local(Expr::const_str("Nat"));
    let next = sc.local(s.term.clone());
    let ih_type = next.pi(statement(&mut sc, k.term.clone(), next.term.clone()));
    let ih = sc.local(ih_type);
    let here = sc.local(s.term.clone());
    let previous = actual_prefix(
        &s.term,
        &a.term,
        actual.term.clone(),
        residual.term.clone(),
        k.term.clone(),
    );
    let actual_here = Expr::apps(actual.term.clone(), [previous.clone(), here.term.clone()]);
    let pulse_here = Expr::app(pulse.term.clone(), here.term.clone());
    let middle = map(&mut sc, pulse_here.clone(), previous.clone());
    let right = map(
        &mut sc,
        prefix(
            &s.term,
            &d.term,
            pulse.term.clone(),
            Expr::app(Expr::const_str("Nat.succ"), k.term.clone()),
            here.term.clone(),
        ),
        residual.term.clone(),
    );
    let observation_proof =
        Expr::apps(observed.term.clone(), [previous.clone(), here.term.clone()]);
    let item = sc.local(pulse_ty.clone());
    let after = sc.local(s.term.clone());
    let done = sc.local(d.term.clone());
    let ignored = sc.local(pulse_ty.clone());
    let unrolled = cases(
        &s.term,
        &d.term,
        ignored.lam(pulse_ty.clone()),
        after.lam(prefix(
            &s.term,
            &d.term,
            pulse.term.clone(),
            k.term.clone(),
            after.term.clone(),
        )),
        done.lam(side(&s.term, &d.term, true, done.term.clone())),
        item.term.clone(),
        false,
    );
    let left_case = map(&mut sc, item.term.clone(), previous);
    let right_case = map(&mut sc, unrolled, residual.term.clone());
    let motive = item.lam(eq(&a.term, left_case, right_case));
    let after = sc.local(s.term.clone());
    let done = sc.local(d.term.clone());
    let case_proof = cases(
        &s.term,
        &d.term,
        motive,
        after.lam(Expr::app(ih.term.clone(), after.term.clone())),
        done.lam(refl(
            &a.term,
            Expr::app(finish.term.clone(), done.term.clone()),
        )),
        pulse_here,
        true,
    );
    let successor_body = trans(
        &a.term,
        actual_here,
        middle,
        right,
        observation_proof,
        case_proof,
    );
    let successor = lams(&[k, ih, here], successor_body);
    let n = sc.local(Expr::const_str("Nat"));
    let state = sc.local(s.term.clone());
    let motive = n.lam(state.pi(statement(&mut sc, n.term.clone(), state.term.clone())));
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [motive, zero, successor, count.term.clone()],
    );
    let state = sc.local(s.term.clone());
    let goal = state.pi(statement(&mut sc, count.term.clone(), state.term.clone()));
    add(
        env,
        LOOP_CPS_PREFIX_OBSERVATION,
        &[s, d, a, actual, pulse, finish, observed, residual, count],
        goal,
        proof,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn pointwise_cps_prefix_theorem_is_kernel_checked() {
        let mut env = Environment::default();
        install_loop_into(&mut env).unwrap();
        install_cps_loop_into(&mut env).unwrap();
        install_cps_observation_into(&mut env).unwrap();
        assert!(install_cps_observation_into(&mut env).is_err());
    }
}
