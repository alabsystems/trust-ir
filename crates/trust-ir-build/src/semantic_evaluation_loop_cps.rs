// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Finite CPS prefixes and their connection to an actual first-order pulse.
//! The residual continuation is a suspension boundary, never a completion.
//!
//! Install the first-order loop vocabulary before this additive bridge. A
//! consumer must prove equality with its actual CPS step separately. Finite
//! prefix correspondence supplies no termination, native, or source authority.
use super::*;

/// `S A step residual n : S → A`, where `step : (S → A) → S → A`.
/// At zero this is exactly `residual`; successor applies `step` once.
pub const LOOP_CPS_PREFIX: &str = "TrustIR.Eval.Loop.cps_prefix";
/// `S A left right same residual n`: exact `Eq left right` transports to
/// equality of whole finite-prefix functions, without function extensionality.
pub const LOOP_CPS_PREFIX_CONGR: &str = "TrustIR.Eval.Loop.cps_prefix_congr";
/// `S D A pulse finish residual n state`: the canonical CPS step for the
/// supplied `pulse : S → Sum S D` agrees with mapping its first-order prefix.
/// Suspension calls `residual`; terminal results call `finish` unchanged.
pub const LOOP_CPS_PREFIX_FROM_PULSE: &str = "TrustIR.Eval.Loop.cps_prefix_from_pulse";

fn cps_prefix(s: &Expr, a: &Expr, step: Expr, residual: Expr, count: Expr) -> Expr {
    Expr::apps(
        c(LOOP_CPS_PREFIX),
        [s.clone(), a.clone(), step, residual, count],
    )
}

/// Add three declarations after `install_loop_into`. Reject every owned-name
/// collision before mutation. Later errors are not transactional: discard the
/// environment. Existing options and declarations are retained; all theorem
/// values are checked and their rooted closures audited with the usual limits.
pub fn install_cps_loop_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in [
        LOOP_CPS_PREFIX,
        LOOP_CPS_PREFIX_CONGR,
        LOOP_CPS_PREFIX_FROM_PULSE,
    ] {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    recheck_theorem(env, LOOP_PREFIX_CONGR)?;
    cps_definition(env)?;
    cps_congruence(env)?;
    cps_from_pulse(env)?;
    for name in [LOOP_CPS_PREFIX_CONGR, LOOP_CPS_PREFIX_FROM_PULSE] {
        recheck_theorem(env, name)?;
    }
    Ok(())
}

fn cps_definition(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, a] = sc.types();
    let continuation = Expr::arrow(s.term.clone(), a.term.clone());
    let step = sc.local(Expr::arrow(continuation.clone(), continuation.clone()));
    let residual = sc.local(continuation.clone());
    let n = sc.local(Expr::const_str("Nat"));
    let k = sc.local(Expr::const_str("Nat"));
    let previous = sc.local(continuation.clone());
    let motive = k.lam(continuation.clone());
    let successor = lams(
        &[k, previous.clone()],
        Expr::app(step.term.clone(), previous.term),
    );
    let body = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(u())]),
        [motive, residual.term.clone(), successor, n.term.clone()],
    );
    add(
        env,
        LOOP_CPS_PREFIX,
        &[s, a, step, residual, n],
        continuation,
        body,
        false,
    )
}

fn cps_congruence(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, a] = sc.types();
    let continuation = Expr::arrow(s.term.clone(), a.term.clone());
    let step_ty = Expr::arrow(continuation.clone(), continuation.clone());
    let left = sc.local(step_ty.clone());
    let right = sc.local(step_ty.clone());
    let same = sc.local(eq(&step_ty, left.term.clone(), right.term.clone()));
    let residual = sc.local(continuation.clone());
    let count = sc.local(Expr::const_str("Nat"));
    let left_prefix = cps_prefix(
        &s.term,
        &a.term,
        left.term.clone(),
        residual.term.clone(),
        count.term.clone(),
    );
    let right_prefix = cps_prefix(
        &s.term,
        &a.term,
        right.term.clone(),
        residual.term.clone(),
        count.term.clone(),
    );
    let f = sc.local(step_ty.clone());
    let mapper = f.lam(cps_prefix(
        &s.term,
        &a.term,
        f.term.clone(),
        residual.term.clone(),
        count.term.clone(),
    ));
    let proof = congr_arg(
        &step_ty,
        &continuation,
        left.term.clone(),
        right.term.clone(),
        mapper,
        same.term.clone(),
    );
    add(
        env,
        LOOP_CPS_PREFIX_CONGR,
        &[s, a, left, right, same, residual, count],
        eq(&continuation, left_prefix, right_prefix),
        proof,
        true,
    )
}

fn cps_from_pulse(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, d] = sc.types();
    let a = sc.local(Expr::sort(Level::succ(u())));
    let pulse_ty = sum(&s.term, &d.term);
    let pulse = sc.local(Expr::arrow(s.term.clone(), pulse_ty.clone()));
    let finish = sc.local(Expr::arrow(d.term.clone(), a.term.clone()));
    let residual = sc.local(Expr::arrow(s.term.clone(), a.term.clone()));
    let count = sc.local(Expr::const_str("Nat"));
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
    let continuation = sc.local(residual.ty.clone());
    let state = sc.local(s.term.clone());
    let step = lams(
        &[continuation.clone(), state.clone()],
        map(
            &mut sc,
            Expr::app(pulse.term.clone(), state.term),
            continuation.term,
        ),
    );
    let statement = |sc: &mut Scope, n: Expr, state: Expr| {
        let left = Expr::app(
            cps_prefix(
                &s.term,
                &a.term,
                step.clone(),
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
    let ih_ty = next.pi(statement(&mut sc, k.term.clone(), next.term.clone()));
    let ih = sc.local(ih_ty);
    let here = sc.local(s.term.clone());
    let observed = sc.local(pulse_ty.clone());
    let previous = cps_prefix(
        &s.term,
        &a.term,
        step.clone(),
        residual.term.clone(),
        k.term.clone(),
    );
    let after = sc.local(s.term.clone());
    let completed = sc.local(d.term.clone());
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
        completed.lam(side(&s.term, &d.term, true, completed.term.clone())),
        observed.term.clone(),
        false,
    );
    let left = map(&mut sc, observed.term.clone(), previous);
    let right = map(&mut sc, unrolled, residual.term.clone());
    let motive = observed.lam(eq(&a.term, left, right));
    let next = sc.local(s.term.clone());
    let done = sc.local(d.term.clone());
    let successor_body = cases(
        &s.term,
        &d.term,
        motive,
        next.lam(Expr::app(ih.term.clone(), next.term.clone())),
        done.lam(refl(
            &a.term,
            Expr::app(finish.term.clone(), done.term.clone()),
        )),
        Expr::app(pulse.term.clone(), here.term.clone()),
        true,
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
        LOOP_CPS_PREFIX_FROM_PULSE,
        &[s, d, a, pulse, finish, residual, count],
        goal,
        proof,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn finite_cps_prefix_definitions_and_proofs_are_kernel_checked() {
        let mut env = Environment::default();
        install_loop_into(&mut env).unwrap();
        install_cps_loop_into(&mut env).unwrap();
        assert!(install_cps_loop_into(&mut env).is_err());
    }
}
