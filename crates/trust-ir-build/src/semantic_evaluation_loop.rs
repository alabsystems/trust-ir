// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! First-order loop prefixes. `Sum.inl state` is suspended/continue, never a
//! successful completion. Step equality must be reconstructed from endpoints.
//! No source membership, provider totality, termination or native authority.
use super::*;

#[path = "semantic_evaluation_loop_drive.rs"]
mod drive;
pub use drive::{
    LOOP_DRIVE_COMPLETE, LOOP_DRIVE_HALT, LOOP_DRIVE_HALTED, LOOP_DRIVE_PREFIX,
    LOOP_DRIVE_PREFIX_SUM, LOOP_DRIVE_STEP, install_loop_drive_into,
};

#[path = "semantic_evaluation_loop_cps.rs"]
mod cps_prefix;
pub use cps_prefix::{
    LOOP_CPS_PREFIX, LOOP_CPS_PREFIX_CONGR, LOOP_CPS_PREFIX_FROM_PULSE, install_cps_loop_into,
};

#[path = "semantic_evaluation_loop_cps_observation.rs"]
mod cps_observation;
pub use cps_observation::{LOOP_CPS_PREFIX_OBSERVATION, install_cps_observation_into};

#[path = "semantic_evaluation_loop_cps_complete.rs"]
mod cps_completion;
pub use cps_completion::{LOOP_CPS_COMPLETE_TRANSFER, install_cps_completion_into};

#[path = "semantic_evaluation_domain.rs"]
mod domain;
pub use domain::{
    DOMAIN_AT, DOMAIN_AT_COVER, DOMAIN_AT_END, DOMAIN_AT_MEMBERS, DOMAIN_AT_SOUND,
    install_indexed_domain_into,
};
pub use domain::{DOMAIN_COMPLETE, DOMAIN_FOLD, DOMAIN_LENGTH, DOMAIN_STEP, install_domain_into};
pub use domain::{
    DOMAIN_ENUMERATE, DOMAIN_ENUMERATE_AT, DOMAIN_ENUMERATE_END, DOMAIN_ENUMERATE_LENGTH,
    DOMAIN_ENUMERATE_NONE, DOMAIN_ENUMERATE_SOME, install_enumerated_domain_into,
};

pub use domain::{
    DOMAIN_TAIL_COMPLETE, DOMAIN_TAIL_FOLD, DOMAIN_TAIL_STEP, install_tail_domain_into,
};
#[path = "semantic_evaluation_loop_map.rs"]
mod mapping;
pub use mapping::{LOOP_MAP_COMPLETE, LOOP_MAP_PREFIX, LOOP_MAP_PULSE, install_loop_map_into};
#[path = "semantic_evaluation_cut_run.rs"]
mod cut_run;
pub use cut_run::{
    IMAGE_TO_PULSE, IMAGE_TO_PULSE_OBSERVATION, RUN_TO_PULSE, RUN_TO_PULSE_CPS,
    install_cut_observation_into, install_cut_run_into,
};
#[path = "semantic_evaluation_loop_rank.rs"]
mod ranking;
pub use ranking::{LOOP_RANK_COMPLETE, install_ranked_loop_into};

pub const LOOP_PREFIX: &str = "TrustIR.Eval.Loop.prefix";
pub const LOOP_PREFIX_CONGR: &str = "TrustIR.Eval.Loop.prefix_congr";
pub const LOOP_COMPLETE_TRANSFER: &str = "TrustIR.Eval.Loop.complete_transfer";

fn sum(s: &Expr, d: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Sum"), vec![u(), u()]),
        [s.clone(), d.clone()],
    )
}
fn side(s: &Expr, d: &Expr, right: bool, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string(if right { "Sum.inr" } else { "Sum.inl" }),
            vec![u(), u()],
        ),
        [s.clone(), d.clone(), value],
    )
}
fn cases(
    s: &Expr,
    d: &Expr,
    motive: Expr,
    left: Expr,
    right: Expr,
    value: Expr,
    prop: bool,
) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Sum.rec"),
            vec![
                if prop {
                    Level::zero()
                } else {
                    Level::succ(u())
                },
                u(),
                u(),
            ],
        ),
        [s.clone(), d.clone(), motive, left, right, value],
    )
}
fn prefix(s: &Expr, d: &Expr, f: Expr, n: Expr, state: Expr) -> Expr {
    Expr::apps(c(LOOP_PREFIX), [s.clone(), d.clone(), f, n, state])
}

/// Install the fixed definitions and checked, pointwise laws. Owned-name
/// collisions reject before any mutation. On later failure discard the env.
pub fn install_loop_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in [LOOP_PREFIX, LOOP_PREFIX_CONGR, LOOP_COMPLETE_TRANSFER] {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    env.init_eq().map_err(|e| error(LOOP_PREFIX, e))?;
    env.init_nat().map_err(|e| error(LOOP_PREFIX, e))?;
    env.init_sum().map_err(|e| error(LOOP_PREFIX, e))?;
    definition(env)?;
    congruence(env)?;
    complete(env)?;
    for theorem in [LOOP_PREFIX_CONGR, LOOP_COMPLETE_TRANSFER] {
        recheck_theorem(env, theorem)?;
    }
    Ok(())
}

fn definition(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, d] = sc.types();
    let pulse = sum(&s.term, &d.term);
    let f = sc.local(Expr::arrow(s.term.clone(), pulse.clone()));
    let n = sc.local(Expr::const_str("Nat"));
    let state = sc.local(s.term.clone());
    let zero = state.lam(side(&s.term, &d.term, false, state.term.clone()));
    let k = sc.local(Expr::const_str("Nat"));
    let previous = sc.local(f.ty.clone());
    let input = sc.local(s.term.clone());
    let completed = sc.local(d.term.clone());
    let ignored = sc.local(pulse.clone());
    let body = cases(
        &s.term,
        &d.term,
        ignored.lam(pulse.clone()),
        previous.term.clone(),
        completed.lam(side(&s.term, &d.term, true, completed.term.clone())),
        Expr::app(f.term.clone(), input.term.clone()),
        false,
    );
    let successor = lams(&[k, previous, input], body);
    let index = sc.local(Expr::const_str("Nat"));
    let motive = index.lam(f.ty.clone());
    let recursion = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(u())]),
        [motive, zero, successor, n.term.clone()],
    );
    add(
        env,
        LOOP_PREFIX,
        &[s, d, f.clone(), n],
        f.ty,
        recursion,
        false,
    )
}

fn congruence(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, d] = sc.types();
    let pulse = sum(&s.term, &d.term);
    let f = sc.local(Expr::arrow(s.term.clone(), pulse.clone()));
    let g = sc.local(f.ty.clone());
    let input = sc.local(s.term.clone());
    let h = sc.local(input.pi(eq(
        &pulse,
        Expr::app(f.term.clone(), input.term.clone()),
        Expr::app(g.term.clone(), input.term.clone()),
    )));
    let n = sc.local(Expr::const_str("Nat"));
    let state = sc.local(s.term.clone());
    let statement = |n: Expr, state: Expr| {
        eq(
            &pulse,
            prefix(&s.term, &d.term, f.term.clone(), n.clone(), state.clone()),
            prefix(&s.term, &d.term, g.term.clone(), n, state),
        )
    };
    let k = sc.local(Expr::const_str("Nat"));
    let z = sc.local(s.term.clone());
    let zero = z.lam(refl(&pulse, side(&s.term, &d.term, false, z.term.clone())));
    let v = sc.local(s.term.clone());
    let ih = sc.local(v.pi(statement(k.term.clone(), v.term.clone())));
    let current = sc.local(s.term.clone());
    let item = sc.local(pulse.clone());
    let next = sc.local(s.term.clone());
    let done = sc.local(d.term.clone());
    let map = |sc: &mut Scope, step: Expr| {
        let next = sc.local(s.term.clone());
        let done = sc.local(d.term.clone());
        let p = sc.local(pulse.clone());
        p.lam(cases(
            &s.term,
            &d.term,
            item.lam(pulse.clone()),
            next.lam(prefix(
                &s.term,
                &d.term,
                step,
                k.term.clone(),
                next.term.clone(),
            )),
            done.lam(side(&s.term, &d.term, true, done.term.clone())),
            p.term.clone(),
            false,
        ))
    };
    let source_map = map(&mut sc, f.term.clone());
    let target_map = map(&mut sc, g.term.clone());
    let p = sc.local(pulse.clone());
    let motive = p.lam(eq(
        &pulse,
        Expr::app(source_map.clone(), p.term.clone()),
        Expr::app(target_map.clone(), p.term.clone()),
    ));
    let same = cases(
        &s.term,
        &d.term,
        motive,
        next.lam(Expr::app(ih.term.clone(), next.term.clone())),
        done.lam(refl(
            &pulse,
            side(&s.term, &d.term, true, done.term.clone()),
        )),
        Expr::app(f.term.clone(), current.term.clone()),
        true,
    );
    let source_pulse = Expr::app(f.term.clone(), current.term.clone());
    let target_pulse = Expr::app(g.term.clone(), current.term.clone());
    let transported = congr_arg(
        &pulse,
        &pulse,
        source_pulse.clone(),
        target_pulse.clone(),
        target_map.clone(),
        Expr::app(h.term.clone(), current.term.clone()),
    );
    let equality = trans(
        &pulse,
        Expr::app(source_map, source_pulse.clone()),
        Expr::app(target_map.clone(), source_pulse),
        Expr::app(target_map, target_pulse),
        same,
        transported,
    );
    let successor = lams(&[k, ih, current], equality);
    let counter = sc.local(Expr::const_str("Nat"));
    let initial = sc.local(s.term.clone());
    let motive = counter.lam(initial.pi(statement(counter.term.clone(), initial.term.clone())));
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [motive, zero, successor, n.term.clone(), state.term.clone()],
    );
    add(
        env,
        LOOP_PREFIX_CONGR,
        &[
            s.clone(),
            d.clone(),
            f.clone(),
            g.clone(),
            h,
            n.clone(),
            state.clone(),
        ],
        statement(n.term, state.term),
        proof,
        true,
    )
}

fn complete(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, d] = sc.types();
    let pulse = sum(&s.term, &d.term);
    let f = sc.local(Expr::arrow(s.term.clone(), pulse.clone()));
    let g = sc.local(f.ty.clone());
    let state = sc.local(s.term.clone());
    let h = sc.local(state.pi(eq(
        &pulse,
        Expr::app(f.term.clone(), state.term.clone()),
        Expr::app(g.term.clone(), state.term.clone()),
    )));
    let n = sc.local(Expr::const_str("Nat"));
    let initial = sc.local(s.term.clone());
    let result = sc.local(d.term.clone());
    let left = prefix(
        &s.term,
        &d.term,
        f.term.clone(),
        n.term.clone(),
        initial.term.clone(),
    );
    let right = prefix(
        &s.term,
        &d.term,
        g.term.clone(),
        n.term.clone(),
        initial.term.clone(),
    );
    let done = side(&s.term, &d.term, true, result.term.clone());
    let finishes = sc.local(eq(&pulse, left.clone(), done.clone()));
    let equal = Expr::apps(
        c(LOOP_PREFIX_CONGR),
        [
            s.term.clone(),
            d.term.clone(),
            f.term.clone(),
            g.term.clone(),
            h.term.clone(),
            n.term.clone(),
            initial.term.clone(),
        ],
    );
    let reversed = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(u())]),
        [pulse.clone(), left.clone(), right.clone(), equal],
    );
    let proof = trans(
        &pulse,
        right.clone(),
        left,
        done.clone(),
        reversed,
        finishes.term.clone(),
    );
    add(
        env,
        LOOP_COMPLETE_TRANSFER,
        &[s, d, f, g, h, n, initial, result, finishes],
        eq(&pulse, right, done),
        proof,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn loop_prefix_laws_are_checked_and_audited_without_termination_axioms() {
        let mut env = Environment::default();
        install_loop_into(&mut env).unwrap();
        for name in [LOOP_PREFIX_CONGR, LOOP_COMPLETE_TRANSFER] {
            recheck_theorem(&env, name).unwrap();
        }
        assert!(install_loop_into(&mut env).is_err());
    }

    #[test]
    fn loop_prefix_zero_fuel_cannot_claim_a_done_result() {
        let mut env = Environment::default();
        install_loop_into(&mut env).unwrap();
        let nat = Expr::const_str("Nat");
        let pulse = Expr::apps(
            Expr::const_(Name::from_string("Sum"), vec![Level::zero(), Level::zero()]),
            [nat.clone(), nat.clone()],
        );
        let done = Expr::apps(
            Expr::const_(
                Name::from_string("Sum.inr"),
                vec![Level::zero(), Level::zero()],
            ),
            [nat.clone(), nat.clone(), Expr::nat_lit(7)],
        );
        let step = Expr::lam(BinderInfo::Default, nat.clone(), done.clone());
        let suspended = Expr::apps(
            Expr::const_(Name::from_string(LOOP_PREFIX), vec![Level::zero()]),
            [nat.clone(), nat, step, Expr::nat_lit(0), Expr::nat_lit(7)],
        );
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [pulse.clone(), suspended.clone(), done],
        );
        TypeChecker::new(&env)
            .check_type(&goal, &Expr::sort(Level::zero()))
            .unwrap();
        let lie = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [pulse, suspended],
        );
        assert!(TypeChecker::new(&env).check_type(&lie, &goal).is_err());
    }
}
