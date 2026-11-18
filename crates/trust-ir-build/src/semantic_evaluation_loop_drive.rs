// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! First-order pulse prefixes through the ORIGINAL Type0 Core driver.
//! A suspended `inl` is never promoted to completion. The complete `inr`
//! payload survives; a caller still owes its actual source/step/termination
//! proofs and every Core/provider/native obligation.
use super::*;

pub const LOOP_DRIVE_HALTED: &str = "TrustIR.Eval.Loop.drive_halted_v1";
pub const LOOP_DRIVE_STEP: &str = "TrustIR.Eval.Loop.drive_step_v1";
pub const LOOP_DRIVE_PREFIX_SUM: &str = "TrustIR.Eval.Loop.drive_prefix_sum_v1";
pub const LOOP_DRIVE_PREFIX: &str = "TrustIR.Eval.Loop.drive_prefix_v1";
pub const LOOP_DRIVE_COMPLETE: &str = "TrustIR.Eval.Loop.drive_complete_v1";
pub const LOOP_DRIVE_HALT: &str = "TrustIR.Eval.Loop.drive_halt_v1";
const OWNED: [&str; 6] = [
    LOOP_DRIVE_HALTED,
    LOOP_DRIVE_STEP,
    LOOP_DRIVE_PREFIX_SUM,
    LOOP_DRIVE_PREFIX,
    LOOP_DRIVE_COMPLETE,
    LOOP_DRIVE_HALT,
];

fn k(name: &str) -> Expr {
    Expr::const_str(name)
}
fn at(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(k(name), args)
}
fn one() -> Level {
    Level::succ(Level::zero())
}
fn sum0(s: &Expr, d: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Sum"), vec![Level::zero(); 2]),
        [s.clone(), d.clone()],
    )
}
fn side0(s: &Expr, d: &Expr, right: bool, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string(if right { "Sum.inr" } else { "Sum.inl" }),
            vec![Level::zero(); 2],
        ),
        [s.clone(), d.clone(), value],
    )
}
fn cases0(
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
                if prop { Level::zero() } else { one() },
                Level::zero(),
                Level::zero(),
            ],
        ),
        [s.clone(), d.clone(), motive, left, right, value],
    )
}
fn eq0(ty: &Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one()]),
        [ty.clone(), left, right],
    )
}
fn refl0(ty: &Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one()]),
        [ty.clone(), value],
    )
}
fn prefix0(s: &Expr, d: &Expr, f: Expr, n: Expr, state: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(LOOP_PREFIX), vec![Level::zero()]),
        [s.clone(), d.clone(), f, n, state],
    )
}
fn halted(s: &Expr, d: &Expr) -> Expr {
    at(LOOP_DRIVE_HALTED, [s.clone(), d.clone()])
}
fn step(s: &Expr, d: &Expr, f: Expr) -> Expr {
    at(LOOP_DRIVE_STEP, [s.clone(), d.clone(), f])
}
fn drive(s: &Expr, d: &Expr, f: Expr, n: Expr, value: Expr) -> Expr {
    at(
        "ir_drive_v1",
        [sum0(s, d), halted(s, d), step(s, d, f), n, value],
    )
}
fn add0(
    env: &mut Environment,
    name: &str,
    vars: &[Local],
    ty: Expr,
    body: Expr,
    theorem: bool,
) -> Result<(), SemanticEvaluationError> {
    let type_ = pis(vars, ty);
    let value = lams(vars, body);
    let declaration = if theorem {
        Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
        }
    } else {
        Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        }
    };
    env.add_decl(declaration).map_err(|e| error(name, e))
}

// One ambient pot covers ALL installation/typechecking/rooted audits. Never
// replace an active caller budget or refill it between declarations.
struct Budget(bool);
impl Budget {
    fn enter() -> Result<Self, SemanticEvaluationError> {
        if clean_kernel::env::mm_axiom_only() {
            return Err(error(LOOP_DRIVE_PREFIX, "strict kernel mode required"));
        }
        let limit = clean_kernel::tc::declaration_budget_limit();
        if limit == 0 {
            clean_kernel::tc::set_declaration_budget(2_000_000);
            Ok(Self(true))
        } else if clean_kernel::tc::declaration_budget_remaining() <= 2_000_000 {
            Ok(Self(false))
        } else {
            Err(error(
                LOOP_DRIVE_PREFIX,
                "cannot replace a larger active caller budget",
            ))
        }
    }
}
impl Drop for Budget {
    fn drop(&mut self) {
        if self.0 {
            clean_kernel::tc::clear_declaration_budget();
        }
    }
}

/// Type0 specialization, with no universe arguments. Install AFTER the
/// original loop vocabulary and canonical ByteV1 `ir_drive_v1`. The latter
/// is checked against its fixed recursion BEFORE any bridge is installed;
/// its name alone supplies no authority. Existing polymorphic/CPS APIs stay
/// unchanged. Every telescope is closed before a consumer applies its terms.
/// Collisions refuse before mutation; discard env after any later failure.
pub fn install_loop_drive_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in OWNED {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    let _budget = Budget::enter()?;
    recheck_theorem(env, LOOP_PREFIX_CONGR)?;
    canonical_driver(env)?;
    definitions(env)?;
    all_sum(env)?;
    initial(env)?;
    complete(env)?;
    halt(env)?;
    for name in &OWNED[2..] {
        recheck_theorem(env, name)?;
    }
    if clean_kernel::tc::declaration_budget_exhausted() || clean_kernel::tc::poll_deadline() {
        return Err(error(
            LOOP_DRIVE_PREFIX,
            "aggregate kernel budget/deadline stopped",
        ));
    }
    Ok(())
}

// Reconstruct the canonical driver's fixed Type0 recursion, not a replacement
// driver. The universally quantified pointwise comparison is kernel checked.
fn driver_contract() -> (Expr, Expr) {
    let mut sc = Scope::default();
    let c = sc.local(Expr::type_());
    let h = sc.local(Expr::arrow(c.term.clone(), k("Bool")));
    let f = sc.local(Expr::arrow(c.term.clone(), c.term.clone()));
    let n = sc.local(k("Nat"));
    let x = sc.local(c.term.clone());
    let z = sc.local(c.term.clone());
    let count = sc.local(k("Nat"));
    let ih = sc.local(f.ty.clone());
    let current = sc.local(c.term.clone());
    let flag = sc.local(k("Bool"));
    let next = Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![one()]),
        [
            flag.lam(c.term.clone()),
            Expr::app(
                ih.term.clone(),
                Expr::app(f.term.clone(), current.term.clone()),
            ),
            current.term.clone(),
            Expr::app(h.term.clone(), current.term.clone()),
        ],
    );
    let index = sc.local(k("Nat"));
    let expected = Expr::app(
        Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![one()]),
            [
                index.lam(f.ty.clone()),
                z.lam(z.term.clone()),
                lams(&[count, ih, current], next),
                n.term.clone(),
            ],
        ),
        x.term.clone(),
    );
    let actual = at(
        "ir_drive_v1",
        [
            c.term.clone(),
            h.term.clone(),
            f.term.clone(),
            n.term.clone(),
            x.term.clone(),
        ],
    );
    let vars = [c.clone(), h, f, n, x];
    (
        pis(&vars, eq0(&c.term, actual.clone(), expected)),
        lams(&vars, refl0(&c.term, actual)),
    )
}
fn canonical_driver(env: &Environment) -> Result<(), SemanticEvaluationError> {
    let info = env
        .get_const(&Name::from_string("ir_drive_v1"))
        .ok_or_else(|| error(LOOP_DRIVE_PREFIX, "missing canonical ir_drive_v1"))?;
    if info.kind != ConstantKind::Definition
        || !info.level_params.is_empty()
        || info.value.is_none()
    {
        return Err(error(
            LOOP_DRIVE_PREFIX,
            "ir_drive_v1 must be the original Type0 definition",
        ));
    }
    let (goal, proof) = driver_contract();
    let mut tc = TypeChecker::with_mode(env, env.mode());
    tc.set_heartbeat_limit(
        env.get_option("maxHeartbeats")
            .and_then(Option::as_ref)
            .and_then(|value| value.parse().ok())
            .unwrap_or(HEARTBEAT_LIMIT),
    );
    tc.set_max_cache_entries(
        env.get_option("tcMaxCacheEntries")
            .and_then(Option::as_ref)
            .and_then(|value| value.parse().ok())
            .unwrap_or(CACHE_ENTRY_LIMIT),
    );
    tc.check_type(&proof, &goal)
        .map_err(|e| error("ir_drive_v1 canonical recursion", e))?;
    let audit = env.audit_certification(&goal, &proof);
    if !audit.issues.is_empty() {
        return Err(error("ir_drive_v1 canonical recursion", audit.issues));
    }
    Ok(())
}
fn definitions(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let s = sc.local(Expr::type_());
    let d = sc.local(Expr::type_());
    let sd = sum0(&s.term, &d.term);
    let value = sc.local(sd.clone());
    let ignored = sc.local(sd.clone());
    let state = sc.local(s.term.clone());
    let done = sc.local(d.term.clone());
    let body = cases0(
        &s.term,
        &d.term,
        ignored.lam(k("Bool")),
        state.lam(k("Bool.false")),
        done.lam(k("Bool.true")),
        value.term.clone(),
        false,
    );
    add0(
        env,
        LOOP_DRIVE_HALTED,
        &[s.clone(), d.clone(), value],
        k("Bool"),
        body,
        false,
    )?;
    let f = sc.local(Expr::arrow(s.term.clone(), sd.clone()));
    let value = sc.local(sd.clone());
    let body = cases0(
        &s.term,
        &d.term,
        ignored.lam(sd.clone()),
        f.term.clone(),
        done.lam(side0(&s.term, &d.term, true, done.term.clone())),
        value.term.clone(),
        false,
    );
    add0(env, LOOP_DRIVE_STEP, &[s, d, f, value], sd, body, false)
}
fn resolved(sc: &mut Scope, s: &Expr, d: &Expr, f: Expr, n: Expr, value: Expr) -> Expr {
    let sd = sum0(s, d);
    let ignored = sc.local(sd.clone());
    let state = sc.local(s.clone());
    let done = sc.local(d.clone());
    cases0(
        s,
        d,
        ignored.lam(sd),
        state.lam(prefix0(s, d, f, n, state.term.clone())),
        done.lam(side0(s, d, true, done.term.clone())),
        value,
        false,
    )
}
fn all_sum(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let s = sc.local(Expr::type_());
    let d = sc.local(Expr::type_());
    let sd = sum0(&s.term, &d.term);
    let f = sc.local(Expr::arrow(s.term.clone(), sd.clone()));
    let n = sc.local(k("Nat"));
    let value = sc.local(sd.clone());
    let statement = |sc: &mut Scope, n: Expr, value: Expr| {
        eq0(
            &sd,
            drive(&s.term, &d.term, f.term.clone(), n.clone(), value.clone()),
            resolved(sc, &s.term, &d.term, f.term.clone(), n, value),
        )
    };
    let z = sc.local(sd.clone());
    let left = sc.local(s.term.clone());
    let right = sc.local(d.term.clone());
    let zero = z.lam(cases0(
        &s.term,
        &d.term,
        z.lam(statement(&mut sc, Expr::nat_lit(0), z.term.clone())),
        left.lam(refl0(
            &sd,
            side0(&s.term, &d.term, false, left.term.clone()),
        )),
        right.lam(refl0(
            &sd,
            side0(&s.term, &d.term, true, right.term.clone()),
        )),
        z.term.clone(),
        true,
    ));
    let count = sc.local(k("Nat"));
    let arbitrary = sc.local(sd.clone());
    let hypothesis = arbitrary.pi(statement(
        &mut sc,
        count.term.clone(),
        arbitrary.term.clone(),
    ));
    let ih = sc.local(hypothesis);
    let current = sc.local(sd.clone());
    let left = sc.local(s.term.clone());
    let right = sc.local(d.term.clone());
    let successor = lams(
        &[count.clone(), ih.clone(), current.clone()],
        cases0(
            &s.term,
            &d.term,
            current.lam(statement(
                &mut sc,
                at("Nat.succ", [count.term.clone()]),
                current.term.clone(),
            )),
            left.lam(Expr::app(
                ih.term.clone(),
                Expr::app(f.term.clone(), left.term.clone()),
            )),
            right.lam(refl0(
                &sd,
                side0(&s.term, &d.term, true, right.term.clone()),
            )),
            current.term.clone(),
            true,
        ),
    );
    let index = sc.local(k("Nat"));
    let arbitrary = sc.local(sd.clone());
    let motive = index.lam(arbitrary.pi(statement(
        &mut sc,
        index.term.clone(),
        arbitrary.term.clone(),
    )));
    let proof = Expr::app(
        Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [motive, zero, successor, n.term.clone()],
        ),
        value.term.clone(),
    );
    let goal = statement(&mut sc, n.term.clone(), value.term.clone());
    add0(
        env,
        LOOP_DRIVE_PREFIX_SUM,
        &[s, d, f, n, value],
        goal,
        proof,
        true,
    )
}
fn initial(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let s = sc.local(Expr::type_());
    let d = sc.local(Expr::type_());
    let sd = sum0(&s.term, &d.term);
    let f = sc.local(Expr::arrow(s.term.clone(), sd.clone()));
    let n = sc.local(k("Nat"));
    let state = sc.local(s.term.clone());
    let start = side0(&s.term, &d.term, false, state.term.clone());
    let goal = eq0(
        &sd,
        drive(
            &s.term,
            &d.term,
            f.term.clone(),
            n.term.clone(),
            start.clone(),
        ),
        prefix0(
            &s.term,
            &d.term,
            f.term.clone(),
            n.term.clone(),
            state.term.clone(),
        ),
    );
    let proof = at(
        LOOP_DRIVE_PREFIX_SUM,
        [
            s.term.clone(),
            d.term.clone(),
            f.term.clone(),
            n.term.clone(),
            start,
        ],
    );
    add0(
        env,
        LOOP_DRIVE_PREFIX,
        &[s, d, f, n, state],
        goal,
        proof,
        true,
    )
}
fn complete(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let s = sc.local(Expr::type_());
    let d = sc.local(Expr::type_());
    let sd = sum0(&s.term, &d.term);
    let f = sc.local(Expr::arrow(s.term.clone(), sd.clone()));
    let n = sc.local(k("Nat"));
    let state = sc.local(s.term.clone());
    let done = sc.local(d.term.clone());
    let pref = prefix0(
        &s.term,
        &d.term,
        f.term.clone(),
        n.term.clone(),
        state.term.clone(),
    );
    let result = side0(&s.term, &d.term, true, done.term.clone());
    let h = sc.local(eq0(&sd, pref.clone(), result.clone()));
    let actual = drive(
        &s.term,
        &d.term,
        f.term.clone(),
        n.term.clone(),
        side0(&s.term, &d.term, false, state.term.clone()),
    );
    let prefix_proof = at(
        LOOP_DRIVE_PREFIX,
        [
            s.term.clone(),
            d.term.clone(),
            f.term.clone(),
            n.term.clone(),
            state.term.clone(),
        ],
    );
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![one()]),
        [
            sd.clone(),
            actual.clone(),
            pref,
            result.clone(),
            prefix_proof,
            h.term.clone(),
        ],
    );
    let goal = eq0(&sd, actual, result);
    add0(
        env,
        LOOP_DRIVE_COMPLETE,
        &[s, d, f, n, state, done, h],
        goal,
        proof,
        true,
    )
}
fn halt(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let s = sc.local(Expr::type_());
    let d = sc.local(Expr::type_());
    let sd = sum0(&s.term, &d.term);
    let f = sc.local(Expr::arrow(s.term.clone(), sd.clone()));
    let n = sc.local(k("Nat"));
    let state = sc.local(s.term.clone());
    let done = sc.local(d.term.clone());
    let pref = prefix0(
        &s.term,
        &d.term,
        f.term.clone(),
        n.term.clone(),
        state.term.clone(),
    );
    let result = side0(&s.term, &d.term, true, done.term.clone());
    let h = sc.local(eq0(&sd, pref, result.clone()));
    let actual = drive(
        &s.term,
        &d.term,
        f.term.clone(),
        n.term.clone(),
        side0(&s.term, &d.term, false, state.term.clone()),
    );
    let proof = at(
        LOOP_DRIVE_COMPLETE,
        [
            s.term.clone(),
            d.term.clone(),
            f.term.clone(),
            n.term.clone(),
            state.term.clone(),
            done.term.clone(),
            h.term.clone(),
        ],
    );
    let proof = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![one(), one()]),
        [
            sd,
            k("Bool"),
            actual.clone(),
            result,
            halted(&s.term, &d.term),
            proof,
        ],
    );
    let goal = eq0(
        &k("Bool"),
        Expr::app(halted(&s.term, &d.term), actual),
        k("Bool.true"),
    );
    add0(
        env,
        LOOP_DRIVE_HALT,
        &[s, d, f, n, state, done, h],
        goal,
        proof,
        true,
    )
}

#[cfg(test)]
#[path = "semantic_evaluation_loop_drive_tests.rs"]
mod tests;
