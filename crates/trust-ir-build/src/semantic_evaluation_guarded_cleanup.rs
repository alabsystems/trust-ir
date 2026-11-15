// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Pointwise decoding/cleanup interchange under the original success guard.
//! The cleanup continuation receives its actual returned state and outcome.
//! This law assumes neither a CPS image nor linear use of the continuation.
//! It does not equate callback functions or transport through an opaque caller.
use super::*;

pub const GUARDED_CLEANUP_DECODE_FIRST: &str = "TrustIR.Eval.guarded_cleanup_decode_first";
pub const GUARDED_CLEANUP_RAW_FIRST: &str = "TrustIR.Eval.guarded_cleanup_raw_first";
pub const GUARDED_RAW_CLEANUP: &str = "TrustIR.Eval.guarded_raw_cleanup";

const NAMES: [&str; 3] = [
    GUARDED_CLEANUP_DECODE_FIRST,
    GUARDED_CLEANUP_RAW_FIRST,
    GUARDED_RAW_CLEANUP,
];

/// `S E V A cleanup yes ok err state original`, all explicit, at universe `u`.
/// `cleanup : S -> (S -> Except E V -> A) -> A` is unrestricted.
/// Both endpoints first test whether `original` succeeded and call exactly
/// `yes state original` if so. Otherwise cleanup runs at `state`; its success
/// preserves the original payload, and its failure replaces that payload.
/// Equality is at this particular state/outcome, not equality of CPS functions.
///
/// Reject owned-name collisions before mutation. A later failure requires the
/// caller to discard the environment. Existing declarations/options are kept.
pub fn install_guarded_raw_cleanup_into(
    env: &mut Environment,
) -> Result<(), SemanticEvaluationError> {
    for name in NAMES {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    env.init_eq().map_err(|e| error(GUARDED_RAW_CLEANUP, e))?;
    env.init_bool().map_err(|e| error(GUARDED_RAW_CLEANUP, e))?;
    env.init_except_t()
        .map_err(|e| error(GUARDED_RAW_CLEANUP, e))?;
    endpoint(env, true)?;
    endpoint(env, false)?;
    theorem(env)?;
    recheck_theorem(env, GUARDED_RAW_CLEANUP)?;
    for name in NAMES {
        let name = Name::from_string(name);
        for (kind, closure) in [
            ("domain", env.axiom_deps(&name)),
            ("foundational", env.foundational_axiom_deps(&name)),
            ("trust-marker", env.trust_marker_deps(&name)),
        ] {
            if !closure.is_some_and(|dependencies| dependencies.is_empty()) {
                return Err(error(
                    GUARDED_RAW_CLEANUP,
                    format!("{name}: nonempty or absent {kind} closure"),
                ));
            }
        }
    }
    Ok(())
}

struct Terms {
    s: Local,
    e: Local,
    v: Local,
    a: Local,
    cleanup: Local,
    yes: Local,
    ok: Local,
    err: Local,
    state: Local,
    original: Local,
}

impl Terms {
    fn new(sc: &mut Scope) -> Self {
        let [s, e, v, a] = sc.types();
        let status = outcome(&e.term, &v.term);
        let callback = Expr::arrow(s.term.clone(), Expr::arrow(status.clone(), a.term.clone()));
        let cleanup = sc.local(Expr::arrow(
            s.term.clone(),
            Expr::arrow(callback.clone(), a.term.clone()),
        ));
        let yes = sc.local(callback);
        let ok = sc.local(Expr::arrow(
            s.term.clone(),
            Expr::arrow(v.term.clone(), a.term.clone()),
        ));
        let err = sc.local(Expr::arrow(
            s.term.clone(),
            Expr::arrow(e.term.clone(), a.term.clone()),
        ));
        let state = sc.local(s.term.clone());
        let original = sc.local(status);
        Self {
            s,
            e,
            v,
            a,
            cleanup,
            yes,
            ok,
            err,
            state,
            original,
        }
    }

    fn parameters(&self) -> Vec<Local> {
        vec![
            self.s.clone(),
            self.e.clone(),
            self.v.clone(),
            self.a.clone(),
            self.cleanup.clone(),
            self.yes.clone(),
            self.ok.clone(),
            self.err.clone(),
            self.state.clone(),
            self.original.clone(),
        ]
    }

    fn call(&self, name: &str, original: Expr) -> Expr {
        apps(
            name,
            self.parameters()
                .iter()
                .take(9)
                .map(|p| p.term.clone())
                .chain([original]),
        )
    }

    fn choose(&self, sc: &mut Scope, test: Expr, yes: Expr, no: Expr) -> Expr {
        let ignored = sc.local(bool_ty());
        bool_cases(ignored.lam(self.a.term.clone()), no, yes, test, false)
    }

    fn success(&self, sc: &mut Scope, status: Expr) -> Expr {
        let ignored = sc.local(outcome(&self.e.term, &self.v.term));
        let error = sc.local(self.e.term.clone());
        let value = sc.local(self.v.term.clone());
        // Bool remains in Type 0 even when the data carriers use Type u.
        Expr::apps(
            Expr::const_(
                Name::from_string("Except.rec"),
                vec![Level::succ(Level::zero()), u(), u()],
            ),
            [
                self.e.term.clone(),
                self.v.term.clone(),
                ignored.lam(bool_ty()),
                error.lam(Expr::const_str("Bool.false")),
                value.lam(Expr::const_str("Bool.true")),
                status,
            ],
        )
    }

    fn dispatch(&self, sc: &mut Scope, state: Expr, status: Expr) -> Expr {
        let ignored = sc.local(outcome(&self.e.term, &self.v.term));
        let error = sc.local(self.e.term.clone());
        let value = sc.local(self.v.term.clone());
        outcome_cases(
            &self.e.term,
            &self.v.term,
            ignored.lam(self.a.term.clone()),
            error.lam(Expr::apps(
                self.err.term.clone(),
                [state.clone(), error.term.clone()],
            )),
            value.lam(Expr::apps(
                self.ok.term.clone(),
                [state, value.term.clone()],
            )),
            status,
            false,
        )
    }

    fn cleaned(&self, sc: &mut Scope, preserved: impl FnOnce(&mut Scope, Expr) -> Expr) -> Expr {
        let post = sc.local(self.s.term.clone());
        let result = sc.local(outcome(&self.e.term, &self.v.term));
        let yes = preserved(sc, post.term.clone());
        let no = self.dispatch(sc, post.term.clone(), result.term.clone());
        let test = self.success(sc, result.term.clone());
        let body = self.choose(sc, test, yes, no);
        Expr::apps(
            self.cleanup.term.clone(),
            [self.state.term.clone(), lams(&[post, result], body)],
        )
    }

    fn body(&self, sc: &mut Scope, decode_first: bool) -> Expr {
        let original = self.original.term.clone();
        let no = if decode_first {
            let ignored = sc.local(outcome(&self.e.term, &self.v.term));
            let error = sc.local(self.e.term.clone());
            let value = sc.local(self.v.term.clone());
            let failed = self.cleaned(sc, |_, post| {
                Expr::apps(self.err.term.clone(), [post, error.term.clone()])
            });
            let normal = self.cleaned(sc, |_, post| {
                Expr::apps(self.ok.term.clone(), [post, value.term.clone()])
            });
            outcome_cases(
                &self.e.term,
                &self.v.term,
                ignored.lam(self.a.term.clone()),
                error.lam(failed),
                value.lam(normal),
                original.clone(),
                false,
            )
        } else {
            self.cleaned(sc, |sc, post| self.dispatch(sc, post, original.clone()))
        };
        let test = self.success(sc, original.clone());
        let yes = Expr::apps(self.yes.term.clone(), [self.state.term.clone(), original]);
        self.choose(sc, test, yes, no)
    }
}

fn endpoint(env: &mut Environment, decode_first: bool) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let t = Terms::new(&mut sc);
    let body = t.body(&mut sc, decode_first);
    add(
        env,
        if decode_first {
            GUARDED_CLEANUP_DECODE_FIRST
        } else {
            GUARDED_CLEANUP_RAW_FIRST
        },
        &t.parameters(),
        t.a.term,
        body,
        false,
    )
}

fn theorem(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let t = Terms::new(&mut sc);
    let statement = |q: Expr| {
        eq(
            &t.a.term,
            t.call(GUARDED_CLEANUP_DECODE_FIRST, q.clone()),
            t.call(GUARDED_CLEANUP_RAW_FIRST, q),
        )
    };
    let subject = sc.local(outcome(&t.e.term, &t.v.term));
    let error = sc.local(t.e.term.clone());
    let value = sc.local(t.v.term.clone());
    let failed = apps(
        "Except.error",
        [t.e.term.clone(), t.v.term.clone(), error.term.clone()],
    );
    let normal = apps(
        "Except.ok",
        [t.e.term.clone(), t.v.term.clone(), value.term.clone()],
    );
    let proof = outcome_cases(
        &t.e.term,
        &t.v.term,
        subject.lam(statement(subject.term.clone())),
        error.lam(refl(&t.a.term, t.call(GUARDED_CLEANUP_RAW_FIRST, failed))),
        value.lam(refl(&t.a.term, t.call(GUARDED_CLEANUP_RAW_FIRST, normal))),
        t.original.term.clone(),
        true,
    );
    add(
        env,
        GUARDED_RAW_CLEANUP,
        &t.parameters(),
        statement(t.original.term.clone()),
        proof,
        true,
    )
}

#[cfg(test)]
#[path = "semantic_evaluation_guarded_cleanup_tests.rs"]
mod tests;
