// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Symbolic finite index-to-value enumeration, with no source or cursor claim.
//!
//! `enumerate A f n` contains `f 0, ..., f (n-1)`, including repeats. The
//! indexed law uses the canonical Boolean strict bound `Nat.ble (succ k) n`.
//! No injectivity, provider readiness, physical materialization or loop/source
//! correspondence is assumed. Existing Domain membership/coverage/end laws
//! apply to this actual list, without changing any earlier declaration.
use super::*;

pub const DOMAIN_ENUMERATE: &str = "TrustIR.Eval.Domain.enumerate";
pub const DOMAIN_ENUMERATE_LENGTH: &str = "TrustIR.Eval.Domain.enumerate_length";
pub const DOMAIN_ENUMERATE_AT: &str = "TrustIR.Eval.Domain.enumerate_at";
pub const DOMAIN_ENUMERATE_SOME: &str = "TrustIR.Eval.Domain.enumerate_some";
pub const DOMAIN_ENUMERATE_NONE: &str = "TrustIR.Eval.Domain.enumerate_none";
pub const DOMAIN_ENUMERATE_END: &str = "TrustIR.Eval.Domain.enumerate_end";
const NAMES: [&str; 6] = [
    DOMAIN_ENUMERATE,
    DOMAIN_ENUMERATE_LENGTH,
    DOMAIN_ENUMERATE_AT,
    DOMAIN_ENUMERATE_SOME,
    DOMAIN_ENUMERATE_NONE,
    DOMAIN_ENUMERATE_END,
];

fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn option(a: &Expr) -> Expr {
    Expr::app(c("Option"), a.clone())
}
fn none(a: &Expr) -> Expr {
    Expr::app(c("Option.none"), a.clone())
}
fn some(a: &Expr, value: Expr) -> Expr {
    Expr::apps(c("Option.some"), [a.clone(), value])
}
fn enumerate(a: &Expr, f: Expr, n: Expr) -> Expr {
    Expr::apps(c(DOMAIN_ENUMERATE), [a.clone(), f, n])
}
fn at(a: &Expr, xs: Expr, k: Expr) -> Expr {
    Expr::apps(c(DOMAIN_AT), [a.clone(), xs, k])
}
fn within(k: Expr, n: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.ble"), [successor(k), n])
}
fn flag(value: bool) -> Expr {
    Expr::const_str(if value { "Bool.true" } else { "Bool.false" })
}
fn choose_option(a: &Expr, test: Expr, value: Expr) -> Expr {
    bool_cases(
        Expr::lam(BinderInfo::Default, bool_ty(), option(a)),
        none(a),
        some(a, value),
        test,
        false,
    )
}
fn bool_eq(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [bool_ty(), left, right],
    )
}
fn nat_eq(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), left, right],
    )
}
fn nat_refl(value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), value],
    )
}
fn congr_small(input: Expr, output: Expr, left: Expr, right: Expr, f: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(u())],
        ),
        [input, output, left, right, f, h],
    )
}

/// Extend an existing indexed Domain environment. Collisions refuse before
/// mutation; discard the environment on any later error. Only new definitions
/// and proved laws are added; existing declaration bodies/options are retained.
pub fn install_enumerated_domain_into(
    env: &mut Environment,
) -> Result<(), SemanticEvaluationError> {
    for name in NAMES {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    recheck_theorem(env, DOMAIN_AT_SOUND)?;
    recheck_theorem(env, DOMAIN_AT_COVER)?;
    recheck_theorem(env, DOMAIN_AT_END)?;
    env.init_list_contains()
        .map_err(|e| error(DOMAIN_ENUMERATE, e))?;
    definition(env)?;
    length_law(env)?;
    indexed_law(env)?;
    bounded_law(env, true)?;
    bounded_law(env, false)?;
    end_law(env)?;
    for name in &NAMES[1..] {
        recheck_theorem(env, name)?;
    }
    Ok(())
}

fn definition(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [a] = sc.types();
    let f = sc.local(Expr::arrow(nat(), a.term.clone()));
    let count = sc.local(nat());
    let n = sc.local(nat());
    let previous = sc.local(Expr::arrow(f.ty.clone(), list(&a.term)));
    let current = sc.local(f.ty.clone());
    let k = sc.local(nat());
    let shifted = k.lam(Expr::app(current.term.clone(), successor(k.term.clone())));
    let body = Expr::apps(
        c("List.cons"),
        [
            a.term.clone(),
            Expr::app(current.term.clone(), Expr::nat_lit(0)),
            Expr::app(previous.term.clone(), shifted),
        ],
    );
    let index = sc.local(nat());
    let zero_f = sc.local(f.ty.clone());
    let recursion = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(u())]),
        [
            index.lam(Expr::arrow(f.ty.clone(), list(&a.term))),
            zero_f.lam(Expr::app(c("List.nil"), a.term.clone())),
            lams(&[n, previous, current], body),
            count.term.clone(),
        ],
    );
    add(
        env,
        DOMAIN_ENUMERATE,
        &[a.clone(), f.clone(), count],
        list(&a.term),
        Expr::app(recursion, f.term),
        false,
    )
}

fn length_law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [a] = sc.types();
    let f = sc.local(Expr::arrow(nat(), a.term.clone()));
    let count = sc.local(nat());
    let statement = |f: Expr, n: Expr| nat_eq(length(&a.term, enumerate(&a.term, f, n.clone())), n);
    let zero_f = sc.local(f.ty.clone());
    let zero = zero_f.lam(nat_refl(Expr::nat_lit(0)));
    let n = sc.local(nat());
    let any_f = sc.local(f.ty.clone());
    let ih = sc.local(any_f.pi(statement(any_f.term.clone(), n.term.clone())));
    let current = sc.local(f.ty.clone());
    let k = sc.local(nat());
    let shifted = k.lam(Expr::app(current.term.clone(), successor(k.term.clone())));
    let before = length(&a.term, enumerate(&a.term, shifted.clone(), n.term.clone()));
    let x = sc.local(nat());
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()); 2],
        ),
        [
            nat(),
            nat(),
            before,
            n.term.clone(),
            x.lam(successor(x.term.clone())),
            Expr::app(ih.term.clone(), shifted),
        ],
    );
    let index = sc.local(nat());
    let any_f = sc.local(f.ty.clone());
    let recursion = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [
            index.lam(any_f.pi(statement(any_f.term.clone(), index.term.clone()))),
            zero,
            lams(&[n, ih, current], proof),
            count.term.clone(),
            f.term.clone(),
        ],
    );
    add(
        env,
        DOMAIN_ENUMERATE_LENGTH,
        &[a.clone(), f.clone(), count.clone()],
        statement(f.term, count.term),
        recursion,
        true,
    )
}

fn indexed_law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [a] = sc.types();
    let f = sc.local(Expr::arrow(nat(), a.term.clone()));
    let count = sc.local(nat());
    let k = sc.local(nat());
    let statement = |f: Expr, n: Expr, k: Expr| {
        eq(
            &option(&a.term),
            at(&a.term, enumerate(&a.term, f.clone(), n.clone()), k.clone()),
            choose_option(&a.term, within(k.clone(), n), Expr::app(f, k)),
        )
    };
    let zero_f = sc.local(f.ty.clone());
    let zero_k = sc.local(nat());
    let zero = lams(&[zero_f, zero_k], refl(&option(&a.term), none(&a.term)));
    let n = sc.local(nat());
    let any_f = sc.local(f.ty.clone());
    let any_k = sc.local(nat());
    let ih = sc.local(any_f.pi(any_k.pi(statement(
        any_f.term.clone(),
        n.term.clone(),
        any_k.term.clone(),
    ))));
    let current = sc.local(f.ty.clone());
    let index = sc.local(nat());
    let j = sc.local(nat());
    let unused = sc.local(statement(
        current.term.clone(),
        successor(n.term.clone()),
        j.term.clone(),
    ));
    let shift_k = sc.local(nat());
    let shifted = shift_k.lam(Expr::app(
        current.term.clone(),
        successor(shift_k.term.clone()),
    ));
    let inner = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [
            index.lam(statement(
                current.term.clone(),
                successor(n.term.clone()),
                index.term.clone(),
            )),
            refl(
                &option(&a.term),
                some(&a.term, Expr::app(current.term.clone(), Expr::nat_lit(0))),
            ),
            lams(
                &[j.clone(), unused],
                Expr::apps(ih.term.clone(), [shifted, j.term]),
            ),
            k.term.clone(),
        ],
    );
    let n_index = sc.local(nat());
    let any_f = sc.local(f.ty.clone());
    let any_k = sc.local(nat());
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [
            n_index.lam(any_f.pi(any_k.pi(statement(
                any_f.term.clone(),
                n_index.term.clone(),
                any_k.term.clone(),
            )))),
            zero,
            lams(&[n, ih, current, k.clone()], inner),
            count.term.clone(),
            f.term.clone(),
            k.term.clone(),
        ],
    );
    add(
        env,
        DOMAIN_ENUMERATE_AT,
        &[a.clone(), f.clone(), count.clone(), k.clone()],
        statement(f.term, count.term, k.term),
        proof,
        true,
    )
}

fn bounded_law(env: &mut Environment, inside: bool) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [a] = sc.types();
    let f = sc.local(Expr::arrow(nat(), a.term.clone()));
    let n = sc.local(nat());
    let k = sc.local(nat());
    let test = within(k.term.clone(), n.term.clone());
    let h = sc.local(bool_eq(test.clone(), flag(inside)));
    let value = Expr::app(f.term.clone(), k.term.clone());
    let actual = at(
        &a.term,
        enumerate(&a.term, f.term.clone(), n.term.clone()),
        k.term.clone(),
    );
    let middle = choose_option(&a.term, test.clone(), value.clone());
    let expected = if inside {
        some(&a.term, value.clone())
    } else {
        none(&a.term)
    };
    let b = sc.local(bool_ty());
    let mapped = congr_small(
        bool_ty(),
        option(&a.term),
        test,
        flag(inside),
        b.lam(choose_option(&a.term, b.term.clone(), value)),
        h.term.clone(),
    );
    let first = Expr::apps(
        c(DOMAIN_ENUMERATE_AT),
        [
            a.term.clone(),
            f.term.clone(),
            n.term.clone(),
            k.term.clone(),
        ],
    );
    let proof = trans(
        &option(&a.term),
        actual.clone(),
        middle,
        expected.clone(),
        first,
        mapped,
    );
    add(
        env,
        if inside {
            DOMAIN_ENUMERATE_SOME
        } else {
            DOMAIN_ENUMERATE_NONE
        },
        &[a.clone(), f, n, k, h],
        eq(&option(&a.term), actual, expected),
        proof,
        true,
    )
}

fn end_law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [a] = sc.types();
    let f = sc.local(Expr::arrow(nat(), a.term.clone()));
    let n = sc.local(nat());
    let values = enumerate(&a.term, f.term.clone(), n.term.clone());
    let size = length(&a.term, values.clone());
    let at_size = at(&a.term, values.clone(), size.clone());
    let at_count = at(&a.term, values.clone(), n.term.clone());
    let index = sc.local(nat());
    let mapped = congr_small(
        nat(),
        option(&a.term),
        size,
        n.term.clone(),
        index.lam(at(&a.term, values.clone(), index.term.clone())),
        Expr::apps(
            c(DOMAIN_ENUMERATE_LENGTH),
            [a.term.clone(), f.term.clone(), n.term.clone()],
        ),
    );
    let reversed = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(u())]),
        [option(&a.term), at_size.clone(), at_count.clone(), mapped],
    );
    let end = Expr::apps(c(DOMAIN_AT_END), [a.term.clone(), values]);
    let proof = trans(
        &option(&a.term),
        at_count.clone(),
        at_size,
        none(&a.term),
        reversed,
        end,
    );
    add(
        env,
        DOMAIN_ENUMERATE_END,
        &[a.clone(), f, n],
        eq(&option(&a.term), at_count, none(&a.term)),
        proof,
        true,
    )
}

#[cfg(test)]
#[path = "semantic_evaluation_domain_enumeration/tests.rs"]
mod tests;
