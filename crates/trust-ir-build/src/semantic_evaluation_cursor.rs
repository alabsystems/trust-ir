// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Indexed immutable-domain reads, matching a prepared backing plus position.
//! Coverage uses the existing kernel List.Mem inductive. No domain data,
//! successful preparation or physical cursor fidelity is assumed here.
use super::*;

pub const DOMAIN_AT: &str = "TrustIR.Eval.Domain.at";
pub const DOMAIN_AT_MEMBERS: &str = "TrustIR.Eval.Domain.at_members";
pub const DOMAIN_AT_SOUND: &str = "TrustIR.Eval.Domain.at_sound";
pub const DOMAIN_AT_COVER: &str = "TrustIR.Eval.Domain.at_cover";
pub const DOMAIN_AT_END: &str = "TrustIR.Eval.Domain.at_end";

fn option(a: &Expr) -> Expr {
    Expr::app(c("Option"), a.clone())
}
fn none(a: &Expr) -> Expr {
    Expr::app(c("Option.none"), a.clone())
}
fn some(a: &Expr, x: Expr) -> Expr {
    Expr::apps(c("Option.some"), [a.clone(), x])
}
fn cons(a: &Expr, x: Expr, xs: Expr) -> Expr {
    Expr::apps(c("List.cons"), [a.clone(), x, xs])
}
fn mem(a: &Expr, x: Expr, xs: Expr) -> Expr {
    Expr::apps(c("List.Mem"), [a.clone(), x, xs])
}
fn at(a: &Expr, xs: Expr, n: Expr) -> Expr {
    Expr::apps(c(DOMAIN_AT), [a.clone(), xs, n])
}
fn members(a: &Expr, xs: Expr, o: Expr) -> Expr {
    Expr::apps(c(DOMAIN_AT_MEMBERS), [a.clone(), xs, o])
}
fn option_rec(a: &Expr, motive: Expr, zero: Expr, next: Expr, o: Expr, level: Level) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Option.rec"), vec![level, u()]),
        [a.clone(), motive, zero, next, o],
    )
}
fn exists(predicate: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Nat"), predicate],
    )
}
fn witness(predicate: Expr, n: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Exists.intro"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Nat"), predicate, n, proof],
    )
}

fn install_at(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [a] = sc.types();
    let xs = sc.local(list(&a.term));
    let n = sc.local(Expr::const_str("Nat"));
    let ignored = sc.local(list(&a.term));
    let head = sc.local(a.term.clone());
    let tail = sc.local(list(&a.term));
    let previous = sc.local(Expr::arrow(n.ty.clone(), option(&a.term)));
    let index = sc.local(n.ty.clone());
    let k = sc.local(n.ty.clone());
    let unused = sc.local(option(&a.term));
    let next = lams(
        &[head.clone(), tail, previous.clone(), n.clone()],
        Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(u())]),
            [
                index.lam(option(&a.term)),
                some(&a.term, head.term),
                lams(&[k.clone(), unused], Expr::app(previous.term, k.term)),
                n.term.clone(),
            ],
        ),
    );
    let value = list_rec(
        &a.term,
        ignored.lam(Expr::arrow(n.ty.clone(), option(&a.term))),
        n.lam(none(&a.term)),
        next,
        xs.term.clone(),
        Level::succ(u()),
    );
    add(
        env,
        DOMAIN_AT,
        &[a.clone(), xs],
        Expr::arrow(Expr::const_str("Nat"), option(&a.term)),
        value,
        false,
    )
}

fn install_members(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [a] = sc.types();
    let xs = sc.local(list(&a.term));
    let o = sc.local(option(&a.term));
    let ignored = sc.local(o.ty.clone());
    let x = sc.local(a.term.clone());
    let term = option_rec(
        &a.term,
        ignored.lam(Expr::sort(Level::zero())),
        Expr::const_str("True"),
        x.lam(mem(&a.term, x.term.clone(), xs.term.clone())),
        o.term.clone(),
        Level::succ(Level::zero()),
    );
    add(
        env,
        DOMAIN_AT_MEMBERS,
        &[a, xs, o],
        Expr::sort(Level::zero()),
        term,
        false,
    )
}

fn install_sound(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [a] = sc.types();
    let xs = sc.local(list(&a.term));
    let n = sc.local(Expr::const_str("Nat"));
    let statement = |xs: Expr, n: Expr| members(&a.term, xs.clone(), at(&a.term, xs, n));
    let zero = n.lam(Expr::const_str("True.intro"));
    let head = sc.local(a.term.clone());
    let tail = sc.local(list(&a.term));
    let k = sc.local(n.ty.clone());
    let ih = sc.local(k.pi(statement(tail.term.clone(), k.term.clone())));
    let index = sc.local(n.ty.clone());
    let next_index = sc.local(n.ty.clone());
    let unused = sc.local(statement(
        cons(&a.term, head.term.clone(), tail.term.clone()),
        next_index.term.clone(),
    ));
    let o = sc.local(option(&a.term));
    let h = sc.local(members(&a.term, tail.term.clone(), o.term.clone()));
    let x = sc.local(a.term.clone());
    let hx = sc.local(mem(&a.term, x.term.clone(), tail.term.clone()));
    let yes = sc.local(Expr::const_str("True"));
    let lifted = Expr::app(
        option_rec(
            &a.term,
            o.lam(h.pi(members(
                &a.term,
                cons(&a.term, head.term.clone(), tail.term.clone()),
                o.term.clone(),
            ))),
            yes.lam(Expr::const_str("True.intro")),
            lams(
                &[x.clone(), hx.clone()],
                Expr::apps(
                    c("List.Mem.tail"),
                    [
                        a.term.clone(),
                        x.term,
                        head.term.clone(),
                        tail.term.clone(),
                        hx.term,
                    ],
                ),
            ),
            at(&a.term, tail.term.clone(), next_index.term.clone()),
            Level::zero(),
        ),
        Expr::app(ih.term.clone(), next_index.term.clone()),
    );
    let nat_motive = index.lam(statement(
        cons(&a.term, head.term.clone(), tail.term.clone()),
        index.term.clone(),
    ));
    let next = lams(
        &[head.clone(), tail.clone(), ih, n.clone()],
        Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [
                nat_motive,
                Expr::apps(c("List.Mem.head"), [a.term.clone(), head.term, tail.term]),
                lams(&[next_index, unused], lifted),
                n.term.clone(),
            ],
        ),
    );
    let index = sc.local(list(&a.term));
    let input = sc.local(Expr::const_str("Nat"));
    let motive = index.lam(input.pi(statement(index.term.clone(), input.term.clone())));
    let proof = Expr::app(
        list_rec(&a.term, motive, zero, next, xs.term.clone(), Level::zero()),
        n.term.clone(),
    );
    add(
        env,
        DOMAIN_AT_SOUND,
        &[a.clone(), xs.clone(), n.clone()],
        statement(xs.term, n.term),
        proof,
        true,
    )
}

fn install_cover(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [a] = sc.types();
    let x = sc.local(a.term.clone());
    let xs = sc.local(list(&a.term));
    let h = sc.local(mem(&a.term, x.term.clone(), xs.term.clone()));
    let index = sc.local(Expr::const_str("Nat"));
    let predicate = |xs: Expr| {
        index.lam(eq(
            &option(&a.term),
            at(&a.term, xs, index.term.clone()),
            some(&a.term, x.term.clone()),
        ))
    };
    let tail = sc.local(list(&a.term));
    let head_case = tail.lam(witness(
        predicate(cons(&a.term, x.term.clone(), tail.term.clone())),
        Expr::nat_lit(0),
        refl(&option(&a.term), some(&a.term, x.term.clone())),
    ));
    let head = sc.local(a.term.clone());
    let tail_h = sc.local(mem(&a.term, x.term.clone(), tail.term.clone()));
    let ih = sc.local(exists(predicate(tail.term.clone())));
    let n = sc.local(Expr::const_str("Nat"));
    let answer = sc.local(eq(
        &option(&a.term),
        at(&a.term, tail.term.clone(), n.term.clone()),
        some(&a.term, x.term.clone()),
    ));
    let conclusion = exists(predicate(cons(
        &a.term,
        head.term.clone(),
        tail.term.clone(),
    )));
    let transferred = lams(
        &[n.clone(), answer.clone()],
        witness(
            predicate(cons(&a.term, head.term.clone(), tail.term.clone())),
            successor(n.term),
            answer.term,
        ),
    );
    let tail_case = lams(
        &[head, tail.clone(), tail_h, ih.clone()],
        Expr::apps(
            Expr::const_(
                Name::from_string("Exists.elim"),
                vec![Level::succ(Level::zero())],
            ),
            [
                Expr::const_str("Nat"),
                predicate(tail.term.clone()),
                conclusion,
                ih.term,
                transferred,
            ],
        ),
    );
    let current = sc.local(list(&a.term));
    let membership = sc.local(mem(&a.term, x.term.clone(), current.term.clone()));
    let motive = current.lam(membership.lam(exists(predicate(current.term.clone()))));
    let proof = Expr::apps(
        c("List.Mem.rec"),
        [
            a.term.clone(),
            x.term.clone(),
            motive,
            head_case,
            tail_case,
            xs.term.clone(),
            h.term.clone(),
        ],
    );
    add(
        env,
        DOMAIN_AT_COVER,
        &[a.clone(), x.clone(), xs.clone(), h],
        exists(predicate(xs.term)),
        proof,
        true,
    )
}

fn install_end(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [a] = sc.types();
    let xs = sc.local(list(&a.term));
    let statement = |xs: Expr| {
        eq(
            &option(&a.term),
            at(&a.term, xs.clone(), length(&a.term, xs)),
            none(&a.term),
        )
    };
    let head = sc.local(a.term.clone());
    let tail = sc.local(list(&a.term));
    let ih = sc.local(statement(tail.term.clone()));
    let input = sc.local(list(&a.term));
    let proof = list_rec(
        &a.term,
        input.lam(statement(input.term.clone())),
        refl(&option(&a.term), none(&a.term)),
        lams(&[head, tail, ih.clone()], ih.term),
        xs.term.clone(),
        Level::zero(),
    );
    add(
        env,
        DOMAIN_AT_END,
        &[a.clone(), xs.clone()],
        statement(xs.term),
        proof,
        true,
    )
}

pub fn install_indexed_domain_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in [
        DOMAIN_AT,
        DOMAIN_AT_MEMBERS,
        DOMAIN_AT_SOUND,
        DOMAIN_AT_COVER,
        DOMAIN_AT_END,
    ] {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    install_domain_into(env)?;
    env.init_option().map_err(|e| error(DOMAIN_AT, e))?;
    env.init_true_false().map_err(|e| error(DOMAIN_AT, e))?;
    env.init_list_mem().map_err(|e| error(DOMAIN_AT, e))?;
    env.init_exists().map_err(|e| error(DOMAIN_AT, e))?;
    install_at(env)?;
    install_members(env)?;
    install_sound(env)?;
    install_cover(env)?;
    install_end(env)?;
    for name in [DOMAIN_AT_SOUND, DOMAIN_AT_COVER, DOMAIN_AT_END] {
        recheck_theorem(env, name)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn indexed_domain_membership_coverage_and_end_are_kernel_checked() {
        let mut env = Environment::default();
        install_indexed_domain_into(&mut env).unwrap();
        for name in [DOMAIN_AT_SOUND, DOMAIN_AT_COVER, DOMAIN_AT_END] {
            recheck_theorem(&env, name).unwrap();
        }
    }
}

#[cfg(test)]
mod hostile_tests {
    use super::*;
    fn z(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string(name), vec![Level::zero()]),
            args,
        )
    }
    #[test]
    fn indexed_domain_wrong_member_index_and_exhaustion_are_well_typed_but_rejected() {
        let mut env = Environment::default();
        install_indexed_domain_into(&mut env).unwrap();
        let nat = Expr::const_str("Nat");
        let xs = z(
            "List.cons",
            [
                nat.clone(),
                Expr::nat_lit(0),
                z(
                    "List.cons",
                    [nat.clone(), Expr::nat_lit(1), z("List.nil", [nat.clone()])],
                ),
            ],
        );
        let opt = z("Option", [nat.clone()]);
        for (index, claimed) in [(0, Some(99)), (2, Some(0)), (1, None)] {
            let actual = z(DOMAIN_AT, [nat.clone(), xs.clone(), Expr::nat_lit(index)]);
            let proposed = match claimed {
                Some(n) => z("Option.some", [nat.clone(), Expr::nat_lit(n)]),
                None => z("Option.none", [nat.clone()]),
            };
            let goal = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [opt.clone(), actual, proposed.clone()],
            );
            let proof = Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [opt.clone(), proposed],
            );
            let tc = TypeChecker::new(&env);
            let _checked_goal_type = tc.infer_type(&goal).unwrap();
            let _checked_proof_type = tc.infer_type(&proof).unwrap();
            assert!(tc.check_type(&proof, &goal).is_err());
        }
    }
}
