// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Pointwise nondependent data-case composition. The fixed checked proof keeps
//! large consumer branch terms out of repeated equality motives. This is not
//! function extensionality, a CPS converse, provider fidelity or CFG admission.
use super::*;
pub const CASE_MAP_PROD: &str = "TrustIR.Eval.CaseMap.prod";
pub const CASE_MAP_EXCEPT: &str = "TrustIR.Eval.CaseMap.except";
pub const CASE_MAP_OPTION: &str = "TrustIR.Eval.CaseMap.option";
pub const CASE_MAP_BOOL: &str = "TrustIR.Eval.CaseMap.bool";
pub const CASE_MAP_THEOREMS: [&str; 4] = [
    CASE_MAP_PROD,
    CASE_MAP_EXCEPT,
    CASE_MAP_OPTION,
    CASE_MAP_BOOL,
];

/// All data and result types use the same universe `u`. A later failure leaves
/// an extended untrusted environment which must be discarded by its caller.
pub fn install_case_maps_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in CASE_MAP_THEOREMS {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    env.init_prod().map_err(|e| error(CASE_MAP_PROD, e))?;
    env.init_except_t().map_err(|e| error(CASE_MAP_EXCEPT, e))?;
    env.init_option().map_err(|e| error(CASE_MAP_OPTION, e))?;
    env.init_bool().map_err(|e| error(CASE_MAP_BOOL, e))?;
    for (family, name) in CASE_MAP_THEOREMS.into_iter().enumerate() {
        install_one(env, family, name)?;
        recheck_theorem(env, name)?;
    }
    Ok(())
}
fn install_one(
    env: &mut Environment,
    family: usize,
    name: &str,
) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let count = match family {
        0 | 1 => 2,
        2 => 1,
        _ => 0,
    };
    let data = (0..count).map(|_| sc.local(type_u())).collect::<Vec<_>>();
    let data_terms = data.iter().map(|l| l.term.clone()).collect::<Vec<_>>();
    let (recursor, data_type, fields) = match family {
        0 => (
            "Prod.rec",
            prod(&data[0].term, &data[1].term),
            vec![vec![data[0].term.clone(), data[1].term.clone()]],
        ),
        1 => (
            "Except.rec",
            outcome(&data[0].term, &data[1].term),
            vec![vec![data[0].term.clone()], vec![data[1].term.clone()]],
        ),
        2 => (
            "Option.rec",
            Expr::app(c("Option"), data[0].term.clone()),
            vec![vec![], vec![data[0].term.clone()]],
        ),
        _ => ("Bool.rec", bool_ty(), vec![vec![], vec![]]),
    };
    let [observed, answer] = sc.types();
    let mapper = sc.local(Expr::arrow(observed.term.clone(), answer.term.clone()));
    let arrow = |fields: &[Expr], result: Expr| {
        fields
            .iter()
            .rev()
            .fold(result, |body, ty| Expr::arrow(ty.clone(), body))
    };
    let sources = fields
        .iter()
        .map(|f| sc.local(arrow(f, answer.term.clone())))
        .collect::<Vec<_>>();
    let observations = fields
        .iter()
        .map(|f| sc.local(arrow(f, observed.term.clone())))
        .collect::<Vec<_>>();
    let mut hypotheses = Vec::new();
    for (i, types) in fields.iter().enumerate() {
        let locals = types
            .iter()
            .cloned()
            .map(|ty| sc.local(ty))
            .collect::<Vec<_>>();
        let args = locals.iter().map(|l| l.term.clone()).collect::<Vec<_>>();
        let statement = eq(
            &answer.term,
            Expr::apps(sources[i].term.clone(), args.clone()),
            Expr::app(
                mapper.term.clone(),
                Expr::apps(observations[i].term.clone(), args),
            ),
        );
        hypotheses.push(sc.local(pis(&locals, statement)));
    }
    let motive = sc.local(data_type.clone());
    let cases = |result: &Expr, arms: &[Local], major: Expr| {
        let mut args = data_terms.clone();
        args.push(motive.lam(result.clone()));
        args.extend(arms.iter().map(|l| l.term.clone()));
        args.push(major);
        let mut levels = vec![Level::succ(u())];
        levels.extend((0..count).map(|_| u()));
        Expr::apps(Expr::const_(Name::from_string(recursor), levels), args)
    };
    let equation = |major: Expr| {
        eq(
            &answer.term,
            cases(&answer.term, &sources, major.clone()),
            Expr::app(
                mapper.term.clone(),
                cases(&observed.term, &observations, major),
            ),
        )
    };
    let major = sc.local(data_type.clone());
    let proof_motive = sc.local(data_type);
    let mut proof_args = data_terms.clone();
    proof_args.push(proof_motive.lam(equation(proof_motive.term.clone())));
    for (i, types) in fields.iter().enumerate() {
        let locals = types
            .iter()
            .cloned()
            .map(|ty| sc.local(ty))
            .collect::<Vec<_>>();
        let applied = Expr::apps(
            hypotheses[i].term.clone(),
            locals.iter().map(|l| l.term.clone()),
        );
        proof_args.push(lams(&locals, applied));
    }
    proof_args.push(major.term.clone());
    let mut proof_levels = vec![Level::zero()];
    proof_levels.extend((0..count).map(|_| u()));
    let proof = Expr::apps(
        Expr::const_(Name::from_string(recursor), proof_levels),
        proof_args,
    );
    let statement = equation(major.term.clone());
    let mut parameters = data;
    parameters.extend([observed, answer, mapper]);
    parameters.extend(sources);
    parameters.extend(observations);
    parameters.extend(hypotheses);
    parameters.push(major);
    add(env, name, &parameters, statement, proof, true)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn case_map_composition_is_kernel_checked_and_rooted_audited() {
        let mut env = build_environment().unwrap();
        install_case_maps_into(&mut env).unwrap();
        for name in CASE_MAP_THEOREMS {
            recheck_theorem(&env, name).unwrap();
        }
        let count = env.num_constants();
        assert!(install_case_maps_into(&mut env).is_err());
        assert_eq!(count, env.num_constants());
    }
    #[test]
    fn case_map_last_owned_name_collision_refuses_before_mutation() {
        let mut env = build_environment().unwrap();
        let ty = Expr::const_str("Bool");
        let value = Expr::const_str("Bool.false");
        let statement = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [ty.clone(), value.clone(), value.clone()],
        );
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [ty, value],
        );
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(CASE_MAP_BOOL),
            level_params: vec![],
            type_: statement,
            value: proof,
        })
        .unwrap();
        let count = env.num_constants();
        assert!(install_case_maps_into(&mut env).is_err());
        assert_eq!(count, env.num_constants());
        assert!(env.get_const(&Name::from_string(CASE_MAP_PROD)).is_none());
    }
}

/// The branch premise quantifies the entire recursive observation. This is a
/// sufficient invariant, never an assumption that recursive data already has
/// the desired projection. Consumers retaining recursive data must prove more.
pub const LIST_PROJECTION: &str = "TrustIR.Eval.CaseMap.list_projection";
pub fn install_list_projection_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    if env.get_const(&Name::from_string(LIST_PROJECTION)).is_some() {
        return Err(error(LIST_PROJECTION, "owned declaration already exists"));
    }
    env.init_list().map_err(|e| error(LIST_PROJECTION, e))?;
    let mut sc = Scope::default();
    let [a, b, c] = sc.types();
    let list = Expr::app(c_("List"), a.term.clone());
    let project = sc.local(Expr::arrow(b.term.clone(), c.term.clone()));
    let expected = sc.local(c.term.clone());
    let zero = sc.local(b.term.clone());
    let step = sc.local(Expr::arrow(
        a.term.clone(),
        Expr::arrow(list.clone(), Expr::arrow(b.term.clone(), b.term.clone())),
    ));
    let base = sc.local(eq(
        &c.term,
        Expr::app(project.term.clone(), zero.term.clone()),
        expected.term.clone(),
    ));
    let head = sc.local(a.term.clone());
    let tail = sc.local(list.clone());
    let previous = sc.local(b.term.clone());
    let branch = sc.local(pis(
        &[head.clone(), tail.clone(), previous.clone()],
        eq(
            &c.term,
            Expr::app(
                project.term.clone(),
                Expr::apps(
                    step.term.clone(),
                    [head.term.clone(), tail.term.clone(), previous.term.clone()],
                ),
            ),
            expected.term.clone(),
        ),
    ));
    let ignored = sc.local(list.clone());
    let fold = |xs| {
        Expr::apps(
            Expr::const_(Name::from_string("List.rec"), vec![Level::succ(u()), u()]),
            [
                a.term.clone(),
                ignored.lam(b.term.clone()),
                zero.term.clone(),
                step.term.clone(),
                xs,
            ],
        )
    };
    let statement = |xs| {
        eq(
            &c.term,
            Expr::app(project.term.clone(), fold(xs)),
            expected.term.clone(),
        )
    };
    let major = sc.local(list.clone());
    let motive = sc.local(list.clone());
    let ih = sc.local(statement(tail.term.clone()));
    let next = lams(
        &[head.clone(), tail.clone(), ih],
        Expr::apps(
            branch.term.clone(),
            [head.term, tail.term.clone(), fold(tail.term)],
        ),
    );
    let proof = Expr::apps(
        Expr::const_(Name::from_string("List.rec"), vec![Level::zero(), u()]),
        [
            a.term.clone(),
            motive.lam(statement(motive.term.clone())),
            base.term.clone(),
            next,
            major.term.clone(),
        ],
    );
    let proposition = statement(major.term.clone());
    add(
        env,
        LIST_PROJECTION,
        &[a, b, c, project, expected, zero, step, base, branch, major],
        proposition,
        proof,
        true,
    )?;
    recheck_theorem(env, LIST_PROJECTION)
}
fn c_(name: &str) -> Expr {
    c(name)
}

#[cfg(test)]
#[test]
fn case_map_list_projection_is_checked_with_unrestricted_recursive_observation() {
    let mut env = build_environment().unwrap();
    install_list_projection_into(&mut env).unwrap();
    recheck_theorem(&env, LIST_PROJECTION).unwrap();
    let count = env.num_constants();
    assert!(install_list_projection_into(&mut env).is_err());
    assert_eq!(count, env.num_constants());
}
