// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Pointwise callback transport through a genuine, explicitly proved CPS image.
//! The explicit image premise lets this rule transport pointwise callback
//! equality without function extensionality. No such transport or provider
//! fidelity is inferred from a callback type or a matching concrete execution.
use super::*;

pub const CPS_IMAGE_CALLBACK_CONGR: &str = "TrustIR.Eval.cps_image_callback_congr";

/// With `image : CpsImage S E V A run code`, pointwise equality of both
/// success callbacks and both error callbacks proves equality of the two
/// applications of `code` at the same input state. All fourteen arguments are
/// explicit: S, E, V, A, run, code, image, left_ok, right_ok, left_err,
/// right_err, same_ok, same_err, input. Returned state and payload are both
/// quantified by each callback premise; neither may be silently discarded.
/// Install after `install_handle_into`. A name collision or missing dependency
/// refuses before mutation; discard the environment on a later failure. No
/// existing declaration or proof policy changes.
pub fn install_image_callback_congruence_into(
    env: &mut Environment,
) -> Result<(), SemanticEvaluationError> {
    if env
        .get_const(&Name::from_string(CPS_IMAGE_CALLBACK_CONGR))
        .is_some()
    {
        return Err(error(
            CPS_IMAGE_CALLBACK_CONGR,
            "owned declaration already exists",
        ));
    }
    recheck_theorem(env, CPS_IMAGE_HANDLE)?;
    law(env)?;
    recheck_theorem(env, CPS_IMAGE_CALLBACK_CONGR)?;
    let name = Name::from_string(CPS_IMAGE_CALLBACK_CONGR);
    if !env.axiom_deps(&name).is_some_and(|deps| deps.is_empty())
        || !env
            .foundational_axiom_deps(&name)
            .is_some_and(|deps| deps.is_empty())
        || !env
            .trust_marker_deps(&name)
            .is_some_and(|deps| deps.is_empty())
    {
        return Err(error(
            CPS_IMAGE_CALLBACK_CONGR,
            "missing or nonempty axiom or trust-marker closure",
        ));
    }
    Ok(())
}

fn law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, r] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let code = sc.local(cps(&s.term, &e.term, &a.term, &r.term));
    let image = sc.local(apps(
        CPS_IMAGE,
        [
            s.term.clone(),
            e.term.clone(),
            a.term.clone(),
            r.term.clone(),
            m.term.clone(),
            code.term.clone(),
        ],
    ));
    let left_ok = sc.local(continuation(&s.term, &a.term, &r.term));
    let right_ok = sc.local(left_ok.ty.clone());
    let left_err = sc.local(continuation(&s.term, &e.term, &r.term));
    let right_err = sc.local(left_err.ty.clone());
    let post = sc.local(s.term.clone());
    let value = sc.local(a.term.clone());
    let failure = sc.local(e.term.clone());
    let same_ok = sc.local(pis(
        &[post.clone(), value.clone()],
        eq(
            &r.term,
            Expr::apps(
                left_ok.term.clone(),
                [post.term.clone(), value.term.clone()],
            ),
            Expr::apps(
                right_ok.term.clone(),
                [post.term.clone(), value.term.clone()],
            ),
        ),
    ));
    let same_err = sc.local(pis(
        &[post.clone(), failure.clone()],
        eq(
            &r.term,
            Expr::apps(
                left_err.term.clone(),
                [post.term.clone(), failure.term.clone()],
            ),
            Expr::apps(
                right_err.term.clone(),
                [post.term.clone(), failure.term.clone()],
            ),
        ),
    ));
    let input = sc.local(s.term.clone());
    let ignored = sc.local(s.term.clone());
    let converted = |computation: Expr, ok: Expr, err: Expr| {
        to_cps(
            &s.term,
            &e.term,
            &a.term,
            &r.term,
            computation,
            input.term.clone(),
            ok,
            err,
        )
    };
    let equation = |observed: Expr| {
        let computation = ignored.lam(observed);
        eq(
            &r.term,
            converted(
                computation.clone(),
                left_ok.term.clone(),
                left_err.term.clone(),
            ),
            converted(computation, right_ok.term.clone(), right_err.term.clone()),
        )
    };
    let through = prove_result_cases(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        Expr::app(m.term.clone(), input.term.clone()),
        equation,
        |post, error| Expr::apps(same_err.term.clone(), [post, error]),
        |post, value| Expr::apps(same_ok.term.clone(), [post, value]),
    );
    let left = Expr::apps(
        code.term.clone(),
        [
            input.term.clone(),
            left_ok.term.clone(),
            left_err.term.clone(),
        ],
    );
    let right = Expr::apps(
        code.term.clone(),
        [
            input.term.clone(),
            right_ok.term.clone(),
            right_err.term.clone(),
        ],
    );
    let middle_left = converted(m.term.clone(), left_ok.term.clone(), left_err.term.clone());
    let middle_right = converted(
        m.term.clone(),
        right_ok.term.clone(),
        right_err.term.clone(),
    );
    let first = Expr::apps(
        image.term.clone(),
        [
            input.term.clone(),
            left_ok.term.clone(),
            left_err.term.clone(),
        ],
    );
    let reverse_last = Expr::apps(
        image.term.clone(),
        [
            input.term.clone(),
            right_ok.term.clone(),
            right_err.term.clone(),
        ],
    );
    let last = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(u())]),
        [
            r.term.clone(),
            right.clone(),
            middle_right.clone(),
            reverse_last,
        ],
    );
    let proof = trans(
        &r.term,
        left.clone(),
        middle_left.clone(),
        right.clone(),
        first,
        trans(
            &r.term,
            middle_left,
            middle_right,
            right.clone(),
            through,
            last,
        ),
    );
    let goal = eq(&r.term, left, right);
    add(
        env,
        CPS_IMAGE_CALLBACK_CONGR,
        &[
            s, e, a, r, m, code, image, left_ok, right_ok, left_err, right_err, same_ok, same_err,
            input,
        ],
        goal,
        proof,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn environment() -> Environment {
        let mut env = build_environment().unwrap();
        install_handle_into(&mut env).unwrap();
        install_image_callback_congruence_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env
    }

    #[test]
    fn callback_congruence_requires_existing_image_and_preserves_old_declarations() {
        let mut missing = build_environment().unwrap();
        let count = missing.num_constants();
        assert!(install_image_callback_congruence_into(&mut missing).is_err());
        assert_eq!(count, missing.num_constants());
        let mut env = build_environment().unwrap();
        install_handle_into(&mut env).unwrap();
        let names = DEFINITIONS.iter().chain(THEOREMS).copied().chain([
            HANDLE,
            TO_CPS_HANDLE,
            CPS_IMAGE,
            CPS_IMAGE_HANDLE,
        ]);
        let before = names
            .map(|name| {
                let info = env.get_const(&Name::from_string(name)).unwrap();
                (
                    name,
                    (
                        trust_ir::proof::encode_clean_expr_dag_v2(&info.type_).unwrap(),
                        trust_ir::proof::encode_clean_expr_dag_v2(info.value.as_ref().unwrap())
                            .unwrap(),
                    ),
                )
            })
            .collect::<Vec<_>>();
        let old_count = env.num_constants();
        install_image_callback_congruence_into(&mut env).unwrap();
        assert_eq!(env.num_constants(), old_count + 1);
        for (name, bytes) in before {
            let info = env.get_const(&Name::from_string(name)).unwrap();
            assert_eq!(
                bytes,
                (
                    trust_ir::proof::encode_clean_expr_dag_v2(&info.type_).unwrap(),
                    trust_ir::proof::encode_clean_expr_dag_v2(info.value.as_ref().unwrap())
                        .unwrap(),
                )
            );
        }
        let count = env.num_constants();
        assert!(install_image_callback_congruence_into(&mut env).is_err());
        assert_eq!(count, env.num_constants());
        let name = Name::from_string(CPS_IMAGE_CALLBACK_CONGR);
        assert!(env.axiom_deps(&name).unwrap().is_empty());
        assert!(env.foundational_axiom_deps(&name).unwrap().is_empty());
        assert!(env.trust_marker_deps(&name).unwrap().is_empty());
        recheck_theorem(&env, CPS_IMAGE_CALLBACK_CONGR).unwrap();
        if let Some(path) = std::env::var_os("TRUST_IR_CPS_CALLBACK_ARTIFACT_DIR") {
            let path = std::path::PathBuf::from(path).join("generic-theorem");
            std::fs::create_dir_all(&path).unwrap();
            let info = env.get_const(&name).unwrap();
            std::fs::write(
                path.join("goal.bin"),
                trust_ir::proof::encode_clean_expr_dag_v2(&info.type_).unwrap(),
            )
            .unwrap();
            std::fs::write(
                path.join("proof.bin"),
                trust_ir::proof::encode_clean_expr_dag_v2(info.value.as_ref().unwrap()).unwrap(),
            )
            .unwrap();
            std::fs::write(path.join("verdict.txt"), "kernel checked; all three rooted closures empty; pointwise CPS image transport only").unwrap();
        }
    }

    fn bool_case(
        sc: &mut Scope,
        result: Expr,
        flag: Expr,
        no: Expr,
        yes: Expr,
        prop: bool,
    ) -> Expr {
        let ignored = sc.local(bool_ty());
        Expr::apps(
            Expr::const_(
                Name::from_string("Bool.rec"),
                vec![if prop {
                    Level::zero()
                } else {
                    Level::succ(u())
                }],
            ),
            [ignored.lam(result), no, yes, flag],
        )
    }

    /// These callbacks are pointwise equal by Bool elimination, but their
    /// function expressions are not definitionally equal on an unknown state.
    fn callback(sc: &mut Scope, error: bool) -> (Expr, Expr, Expr) {
        let nat = Expr::const_str("Nat");
        let state = sc.local(bool_ty());
        let payload = sc.local(nat.clone());
        let base = if error {
            Expr::app(Expr::const_str("Nat.succ"), payload.term.clone())
        } else {
            payload.term.clone()
        };
        let right_body = bool_case(
            sc,
            nat.clone(),
            state.term.clone(),
            base.clone(),
            Expr::app(Expr::const_str("Nat.succ"), base),
            false,
        );
        let left_body = bool_case(
            sc,
            nat.clone(),
            state.term.clone(),
            right_body.clone(),
            right_body.clone(),
            false,
        );
        let left = lams(&[state.clone(), payload.clone()], left_body);
        let right = lams(&[state.clone(), payload.clone()], right_body);
        let probe = sc.local(bool_ty());
        let statement = |flag: Expr| {
            eq(
                &nat,
                Expr::apps(left.clone(), [flag.clone(), payload.term.clone()]),
                Expr::apps(right.clone(), [flag, payload.term.clone()]),
            )
        };
        let motive = probe.lam(statement(probe.term.clone()));
        let branch = |flag: Expr| {
            refl(
                &nat,
                Expr::apps(right.clone(), [flag, payload.term.clone()]),
            )
        };
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            [
                motive,
                branch(Expr::const_str("Bool.false")),
                branch(Expr::const_str("Bool.true")),
                state.term.clone(),
            ],
        );
        (left, right, lams(&[state, payload], proof))
    }

    #[derive(Clone, Copy, Debug)]
    enum Mutation {
        None,
        OpaqueCode,
        SuccessCallback,
        FailureCallback,
        FrozenState,
        LostError,
        ForgedProof,
    }

    fn instance(mutation: Mutation) -> (Expr, Expr) {
        let nat = Expr::const_str("Nat");
        let mut sc = Scope::default();
        let fails = sc.local(bool_ty());
        let input = sc.local(bool_ty());
        let payload = sc.local(nat.clone());
        let state = sc.local(bool_ty());
        let yes = sc.local(continuation(&bool_ty(), &nat, &nat));
        let no = sc.local(yes.ty.clone());
        let post = bool_case(
            &mut sc,
            bool_ty(),
            state.term.clone(),
            Expr::const_str("Bool.true"),
            Expr::const_str("Bool.false"),
            false,
        );
        let outcome = bool_case(
            &mut sc,
            super::outcome(&nat, &nat),
            fails.term.clone(),
            apps(
                "Except.ok",
                [nat.clone(), nat.clone(), payload.term.clone()],
            ),
            apps(
                "Except.error",
                [nat.clone(), nat.clone(), payload.term.clone()],
            ),
            false,
        );
        let observed = pair(
            &bool_ty(),
            &super::outcome(&nat, &nat),
            post.clone(),
            outcome.clone(),
        );
        let m = state.lam(observed);
        let convert = |run: Expr| {
            apps(
                TO_CPS,
                [bool_ty(), nat.clone(), nat.clone(), nat.clone(), run],
            )
        };
        let converted = convert(m.clone());
        let code = match mutation {
            Mutation::OpaqueCode => {
                lams(&[state.clone(), yes.clone(), no.clone()], Expr::nat_lit(37))
            }
            Mutation::FrozenState => convert(state.lam(pair(
                &bool_ty(),
                &super::outcome(&nat, &nat),
                state.term.clone(),
                outcome,
            ))),
            Mutation::LostError => {
                let lost = bool_case(
                    &mut sc,
                    super::outcome(&nat, &nat),
                    fails.term.clone(),
                    apps(
                        "Except.ok",
                        [nat.clone(), nat.clone(), payload.term.clone()],
                    ),
                    apps("Except.error", [nat.clone(), nat.clone(), Expr::nat_lit(0)]),
                    false,
                );
                convert(state.lam(pair(&bool_ty(), &super::outcome(&nat, &nat), post, lost)))
            }
            _ => converted.clone(),
        };
        let image = lams(
            &[state.clone(), yes.clone(), no.clone()],
            refl(
                &nat,
                Expr::apps(
                    converted,
                    [state.term.clone(), yes.term.clone(), no.term.clone()],
                ),
            ),
        );
        let (left_ok, mut right_ok, same_ok) = callback(&mut sc, false);
        let (left_err, mut right_err, same_err) = callback(&mut sc, true);
        if matches!(mutation, Mutation::SuccessCallback) {
            right_ok = lams(&[state.clone(), payload.clone()], Expr::nat_lit(99));
        }
        if matches!(mutation, Mutation::FailureCallback) {
            right_err = lams(&[state.clone(), payload.clone()], Expr::nat_lit(99));
        }
        let left = Expr::apps(
            code.clone(),
            [input.term.clone(), left_ok.clone(), left_err.clone()],
        );
        let right = Expr::apps(
            code.clone(),
            [input.term.clone(), right_ok.clone(), right_err.clone()],
        );
        let goal = eq(&nat, left.clone(), right);
        let proof = if matches!(mutation, Mutation::ForgedProof) {
            refl(&nat, left)
        } else {
            apps(
                CPS_IMAGE_CALLBACK_CONGR,
                [
                    bool_ty(),
                    nat.clone(),
                    nat.clone(),
                    nat,
                    m,
                    code,
                    image,
                    left_ok,
                    right_ok,
                    left_err,
                    right_err,
                    same_ok,
                    same_err,
                    input.term.clone(),
                ],
            )
        };
        let parameters = [fails, input, payload];
        let levels = [(Name::from_string("u"), Level::zero())];
        (
            pis(&parameters, goal).instantiate_level_params(&levels),
            lams(&parameters, proof).instantiate_level_params(&levels),
        )
    }

    fn replay(mutation: Mutation, accepted: bool) {
        let env = environment();
        let (goal, proof) = instance(mutation);
        let encode = |term: &Expr| trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap();
        let goal_bytes = encode(&goal);
        let proof_bytes = encode(&proof);
        let goal = trust_ir::proof::decode_clean_expr_dag_v2(&goal_bytes).unwrap();
        let proof = trust_ir::proof::decode_clean_expr_dag_v2(&proof_bytes).unwrap();
        let mut tc = TypeChecker::new(&env);
        tc.set_allow_unsafe(false);
        tc.set_allow_partial(false);
        tc.set_heartbeat_limit(HEARTBEAT_LIMIT);
        tc.set_max_cache_entries(CACHE_ENTRY_LIMIT);
        tc.check_type(&goal, &Expr::prop()).unwrap();
        let result = tc.check_type(&proof, &goal);
        if let Some(path) = std::env::var_os("TRUST_IR_CPS_CALLBACK_ARTIFACT_DIR") {
            let path = std::path::PathBuf::from(path).join(format!("{mutation:?}"));
            std::fs::create_dir_all(&path).unwrap();
            std::fs::write(path.join("goal.bin"), goal_bytes).unwrap();
            std::fs::write(path.join("proof.bin"), proof_bytes).unwrap();
            std::fs::write(path.join("verdict.txt"), format!("{result:?}")).unwrap();
        }
        if accepted {
            result.unwrap();
            let audit = env.audit_certification(&goal, &proof);
            assert!(audit.is_certified(), "{audit:?}");
            for dependency in audit.dependencies {
                assert!(env.axiom_deps(&dependency).unwrap().is_empty());
                assert!(env.foundational_axiom_deps(&dependency).unwrap().is_empty());
                assert!(env.trust_marker_deps(&dependency).unwrap().is_empty());
            }
        } else {
            assert!(
                matches!(
                    result,
                    Err(clean_kernel::tc::TypeError::TypeMismatch { .. })
                ),
                "{mutation:?}: {result:?}"
            );
            assert!(!tc.heartbeat_spent());
        }
    }

    #[test]
    fn genuine_stateful_provider_transports_nonidentical_callbacks() {
        replay(Mutation::None, true);
    }

    #[test]
    fn callback_congruence_refuses_unproved_image_changed_state_payload_or_callbacks() {
        for mutation in [
            Mutation::OpaqueCode,
            Mutation::SuccessCallback,
            Mutation::FailureCallback,
            Mutation::FrozenState,
            Mutation::LostError,
            Mutation::ForgedProof,
        ] {
            replay(mutation, false);
        }
    }
}
