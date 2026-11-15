// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! New finite-prefix API consumed by the existing original typed SSA cut.
//! The inherited provider is an explicit mathematical Run model, not a native
//! implementation. Cut reconstruction and its full image proof remain checked.
use super::*;

fn cps_environment() -> Environment {
    let mut env = environment();
    semantic_evaluation::install_loop_into(&mut env).unwrap();
    semantic_evaluation::install_cps_loop_into(&mut env).unwrap();
    env
}
fn cps_mapping(scope: &mut LocalScope, lm: &LoopModel, terminal: bool) -> Expr {
    let value = local(
        scope,
        if terminal {
            lm.done_ty.clone()
        } else {
            lm.state_ty.clone()
        },
    );
    value.lam(lm.pulse(terminal, value.term().clone()))
}
fn cps_step(scope: &mut LocalScope, lm: &LoopModel, finish: Expr) -> Expr {
    let k = local(scope, Expr::arrow(lm.state_ty.clone(), lm.pulse_ty.clone()));
    let state = local(scope, lm.state_ty.clone());
    let ignored = local(scope, lm.pulse_ty.clone());
    lams(
        &[k.clone(), state.clone()],
        call(
            "Sum.rec",
            &[1, 0, 0],
            [
                lm.state_ty.clone(),
                lm.done_ty.clone(),
                ignored.lam(lm.pulse_ty.clone()),
                k.term().clone(),
                finish,
                Expr::app(lm.step.clone(), state.term().clone()),
            ],
        ),
    )
}
fn prefix_evidence(
    graph: &Graph,
    env: &Environment,
    count: u64,
    fail: bool,
    force_terminal: bool,
) -> (Expr, Expr) {
    let mut scope = LocalScope::new();
    // Reconstruct the actual original module/SSA cut and check its complete
    // CPS-image candidate before consuming the returned Run interpretation.
    let lm = reconstruct(&mut scope, graph, env, fail);
    let host = local(&mut scope, c("Nat"));
    let initial = pair(
        lanes(&ptypes(4)),
        c("Nat"),
        packed(&[
            c("Bool.true"),
            c("Bool.true"),
            c("Bool.true"),
            c("Bool.true"),
        ]),
        host.term().clone(),
    );
    let finish = cps_mapping(&mut scope, &lm, true);
    let residual = cps_mapping(&mut scope, &lm, false);
    let step = cps_step(&mut scope, &lm, finish.clone());
    let actual = call(
        semantic_evaluation::LOOP_CPS_PREFIX,
        &[0],
        [
            lm.state_ty.clone(),
            lm.pulse_ty.clone(),
            step,
            residual.clone(),
            Expr::nat_lit(count),
            initial.clone(),
        ],
    );
    let expected = if count == 0 && !force_terminal {
        lm.pulse(false, initial.clone())
    } else if count == 1 && !fail && !force_terminal {
        lm.pulse(
            false,
            pair(
                lanes(&ptypes(4)),
                c("Nat"),
                packed(&[
                    c("Bool.false"),
                    c("Bool.false"),
                    c("Bool.false"),
                    c("Bool.true"),
                ]),
                Expr::app(c("Nat.succ"), host.term().clone()),
            ),
        )
    } else {
        lm.pulse(
            true,
            pair(
                c("Nat"),
                except(lanes(&ptypes(2))),
                Expr::app(c("Nat.succ"), host.term().clone()),
                if fail {
                    outcome(false, lanes(&ptypes(2)), c("Bool.false"))
                } else {
                    outcome(
                        true,
                        lanes(&ptypes(2)),
                        packed(&[c("Bool.false"), c("Bool.false")]),
                    )
                },
            ),
        )
    };
    let proof = call(
        semantic_evaluation::LOOP_CPS_PREFIX_FROM_PULSE,
        &[0],
        [
            lm.state_ty.clone(),
            lm.done_ty.clone(),
            lm.pulse_ty.clone(),
            lm.step.clone(),
            finish,
            residual,
            Expr::nat_lit(count),
            initial,
        ],
    );
    let goal = eq(lm.pulse_ty, actual, expected);
    (
        close(&scope, &[host.clone()], goal, false),
        close(&scope, &[host], proof, true),
    )
}
fn cps_check(env: &Environment, label: &str, goal: Expr, proof: Expr, accept: bool) {
    let goal_wire = trust_ir::proof::encode_clean_expr_dag_v2(&goal).unwrap();
    let proof_wire = trust_ir::proof::encode_clean_expr_dag_v2(&proof).unwrap();
    let goal = trust_ir::proof::decode_clean_expr_dag_v2(&goal_wire).unwrap();
    let proof = trust_ir::proof::decode_clean_expr_dag_v2(&proof_wire).unwrap();
    let mut checker = TypeChecker::new(env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(semantic_evaluation::HEARTBEAT_LIMIT);
    checker.set_max_cache_entries(semantic_evaluation::CACHE_ENTRY_LIMIT);
    checker.check_type(&goal, &Expr::prop()).unwrap();
    let result = checker.check_type(&proof, &goal);
    if accept {
        assert!(
            result.is_ok(),
            "{label}: typed cut prefix refused; mismatch={} spent={}",
            matches!(
                result,
                Err(clean_kernel::KernelTypeError::TypeMismatch { .. })
            ),
            checker.heartbeat_spent()
        );
        assert!(env.audit_certification(&goal, &proof).is_certified());
    } else {
        assert!(
            matches!(
                result,
                Err(clean_kernel::KernelTypeError::TypeMismatch { .. })
            ),
            "{label}: expected semantic TypeMismatch"
        );
        assert!(!checker.heartbeat_spent());
    }
    if let Some(base) = std::env::var_os("TRUST_IR_CPS_PREFIX_ARTIFACT_DIR") {
        let dir = std::path::PathBuf::from(base).join(label);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("goal.bin"), goal_wire).unwrap();
        std::fs::write(dir.join("proof.bin"), proof_wire).unwrap();
        std::fs::write(dir.join("codec.txt"), "Clean DAG v2").unwrap();
        std::fs::write(
            dir.join("verdict.txt"),
            if accept {
                "kernel/audit accepted"
            } else {
                "semantic TypeMismatch"
            },
        )
        .unwrap();
    }
}

#[test]
fn actual_cut_cps_prefix_preserves_suspension_terminal_success_and_error() {
    let env = cps_environment();
    for (fail, count) in [
        (false, 0),
        (false, 1),
        (false, 2),
        (false, 4),
        (true, 0),
        (true, 1),
        (true, 4),
    ] {
        let (goal, proof) = prefix_evidence(&graph(), &env, count, fail, false);
        cps_check(
            &env,
            &format!("typed-cut-fail{fail}-prefix{count}"),
            goal,
            proof,
            true,
        );
    }
}
#[test]
fn actual_cut_cps_prefix_rejects_an_original_cursor_backedge_mutation() {
    let env = cps_environment();
    let (_, proof) = prefix_evidence(&graph(), &env, 2, false, false);
    let mut changed = graph();
    let function = changed
        .module
        .functions
        .iter_mut()
        .find(|f| f.id == changed.function)
        .unwrap();
    let node = function
        .blocks
        .iter_mut()
        .find(|b| b.id == changed.back)
        .unwrap()
        .body
        .last_mut()
        .unwrap();
    let Inst::Br { args, .. } = &mut node.inst else {
        panic!()
    };
    args[0] = changed.cursor;
    let (goal, _) = prefix_evidence(&changed, &env, 2, false, false);
    cps_check(
        &env,
        "typed-cut-refuse-original-backedge",
        goal,
        proof,
        false,
    );
}
#[test]
fn actual_cut_cps_prefix_rejects_an_original_stale_returned_world() {
    let env = cps_environment();
    let (_, proof) = prefix_evidence(&graph(), &env, 2, false, false);
    let mut changed = graph();
    let function = changed
        .module
        .functions
        .iter()
        .find(|f| f.id == changed.function)
        .unwrap();
    let capture = function
        .blocks
        .iter()
        .find(|b| b.id == function.entry)
        .unwrap()
        .params[0]
        .0;
    let function = changed
        .module
        .functions
        .iter_mut()
        .find(|f| f.id == changed.function)
        .unwrap();
    let done = function
        .blocks
        .iter_mut()
        .find(|b| {
            b.id != changed.failed
                && matches!(b.body.last().map(|n| &n.inst), Some(Inst::Return { .. }))
        })
        .unwrap();
    let Inst::Return { values } = &mut done.body.last_mut().unwrap().inst else {
        panic!()
    };
    values[1] = capture;
    let (goal, _) = prefix_evidence(&changed, &env, 2, false, false);
    cps_check(&env, "typed-cut-refuse-original-return", goal, proof, false);
}
#[test]
fn actual_cut_cps_prefix_rejects_zero_as_completion() {
    let env = cps_environment();
    let (goal, proof) = prefix_evidence(&graph(), &env, 0, false, true);
    cps_check(&env, "typed-cut-refuse-zero-completion", goal, proof, false);
}
