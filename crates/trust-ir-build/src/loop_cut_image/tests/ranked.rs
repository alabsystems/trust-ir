// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! A ranked completion consumer over the original typed SSA cut, not an
//! alternate loop implementation. Its concrete provider is a mathematical
//! Run model; no native-provider or source-language correspondence is claimed.
use super::*;

#[path = "cps_prefix.rs"]
mod cps_prefix_tests;

fn constant(name: &str, levels: &[u8]) -> Expr {
    Expr::const_(
        Name::from_string(name),
        levels
            .iter()
            .map(|n| (0..*n).fold(Level::zero(), |u, _| Level::succ(u)))
            .collect::<Vec<_>>(),
    )
}
fn call(name: &str, levels: &[u8], args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(constant(name, levels), args)
}
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    call("Eq", &[1], [ty, a, b])
}
fn refl(ty: Expr, value: Expr) -> Expr {
    call("Eq.refl", &[1], [ty, value])
}
fn trans(ty: Expr, a: Expr, b: Expr, c_: Expr, ab: Expr, bc: Expr) -> Expr {
    call("Eq.trans", &[1], [ty, a, b, c_, ab, bc])
}
fn symm(ty: Expr, a: Expr, b: Expr, ab: Expr) -> Expr {
    call("Eq.symm", &[1], [ty, a, b, ab])
}
fn congr(a: Expr, b: Expr, f: Expr, x: Expr, y: Expr, xy: Expr) -> Expr {
    call("congrArg", &[1, 1], [a, b, x, y, f, xy])
}
fn prod(a: Expr, b: Expr) -> Expr {
    call("Prod", &[0, 0], [a, b])
}
fn pair(a: Expr, b: Expr, x: Expr, y: Expr) -> Expr {
    call("Prod.mk", &[0, 0], [a, b, x, y])
}
fn field(second: bool, a: Expr, b: Expr, value: Expr) -> Expr {
    call(
        if second { "Prod.snd" } else { "Prod.fst" },
        &[0, 0],
        [a, b, value],
    )
}
fn sum(a: Expr, b: Expr) -> Expr {
    call("Sum", &[0, 0], [a, b])
}
fn tag(right: bool, a: Expr, b: Expr, value: Expr) -> Expr {
    call(
        if right { "Sum.inr" } else { "Sum.inl" },
        &[0, 0],
        [a, b, value],
    )
}
fn except(a: Expr) -> Expr {
    call("Except", &[0, 0], [c("Bool"), a])
}
fn outcome(ok: bool, a: Expr, value: Expr) -> Expr {
    call(
        if ok { "Except.ok" } else { "Except.error" },
        &[0, 0],
        [c("Bool"), a, value],
    )
}
fn local(scope: &mut LocalScope, ty: Expr) -> ScopedLocal {
    scope.allocate_local(ty).unwrap()
}
fn nth(mut value: Expr, count: usize, index: usize) -> Expr {
    for i in 0..index {
        value = field(true, c("Bool"), lanes(&ptypes(count - i - 1)), value);
    }
    field(false, c("Bool"), lanes(&ptypes(count - index - 1)), value)
}

struct LoopModel {
    step: Expr,
    at_cursor: Expr,
    invariant: Expr,
    state_ty: Expr,
    done_ty: Expr,
    pulse_ty: Expr,
}
impl LoopModel {
    fn header(&self, state: Expr) -> Expr {
        field(false, lanes(&ptypes(4)), c("Nat"), state)
    }
    fn host(&self, state: Expr) -> Expr {
        field(true, lanes(&ptypes(4)), c("Nat"), state)
    }
    fn cursor(&self, state: Expr) -> Expr {
        nth(self.header(state), 4, 0)
    }
    fn inv(&self, rank: Expr, state: Expr) -> Expr {
        Expr::apps(self.invariant.clone(), [rank, state])
    }
    fn pulse(&self, right: bool, value: Expr) -> Expr {
        tag(right, self.state_ty.clone(), self.done_ty.clone(), value)
    }
    fn prefix(&self, count: Expr, state: Expr) -> Expr {
        call(
            semantic_evaluation::LOOP_PREFIX,
            &[0],
            [
                self.state_ty.clone(),
                self.done_ty.clone(),
                self.step.clone(),
                count,
                state,
            ],
        )
    }
    fn done_at_zero(&self, state: Expr) -> Expr {
        let header = self.header(state.clone());
        pair(
            c("Nat"),
            except(lanes(&ptypes(2))),
            self.host(state),
            outcome(
                true,
                lanes(&ptypes(2)),
                packed(&[nth(header.clone(), 4, 1), nth(header, 4, 2)]),
            ),
        )
    }
    fn terminal_predicate(&self, scope: &mut LocalScope, actual: Expr) -> Expr {
        let done = local(scope, self.done_ty.clone());
        done.lam(eq(
            self.pulse_ty.clone(),
            actual,
            self.pulse(true, done.term().clone()),
        ))
    }
    fn exists(&self, predicate: Expr) -> Expr {
        call("Exists", &[1], [self.done_ty.clone(), predicate])
    }
}

fn provider(scope: &mut LocalScope, id: FuncId, fail: bool) -> Model {
    let args = (0..3).map(|_| local(scope, c("Bool"))).collect::<Vec<_>>();
    let host = local(scope, c("Nat"));
    let value_ty = lanes(&ptypes(3));
    let observation = pair(
        c("Nat"),
        except(value_ty.clone()),
        Expr::app(c("Nat.succ"), host.term().clone()),
        if fail {
            outcome(false, value_ty, c("Bool.false"))
        } else {
            outcome(
                true,
                value_ty,
                packed(&[c("Bool.false"), c("Bool.false"), c("Bool.true")]),
            )
        },
    );
    let run = host.lam(observation);
    let converted = from_run(scope, &primitive_types(), run.clone());
    Model {
        provider: id,
        run: lams(&args, run),
        cps: lams(&args, converted.cps),
        proof: lams(&args, converted.proof),
        forged: false,
    }
}

fn decode(scope: &mut LocalScope, lm: &LoopModel, observation: Expr) -> Expr {
    let cut_value = sum_type();
    let result_ty = lanes(&ptypes(2));
    let host = field(
        false,
        c("Nat"),
        except(cut_value.clone()),
        observation.clone(),
    );
    let status = field(true, c("Nat"), except(cut_value.clone()), observation);
    let bad = local(scope, c("Bool"));
    let ok = local(scope, cut_value.clone());
    let resumed = local(scope, lanes(&ptypes(4)));
    let returned = local(scope, result_ty.clone());
    let ignored_sum = local(scope, cut_value.clone());
    let result = call(
        "Sum.rec",
        &[1, 0, 0],
        [
            lanes(&ptypes(4)),
            result_ty.clone(),
            ignored_sum.lam(lm.pulse_ty.clone()),
            resumed.lam(lm.pulse(
                false,
                pair(
                    lanes(&ptypes(4)),
                    c("Nat"),
                    resumed.term().clone(),
                    host.clone(),
                ),
            )),
            returned.lam(lm.pulse(
                true,
                pair(
                    c("Nat"),
                    except(result_ty.clone()),
                    host.clone(),
                    outcome(true, result_ty.clone(), returned.term().clone()),
                ),
            )),
            ok.term().clone(),
        ],
    );
    let ignored_except = local(scope, except(cut_value.clone()));
    call(
        "Except.rec",
        &[1, 0, 0],
        [
            c("Bool"),
            cut_value,
            ignored_except.lam(lm.pulse_ty.clone()),
            bad.lam(lm.pulse(
                true,
                pair(
                    c("Nat"),
                    except(result_ty.clone()),
                    host,
                    outcome(false, result_ty, bad.term().clone()),
                ),
            )),
            ok.lam(result),
            status,
        ],
    )
}

fn reconstruct(scope: &mut LocalScope, graph: &Graph, env: &Environment, fail: bool) -> LoopModel {
    let report = crate::validate_module_report(&graph.module);
    assert!(report.is_ok(), "{:?}", report.errors());
    let endpoint = CutImageEndpoint::new(&report, graph.function, graph.header).unwrap();
    let model = provider(scope, graph.provider, fail);
    let image = endpoint
        .reconstruct(&model, scope, types(), CutImageLimits::default())
        .unwrap();
    assert_eq!(
        image.ids[..3],
        [graph.cursor, graph.accumulator, graph.world]
    );
    let claim = close(
        scope,
        &image.parameters,
        image.candidate.proposition(&types()),
        false,
    );
    let proof = close(
        scope,
        &image.parameters,
        image.candidate.proof.clone(),
        true,
    );
    check(env, &claim, &proof).unwrap();
    assert!(env.audit_certification(&claim, &proof).is_certified());
    let original_run = lams(&image.parameters, image.candidate.run);

    let header_ty = lanes(&ptypes(4));
    let state_ty = prod(header_ty.clone(), c("Nat"));
    let done_ty = prod(c("Nat"), except(lanes(&ptypes(2))));
    let mut lm = LoopModel {
        step: c("Unit.unit"),
        at_cursor: c("Unit.unit"),
        invariant: c("Unit.unit"),
        pulse_ty: sum(state_ty.clone(), done_ty.clone()),
        state_ty,
        done_ty,
    };
    let state = local(scope, lm.state_ty.clone());
    let cursor = local(scope, c("Bool"));
    let header = lm.header(state.term().clone());
    let mut args = vec![cursor.term().clone()];
    args.extend((1..4).map(|i| nth(header.clone(), 4, i)));
    args.push(lm.host(state.term().clone()));
    let observed = Expr::apps(original_run, args);
    let pulsed = decode(scope, &lm, observed);
    lm.at_cursor = state.lam(cursor.lam(pulsed));
    let step_state = local(scope, lm.state_ty.clone());
    lm.step = step_state.lam(Expr::apps(
        lm.at_cursor.clone(),
        [
            step_state.term().clone(),
            lm.cursor(step_state.term().clone()),
        ],
    ));

    let rank = local(scope, c("Nat"));
    let invariant_state = local(scope, lm.state_ty.clone());
    let index = local(scope, c("Nat"));
    let old = local(scope, Expr::sort(Level::zero()));
    let zero = eq(
        c("Bool"),
        lm.cursor(invariant_state.term().clone()),
        c("Bool.false"),
    );
    let inv = call(
        "Nat.rec",
        &[1],
        [
            index.lam(Expr::sort(Level::zero())),
            zero,
            lams(&[index.clone(), old], c("True")),
            rank.term().clone(),
        ],
    );
    lm.invariant = rank.lam(invariant_state.lam(inv));
    lm
}

fn zero_case(scope: &mut LocalScope, lm: &LoopModel) -> Expr {
    let state = local(scope, lm.state_ty.clone());
    let h = local(scope, lm.inv(Expr::nat_lit(0), state.term().clone()));
    let actual = Expr::app(lm.step.clone(), state.term().clone());
    let done = lm.done_at_zero(state.term().clone());
    let cursor = local(scope, c("Bool"));
    let mapper = cursor.lam(Expr::apps(
        lm.at_cursor.clone(),
        [state.term().clone(), cursor.term().clone()],
    ));
    let equality = congr(
        c("Bool"),
        lm.pulse_ty.clone(),
        mapper,
        lm.cursor(state.term().clone()),
        c("Bool.false"),
        h.term().clone(),
    );
    let predicate = lm.terminal_predicate(scope, actual);
    lams(
        &[state, h],
        call(
            "Exists.intro",
            &[1],
            [lm.done_ty.clone(), predicate, done, equality],
        ),
    )
}

fn cursor_observer(scope: &mut LocalScope, lm: &LoopModel) -> Expr {
    let pulse = local(scope, lm.pulse_ty.clone());
    let state = local(scope, lm.state_ty.clone());
    let done = local(scope, lm.done_ty.clone());
    let ignored = local(scope, lm.pulse_ty.clone());
    pulse.lam(call(
        "Sum.rec",
        &[1, 0, 0],
        [
            lm.state_ty.clone(),
            lm.done_ty.clone(),
            ignored.lam(c("Bool")),
            state.lam(lm.cursor(state.term().clone())),
            done.lam(c("Bool.false")),
            pulse.term().clone(),
        ],
    ))
}

fn decrease_goal(scope: &mut LocalScope, lm: &LoopModel, rank: Expr) -> Expr {
    let state = local(scope, lm.state_ty.clone());
    let next = local(scope, lm.state_ty.clone());
    let inv = local(
        scope,
        lm.inv(Expr::app(c("Nat.succ"), rank.clone()), state.term().clone()),
    );
    let edge = local(
        scope,
        eq(
            lm.pulse_ty.clone(),
            Expr::app(lm.step.clone(), state.term().clone()),
            lm.pulse(false, next.term().clone()),
        ),
    );
    state.pi(next.pi(inv.pi(edge.pi(lm.inv(rank, next.term().clone())))))
}
fn decrease_at_zero(scope: &mut LocalScope, lm: &LoopModel) -> Expr {
    let state = local(scope, lm.state_ty.clone());
    let next = local(scope, lm.state_ty.clone());
    let inv = local(scope, lm.inv(Expr::nat_lit(1), state.term().clone()));
    let actual = Expr::app(lm.step.clone(), state.term().clone());
    let continued = lm.pulse(false, next.term().clone());
    let edge = local(
        scope,
        eq(lm.pulse_ty.clone(), actual.clone(), continued.clone()),
    );
    let observer = cursor_observer(scope, lm);
    let cursor = local(scope, c("Bool"));
    let observed = Expr::app(
        observer.clone(),
        Expr::apps(
            lm.at_cursor.clone(),
            [state.term().clone(), cursor.term().clone()],
        ),
    );
    let motive = cursor.lam(eq(c("Bool"), observed, c("Bool.false")));
    let actual_law = call(
        "Bool.rec",
        &[0],
        [
            motive,
            refl(c("Bool"), c("Bool.false")),
            refl(c("Bool"), c("Bool.false")),
            lm.cursor(state.term().clone()),
        ],
    );
    let mapped = congr(
        lm.pulse_ty.clone(),
        c("Bool"),
        observer.clone(),
        actual.clone(),
        continued.clone(),
        edge.term().clone(),
    );
    let actual_observed = Expr::app(observer.clone(), actual);
    let next_observed = Expr::app(observer, continued);
    let proof = trans(
        c("Bool"),
        next_observed.clone(),
        actual_observed.clone(),
        c("Bool.false"),
        symm(c("Bool"), actual_observed, next_observed, mapped),
        actual_law,
    );
    lams(&[state, next, inv, edge], proof)
}
fn decreases(scope: &mut LocalScope, lm: &LoopModel) -> Expr {
    let rank = local(scope, c("Nat"));
    let index = local(scope, c("Nat"));
    let goal = decrease_goal(scope, lm, index.term().clone());
    let motive = index.lam(goal);
    let zero = decrease_at_zero(scope, lm);
    let k = local(scope, c("Nat"));
    let lower_goal = decrease_goal(scope, lm, k.term().clone());
    let ih = local(scope, lower_goal);
    let state = local(scope, lm.state_ty.clone());
    let next = local(scope, lm.state_ty.clone());
    let inv = local(
        scope,
        lm.inv(
            Expr::app(c("Nat.succ"), Expr::app(c("Nat.succ"), k.term().clone())),
            state.term().clone(),
        ),
    );
    let edge = local(
        scope,
        eq(
            lm.pulse_ty.clone(),
            Expr::app(lm.step.clone(), state.term().clone()),
            lm.pulse(false, next.term().clone()),
        ),
    );
    let succ = lams(&[k, ih, state, next, inv, edge], c("True.intro"));
    rank.lam(call(
        "Nat.rec",
        &[0],
        [motive, zero, succ, rank.term().clone()],
    ))
}

fn ranked_environment() -> Environment {
    let mut env = environment();
    env.init_true_false().unwrap();
    semantic_evaluation::install_loop_into(&mut env).unwrap();
    semantic_evaluation::install_ranked_loop_into(&mut env).unwrap();
    env
}

fn complete_graph_at_rank(
    graph: &Graph,
    env: &Environment,
    rank: u64,
    fail: bool,
) -> (Expr, Expr, Expr, Expr) {
    let mut scope = LocalScope::new();
    let lm = reconstruct(&mut scope, graph, env, fail);
    let zero = zero_case(&mut scope, &lm);
    let decreasing = decreases(&mut scope, &lm);
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
    let actual = lm.prefix(Expr::nat_lit(rank + 1), initial.clone());
    let predicate = lm.terminal_predicate(&mut scope, actual.clone());
    let claim = lm.exists(predicate);
    let proof = call(
        semantic_evaluation::LOOP_RANK_COMPLETE,
        &[0],
        [
            lm.state_ty.clone(),
            lm.done_ty.clone(),
            lm.step.clone(),
            lm.invariant.clone(),
            zero,
            decreasing,
            Expr::nat_lit(rank),
            initial,
            c("True.intro"),
        ],
    );
    let expected_done = pair(
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
    );
    let exact = eq(
        lm.pulse_ty.clone(),
        actual.clone(),
        lm.pulse(true, expected_done),
    );
    let exact_proof = refl(lm.pulse_ty, actual);
    (
        close(&scope, &[host.clone()], claim, false),
        close(&scope, &[host.clone()], proof, true),
        close(&scope, &[host.clone()], exact, false),
        close(&scope, &[host], exact_proof, true),
    )
}

fn complete_graph(graph: &Graph, env: &Environment) -> (Expr, Expr, Expr, Expr) {
    complete_graph_at_rank(graph, env, 1, false)
}

fn semantic_refusal(env: &Environment, claim: &Expr, proof: &Expr) {
    let mut checker = TypeChecker::new(env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(16_384);
    checker
        .check_type(claim, &Expr::sort(Level::zero()))
        .expect("the mutated original still has a well-formed claim");
    let error = checker
        .check_type(proof, claim)
        .expect_err("the stale completion proof must fail");
    assert!(
        matches!(error, clean_kernel::KernelTypeError::TypeMismatch { .. }),
        "expected semantic TypeMismatch, got {error:?}"
    );
    assert!(!checker.heartbeat_spent());
}

#[test]
fn actual_cut_rank_completes_with_provider_updated_state() {
    let env = ranked_environment();
    let (claim, proof, exact, exact_proof) = complete_graph(&graph(), &env);
    check(&env, &claim, &proof).unwrap();
    check(&env, &exact, &exact_proof).unwrap();
    assert!(env.audit_certification(&claim, &proof).is_certified());
    assert!(env.audit_certification(&exact, &exact_proof).is_certified());
    let claim_wire = trust_ir::proof::encode_clean_expr_dag_v2(&claim).unwrap();
    let proof_wire = trust_ir::proof::encode_clean_expr_dag_v2(&proof).unwrap();
    let decoded_claim = trust_ir::proof::decode_clean_expr_dag_v2(&claim_wire).unwrap();
    let decoded_proof = trust_ir::proof::decode_clean_expr_dag_v2(&proof_wire).unwrap();
    assert_eq!(decoded_claim, claim);
    assert_eq!(decoded_proof, proof);
    check(&env, &decoded_claim, &decoded_proof).unwrap();
    eprintln!(
        "ranked actual-CFG completion DAG: goal={} bytes, proof={} bytes",
        claim_wire.len(),
        proof_wire.len()
    );
}

#[test]
fn actual_cut_rank_refuses_the_original_cursor_backedge() {
    let env = ranked_environment();
    let (_, proof, _, _) = complete_graph(&graph(), &env);
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
    let (claim, _, _, _) = complete_graph(&changed, &env);
    semantic_refusal(&env, &claim, &proof);
}

#[test]
fn actual_cut_rank_refuses_zero_rank_at_a_live_cursor() {
    let env = ranked_environment();
    let (claim, proof, _, _) = complete_graph_at_rank(&graph(), &env, 0, false);
    semantic_refusal(&env, &claim, &proof);
}

#[test]
fn actual_cut_complete_result_refuses_stale_world_return() {
    let env = ranked_environment();
    let (_, _, _, proof) = complete_graph(&graph(), &env);
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
    // The original entry capture is still live and has the same Bool type,
    // but is not the actual provider's newly returned world.
    values[1] = capture;
    let (_, _, claim, _) = complete_graph(&changed, &env);
    semantic_refusal(&env, &claim, &proof);
}

#[test]
fn actual_cut_rank_keeps_a_terminal_error_with_its_updated_host_state() {
    let env = ranked_environment();
    let (claim, proof, exact, exact_proof) = complete_graph_at_rank(&graph(), &env, 1, true);
    check(&env, &claim, &proof).unwrap();
    check(&env, &exact, &exact_proof).unwrap();
    assert!(env.audit_certification(&claim, &proof).is_certified());
    assert!(env.audit_certification(&exact, &exact_proof).is_certified());
}
