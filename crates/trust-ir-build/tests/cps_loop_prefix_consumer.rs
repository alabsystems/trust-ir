// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Ordinary first-order countdown cuts consumed by the public CPS-prefix API.
//! This has no TLA types, provider assumptions, native or termination authority.
use clean_kernel::expr::FVarId;
use clean_kernel::{BinderInfo, Environment, Expr, KernelTypeError, Level, Name, TypeChecker};
use trust_ir_build::semantic_evaluation as eval;

fn at(name: &str, levels: usize, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::zero(); levels]),
        args,
    )
}
fn z(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    at(name, 1, args)
}
fn n(x: u64) -> Expr {
    Expr::nat_lit(x)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn pair_ty(a: Expr, b: Expr) -> Expr {
    at("Prod", 2, [a, b])
}
fn pair(a: Expr, b: Expr, x: Expr, y: Expr) -> Expr {
    at("Prod.mk", 2, [a, b, x, y])
}
fn fst(a: Expr, b: Expr, p: Expr) -> Expr {
    at("Prod.fst", 2, [a, b, p])
}
fn snd(a: Expr, b: Expr, p: Expr) -> Expr {
    at("Prod.snd", 2, [a, b, p])
}
fn sum(a: Expr, b: Expr) -> Expr {
    at("Sum", 2, [a, b])
}
fn side(a: Expr, b: Expr, right: bool, p: Expr) -> Expr {
    at(if right { "Sum.inr" } else { "Sum.inl" }, 2, [a, b, p])
}
fn except(a: Expr, b: Expr) -> Expr {
    at("Except", 2, [a, b])
}
fn outcome(error: bool, ty: Expr, value: Expr) -> Expr {
    at(
        if error { "Except.error" } else { "Except.ok" },
        2,
        [nat(), ty, value],
    )
}
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, a, b],
    )
}
fn refl(ty: Expr, a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, a],
    )
}
#[derive(Clone)]
struct Local {
    id: FVarId,
    ty: Expr,
    term: Expr,
}
impl Local {
    fn lam(&self, b: Expr) -> Expr {
        Expr::lam(
            BinderInfo::Default,
            self.ty.clone(),
            b.abstract_fvar(self.id),
        )
    }
}
#[derive(Default)]
struct Scope(u64);
impl Scope {
    fn local(&mut self, ty: Expr) -> Local {
        let id = FVarId::new(self.0);
        self.0 += 1;
        Local {
            id,
            ty,
            term: Expr::fvar(id),
        }
    }
}
fn lams(xs: &[Local], b: Expr) -> Expr {
    xs.iter().rev().fold(b, |b, x| x.lam(b))
}
// Use only the minimal Nat vocabulary installed by the loop API. A prior
// fixture used Nat.beq without installing its separate order vocabulary.
fn is_zero(sc: &mut Scope, value: Expr) -> Expr {
    let index = sc.local(nat());
    let previous = sc.local(Expr::const_str("Bool"));
    Expr::apps(
        Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            index.lam(Expr::const_str("Bool")),
            Expr::const_str("Bool.true"),
            lams(&[index, previous], Expr::const_str("Bool.false")),
            value,
        ],
    )
}
fn choose(sc: &mut Scope, ty: Expr, flag: Expr, yes: Expr, no: Expr) -> Expr {
    let b = sc.local(Expr::const_str("Bool"));
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [b.lam(ty), no, yes, flag],
    )
}
fn cases(sc: &mut Scope, s: Expr, d: Expr, a: Expr, value: Expr, left: Expr, right: Expr) -> Expr {
    let p = sc.local(sum(s.clone(), d.clone()));
    Expr::apps(
        Expr::const_(
            Name::from_string("Sum.rec"),
            vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
        ),
        [s, d, p.lam(a), left, right, value],
    )
}
fn state() -> Expr {
    pair_ty(nat(), nat())
}
fn state_value(count: u64, stamp: u64) -> Expr {
    pair(nat(), nat(), n(count), n(stamp))
}
fn done() -> Expr {
    pair_ty(state(), except(nat(), nat()))
}
fn terminal(count: u64, stamp: u64, error: bool, value: u64) -> Expr {
    pair(
        state(),
        except(nat(), nat()),
        state_value(count, stamp),
        outcome(error, nat(), n(value)),
    )
}
fn answer() -> Expr {
    sum(state(), done())
}
fn environment() -> Environment {
    let mut e = eval::build_environment().unwrap();
    eval::install_loop_into(&mut e).unwrap();
    eval::install_cps_loop_into(&mut e).unwrap();
    eval::install_handle_into(&mut e).unwrap();
    eval::install_cut_run_into(&mut e).unwrap();
    e
}
/// A cut returns None after a real state update; Some/error is terminal and
/// retains that cut's returned State. The public run-to-pulse map interprets it.
fn cut(sc: &mut Scope, fail_at_one: bool) -> Expr {
    let s = sc.local(state());
    let count = fst(nat(), nat(), s.term.clone());
    let stamp = snd(nat(), nat(), s.term.clone());
    let next = pair(
        nat(),
        nat(),
        Expr::app(Expr::const_str("Nat.pred"), count.clone()),
        Expr::apps(Expr::const_str("Nat.add"), [stamp.clone(), n(1)]),
    );
    let opt = z("Option", [nat()]);
    let result = pair_ty(state(), except(nat(), opt.clone()));
    let resume = pair(
        state(),
        except(nat(), opt.clone()),
        next.clone(),
        outcome(false, opt.clone(), z("Option.none", [nat()])),
    );
    let failure = pair(
        state(),
        except(nat(), opt.clone()),
        next,
        outcome(true, opt.clone(), n(9)),
    );
    let working = if fail_at_one {
        let at_one = is_zero(sc, Expr::app(Expr::const_str("Nat.pred"), count.clone()));
        choose(sc, result.clone(), at_one, failure, resume)
    } else {
        resume
    };
    let success = pair(
        state(),
        except(nat(), opt.clone()),
        s.term.clone(),
        outcome(false, opt, z("Option.some", [nat(), stamp])),
    );
    let at_zero = is_zero(sc, count);
    let body = choose(sc, result, at_zero, success, working);
    s.lam(body)
}
fn pulse(sc: &mut Scope, cut: Expr) -> Expr {
    let s = sc.local(state());
    s.lam(z(
        eval::RUN_TO_PULSE,
        [state(), nat(), nat(), Expr::app(cut, s.term.clone())],
    ))
}
fn finish(sc: &mut Scope) -> Expr {
    let d = sc.local(done());
    d.lam(side(state(), done(), true, d.term.clone()))
}
fn residual(sc: &mut Scope) -> Expr {
    let s = sc.local(state());
    s.lam(side(state(), done(), false, s.term.clone()))
}
fn cps_step(sc: &mut Scope, pulse: Expr, finish: Expr) -> Expr {
    let k = sc.local(Expr::arrow(state(), answer()));
    let s = sc.local(state());
    let body = cases(
        sc,
        state(),
        done(),
        answer(),
        Expr::app(pulse, s.term.clone()),
        k.term.clone(),
        finish,
    );
    lams(&[k, s], body)
}
fn prefix(step: Expr, residual: Expr, count: u64, initial: Expr) -> Expr {
    z(
        eval::LOOP_CPS_PREFIX,
        [state(), answer(), step, residual, n(count), initial],
    )
}
fn check(e: &Environment, label: &str, goal: Expr, proof: Expr, accept: bool) {
    let gw = trust_ir::proof::encode_clean_expr_v1(&goal).unwrap();
    let pw = trust_ir::proof::encode_clean_expr_v1(&proof).unwrap();
    let g = trust_ir::proof::decode_clean_expr_v1(&gw).unwrap();
    let p = trust_ir::proof::decode_clean_expr_v1(&pw).unwrap();
    let mut tc = TypeChecker::new(e);
    tc.set_heartbeat_limit(eval::HEARTBEAT_LIMIT);
    tc.set_max_cache_entries(eval::CACHE_ENTRY_LIMIT);
    tc.check_type(&g, &Expr::prop()).unwrap();
    let result = tc.check_type(&p, &g);
    if accept {
        assert!(
            result.is_ok(),
            "{label}: semantic proof refused; mismatch={} spent={}",
            matches!(result, Err(KernelTypeError::TypeMismatch { .. })),
            tc.heartbeat_spent()
        );
        assert!(e.audit_certification(&g, &p).is_certified());
    } else {
        assert!(
            matches!(result, Err(KernelTypeError::TypeMismatch { .. })),
            "{label}: expected semantic TypeMismatch"
        );
        assert!(!tc.heartbeat_spent());
    }
    if let Some(base) = std::env::var_os("TRUST_IR_CPS_PREFIX_ARTIFACT_DIR") {
        let dir = std::path::PathBuf::from(base).join(label);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("goal.bin"), gw).unwrap();
        std::fs::write(dir.join("proof.bin"), pw).unwrap();
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
fn ordinary_countdown_cut_prefix_retains_full_terminal_and_suspended_observations() {
    let e = environment();
    for (fail, count, expected) in [
        (false, 0, side(state(), done(), false, state_value(2, 40))),
        (false, 1, side(state(), done(), false, state_value(1, 41))),
        (false, 2, side(state(), done(), false, state_value(0, 42))),
        (
            false,
            3,
            side(state(), done(), true, terminal(0, 42, false, 42)),
        ),
        (
            false,
            8,
            side(state(), done(), true, terminal(0, 42, false, 42)),
        ),
        (true, 1, side(state(), done(), false, state_value(1, 41))),
        (
            true,
            2,
            side(state(), done(), true, terminal(0, 42, true, 9)),
        ),
        (
            true,
            8,
            side(state(), done(), true, terminal(0, 42, true, 9)),
        ),
    ] {
        let mut sc = Scope::default();
        let raw = cut(&mut sc, fail);
        let p = pulse(&mut sc, raw);
        let f = finish(&mut sc);
        let r = residual(&mut sc);
        let step = cps_step(&mut sc, p.clone(), f.clone());
        let actual = prefix(step, r.clone(), count, state_value(2, 40));
        let proof = z(
            eval::LOOP_CPS_PREFIX_FROM_PULSE,
            [
                state(),
                done(),
                answer(),
                p,
                f,
                r,
                n(count),
                state_value(2, 40),
            ],
        );
        check(
            &e,
            &format!("countdown-fail{fail}-prefix{count}"),
            eq(answer(), actual, expected),
            proof,
            true,
        );
    }
}
#[test]
fn wrong_step_wrong_output_and_zero_completion_are_semantic_refusals() {
    let e = environment();
    for which in ["step", "output", "zero", "error-payload", "terminal-state"] {
        let mut sc = Scope::default();
        let raw = cut(&mut sc, matches!(which, "error-payload" | "terminal-state"));
        let p = pulse(&mut sc, raw);
        let f = finish(&mut sc);
        let r = residual(&mut sc);
        let step = cps_step(&mut sc, p.clone(), f.clone());
        let count = match which {
            "zero" => 0,
            "error-payload" | "terminal-state" => 2,
            _ => 1,
        };
        let step = if which == "step" {
            let k = sc.local(Expr::arrow(state(), answer()));
            let s = sc.local(state());
            let wrong = pair(
                nat(),
                nat(),
                Expr::app(
                    Expr::const_str("Nat.pred"),
                    fst(nat(), nat(), s.term.clone()),
                ),
                Expr::apps(
                    Expr::const_str("Nat.add"),
                    [snd(nat(), nat(), s.term.clone()), n(5)],
                ),
            );
            lams(&[k.clone(), s], Expr::app(k.term, wrong))
        } else {
            step
        };
        let expected = if which == "zero" {
            side(state(), done(), true, terminal(2, 40, false, 40))
        } else if which == "error-payload" {
            side(state(), done(), true, terminal(0, 42, true, 10))
        } else if which == "terminal-state" {
            side(state(), done(), true, terminal(0, 40, true, 9))
        } else {
            side(
                state(),
                done(),
                false,
                state_value(1, if which == "output" { 99 } else { 41 }),
            )
        };
        let actual = prefix(step, r.clone(), count, state_value(2, 40));
        let proof = z(
            eval::LOOP_CPS_PREFIX_FROM_PULSE,
            [
                state(),
                done(),
                answer(),
                p,
                f,
                r,
                n(count),
                state_value(2, 40),
            ],
        );
        check(
            &e,
            &format!("refuse-{which}"),
            eq(answer(), actual, expected),
            proof,
            false,
        );
    }
}
#[test]
fn exact_step_equality_congruence_requires_a_proved_replacement() {
    let e = environment();
    let mut sc = Scope::default();
    let raw = cut(&mut sc, false);
    let p = pulse(&mut sc, raw);
    let f = finish(&mut sc);
    let r = residual(&mut sc);
    let step = cps_step(&mut sc, p, f);
    let k = sc.local(Expr::arrow(state(), answer()));
    let s = sc.local(state());
    let eta = lams(
        &[k.clone(), s.clone()],
        Expr::apps(step.clone(), [k.term.clone(), s.term.clone()]),
    );
    let step_ty = Expr::arrow(
        Expr::arrow(state(), answer()),
        Expr::arrow(state(), answer()),
    );
    let equal_steps = refl(step_ty.clone(), step.clone());
    let left = z(
        eval::LOOP_CPS_PREFIX,
        [state(), answer(), step.clone(), r.clone(), n(3)],
    );
    let right = z(
        eval::LOOP_CPS_PREFIX,
        [state(), answer(), eta.clone(), r.clone(), n(3)],
    );
    let goal = eq(Expr::arrow(state(), answer()), left, right);
    let proof = z(
        eval::LOOP_CPS_PREFIX_CONGR,
        [state(), answer(), step.clone(), eta, equal_steps, r, n(3)],
    );
    check(&e, "exact-step-congruence", goal, proof, true);
    let k = sc.local(Expr::arrow(state(), answer()));
    let s = sc.local(state());
    let bad = lams(
        &[k.clone(), s.clone()],
        Expr::app(k.term, state_value(88, 99)),
    );
    check(
        &e,
        "refuse-wrong-step-premise",
        eq(step_ty.clone(), step.clone(), bad),
        refl(step_ty, step),
        false,
    );
}

#[test]
fn generic_laws_replay_and_installation_preserves_existing_vocabulary() {
    let mut e = eval::build_environment().unwrap();
    eval::install_loop_into(&mut e).unwrap();
    let before: Vec<_> = e.constants().map(|i| (i.name.clone(), i.clone())).collect();
    let options = [
        e.get_option("maxHeartbeats").cloned(),
        e.get_option("tcMaxCacheEntries").cloned(),
    ];
    let mode = e.mode();
    eval::install_cps_loop_into(&mut e).unwrap();
    assert_eq!(e.num_constants(), before.len() + 3);
    for (name, old) in before {
        let new = e.get_const(&name).unwrap();
        assert_eq!(new.type_, old.type_);
        assert_eq!(new.value, old.value);
        assert_eq!(new.level_params, old.level_params);
        assert_eq!(new.kind, old.kind);
    }
    assert_eq!(e.mode(), mode);
    assert_eq!(e.get_option("maxHeartbeats").cloned(), options[0]);
    assert_eq!(e.get_option("tcMaxCacheEntries").cloned(), options[1]);
    for name in [
        eval::LOOP_CPS_PREFIX_CONGR,
        eval::LOOP_CPS_PREFIX_FROM_PULSE,
    ] {
        let info = e.get_const(&Name::from_string(name)).unwrap();
        check(
            &e,
            name.rsplit('.').next().unwrap(),
            info.type_.clone(),
            info.value.clone().unwrap(),
            true,
        );
    }
}

#[test]
fn every_owned_name_collision_refuses_before_any_mutation() {
    for name in [
        eval::LOOP_CPS_PREFIX,
        eval::LOOP_CPS_PREFIX_CONGR,
        eval::LOOP_CPS_PREFIX_FROM_PULSE,
    ] {
        let mut e = Environment::default();
        e.add_decl(clean_kernel::Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            is_reducible: true,
        })
        .unwrap();
        let generation = e.generation();
        let constants = e.num_constants();
        assert_eq!(
            eval::install_cps_loop_into(&mut e).unwrap_err().declaration,
            name
        );
        assert_eq!(e.generation(), generation);
        assert_eq!(e.num_constants(), constants);
    }
}

#[test]
fn proved_terminal_pulse_transfers_the_full_cps_answer_for_different_residuals() {
    let mut e = environment();
    eval::install_cps_observation_into(&mut e).unwrap();
    eval::install_cps_completion_into(&mut e).unwrap();
    for fail in [false, true] {
        for different_residual in [false, true] {
            let mut sc = Scope::default();
            let raw = cut(&mut sc, fail);
            let p = pulse(&mut sc, raw);
            let f = finish(&mut sc);
            let step = cps_step(&mut sc, p.clone(), f.clone());
            let k = sc.local(Expr::arrow(state(), answer()));
            let s = sc.local(state());
            let observation = lams(
                &[k.clone(), s.clone()],
                refl(answer(), Expr::apps(step.clone(), [k.term, s.term])),
            );
            let r = if different_residual {
                let s = sc.local(state());
                s.lam(side(state(), done(), true, terminal(99, 99, true, 99)))
            } else {
                residual(&mut sc)
            };
            let count = if fail { 2 } else { 3 };
            let result = terminal(0, 42, fail, if fail { 9 } else { 42 });
            let done_pulse = side(state(), done(), true, result.clone());
            let terminal_proof = refl(sum(state(), done()), done_pulse);
            let arguments = vec![
                state(),
                done(),
                answer(),
                step.clone(),
                p,
                f,
                observation,
                r.clone(),
                n(count),
                state_value(2, 40),
                result.clone(),
                terminal_proof,
            ];
            let proof = z(eval::LOOP_CPS_COMPLETE_TRANSFER, arguments.clone());
            let actual = prefix(step.clone(), r.clone(), count, state_value(2, 40));
            if !fail && !different_residual {
                let mut premature = arguments.clone();
                premature[8] = n(0);
                check(
                    &e,
                    "refuse-cps-completion-without-terminal-prefix",
                    eq(
                        answer(),
                        prefix(step.clone(), r.clone(), 0, state_value(2, 40)),
                        side(state(), done(), true, result.clone()),
                    ),
                    z(eval::LOOP_CPS_COMPLETE_TRANSFER, premature),
                    false,
                );
                let k = sc.local(Expr::arrow(state(), answer()));
                let s = sc.local(state());
                let wrong_step = lams(&[k.clone(), s], Expr::app(k.term, state_value(99, 99)));
                let mut wrong_observation = arguments;
                wrong_observation[3] = wrong_step.clone();
                check(
                    &e,
                    "refuse-cps-completion-with-wrong-step-observation",
                    eq(
                        answer(),
                        prefix(wrong_step, r.clone(), count, state_value(2, 40)),
                        side(state(), done(), true, result.clone()),
                    ),
                    z(eval::LOOP_CPS_COMPLETE_TRANSFER, wrong_observation),
                    false,
                );
            }
            check(
                &e,
                &format!("complete-fail{fail}-residual{different_residual}"),
                eq(
                    answer(),
                    actual.clone(),
                    side(state(), done(), true, result),
                ),
                proof.clone(),
                true,
            );
            check(
                &e,
                &format!("refuse-complete-wrong-state-fail{fail}-residual{different_residual}"),
                eq(
                    answer(),
                    actual,
                    side(state(), done(), true, terminal(0, 40, fail, 99)),
                ),
                proof,
                false,
            );
        }
    }
}

#[test]
fn completion_theorem_replays_and_its_collision_is_transactional() {
    let mut e = environment();
    eval::install_cps_observation_into(&mut e).unwrap();
    let before: Vec<_> = e.constants().map(|i| (i.name.clone(), i.clone())).collect();
    eval::install_cps_completion_into(&mut e).unwrap();
    assert_eq!(e.num_constants(), before.len() + 1);
    for (name, old) in before {
        let current = e.get_const(&name).unwrap();
        assert_eq!(current.type_, old.type_);
        assert_eq!(current.value, old.value);
    }
    let info = e
        .get_const(&Name::from_string(eval::LOOP_CPS_COMPLETE_TRANSFER))
        .unwrap();
    check(
        &e,
        "generic-cps-completion",
        info.type_.clone(),
        info.value.clone().unwrap(),
        true,
    );
    let generation = e.generation();
    let constants = e.num_constants();
    assert_eq!(
        eval::install_cps_completion_into(&mut e)
            .unwrap_err()
            .declaration,
        eval::LOOP_CPS_COMPLETE_TRANSFER
    );
    assert_eq!(e.generation(), generation);
    assert_eq!(e.num_constants(), constants);
}
