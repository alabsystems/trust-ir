// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Ordinary typed consumers of the all-resume CPS-prefix observation law.
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
    fn pi(&self, b: Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.ty.clone(),
            b.abstract_fvar(self.id),
        )
    }
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
    eval::install_cps_observation_into(&mut e).unwrap();
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
    assert!(
        tc.check_type(&g, &Expr::prop()).is_ok(),
        "{label}: goal must be well typed"
    );
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
    if let Some(base) = std::env::var_os("TRUST_IR_CPS_OBSERVATION_ARTIFACT_DIR") {
        let dir = std::path::PathBuf::from(base).join(label);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("codec.txt"), "Clean expression v1").unwrap();
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

// Copying an arbitrary Sum is propositionally the identity. It is not reduced
// to the input by inspecting a single selected continuation.
fn copy_sum(sc: &mut Scope, value: Expr) -> Expr {
    let left = sc.local(state());
    let right = sc.local(done());
    cases(
        sc,
        state(),
        done(),
        answer(),
        value,
        left.lam(side(state(), done(), false, left.term.clone())),
        right.lam(side(state(), done(), true, right.term.clone())),
    )
}
fn copy_sum_identity(sc: &mut Scope, value: Expr) -> Expr {
    let v = sc.local(answer());
    let left = sc.local(state());
    let right = sc.local(done());
    let copied = copy_sum(sc, v.term.clone());
    Expr::apps(
        Expr::const_(Name::from_string("Sum.rec"), vec![Level::zero(); 3]),
        [
            state(),
            done(),
            v.lam(eq(answer(), copied, v.term.clone())),
            left.lam(refl(
                answer(),
                side(state(), done(), false, left.term.clone()),
            )),
            right.lam(refl(
                answer(),
                side(state(), done(), true, right.term.clone()),
            )),
            value,
        ],
    )
}
fn pointwise_actual(sc: &mut Scope, canonical: Expr) -> Expr {
    let r = sc.local(Expr::arrow(state(), answer()));
    let s = sc.local(state());
    let result = Expr::apps(canonical, [r.term.clone(), s.term.clone()]);
    let copied = copy_sum(sc, result);
    lams(&[r, s], copied)
}
fn observed_type(sc: &mut Scope, st: Expr, out: Expr, actual: Expr, canonical: Expr) -> Expr {
    let r = sc.local(Expr::arrow(st.clone(), out.clone()));
    let s = sc.local(st);
    r.pi(s.pi(eq(
        out,
        Expr::apps(actual, [r.term.clone(), s.term.clone()]),
        Expr::apps(canonical, [r.term.clone(), s.term.clone()]),
    )))
}
fn pointwise_observed(sc: &mut Scope, canonical: Expr) -> Expr {
    let r = sc.local(Expr::arrow(state(), answer()));
    let s = sc.local(state());
    let result = Expr::apps(canonical, [r.term.clone(), s.term.clone()]);
    let proof = copy_sum_identity(sc, result);
    lams(&[r, s], proof)
}
fn observed_prefix(
    actual: Expr,
    p: Expr,
    f: Expr,
    law: Expr,
    r: Expr,
    count: u64,
    initial: Expr,
) -> Expr {
    z(
        eval::LOOP_CPS_PREFIX_OBSERVATION,
        [
            state(),
            done(),
            answer(),
            actual,
            p,
            f,
            law,
            r,
            n(count),
            initial,
        ],
    )
}
#[test]
fn all_resume_observation_preserves_full_suspension_success_and_error() {
    let e = environment();
    for fail in [false, true] {
        let mut sc = Scope::default();
        let raw = cut(&mut sc, fail);
        let p = pulse(&mut sc, raw);
        let f = finish(&mut sc);
        let r = residual(&mut sc);
        let canonical = cps_step(&mut sc, p.clone(), f.clone());
        let actual = pointwise_actual(&mut sc, canonical.clone());
        let law = pointwise_observed(&mut sc, canonical.clone());
        let ty = observed_type(
            &mut sc,
            state(),
            answer(),
            actual.clone(),
            canonical.clone(),
        );
        check(
            &e,
            &format!("all-resume-premise-fail{fail}"),
            ty,
            law.clone(),
            true,
        );
        let counts: &[u64] = if fail {
            &[0, 1, 2, 8]
        } else {
            &[0, 1, 2, 3, 8]
        };
        for count in counts {
            let expected = if *count == 0 {
                side(state(), done(), false, state_value(2, 40))
            } else if *count == 1 {
                side(state(), done(), false, state_value(1, 41))
            } else if fail {
                side(state(), done(), true, terminal(0, 42, true, 9))
            } else if *count == 2 {
                side(state(), done(), false, state_value(0, 42))
            } else {
                side(state(), done(), true, terminal(0, 42, false, 42))
            };
            let initial = state_value(2, 40);
            check(
                &e,
                &format!("observed-fail{fail}-prefix{count}"),
                eq(
                    answer(),
                    prefix(actual.clone(), r.clone(), *count, initial.clone()),
                    expected,
                ),
                observed_prefix(
                    actual.clone(),
                    p.clone(),
                    f.clone(),
                    law.clone(),
                    r.clone(),
                    *count,
                    initial,
                ),
                true,
            );
        }
        // The actual step has an extra Sum elimination. Its law is supplied by
        // a genuine pointwise proof, not a definitionally equal function.
        let step_ty = Expr::arrow(
            Expr::arrow(state(), answer()),
            Expr::arrow(state(), answer()),
        );
        check(
            &e,
            &format!("refuse-whole-function-refl-fail{fail}"),
            eq(step_ty.clone(), actual, canonical.clone()),
            refl(step_ty, canonical),
            false,
        );
    }
}
#[test]
fn changed_step_pulse_payload_state_and_zero_completion_refuse() {
    let e = environment();
    for which in [
        "step",
        "pulse",
        "output",
        "terminal-state",
        "error-payload",
        "zero",
    ] {
        let mut sc = Scope::default();
        let fail = which == "error-payload";
        let raw = cut(&mut sc, fail);
        let p = pulse(&mut sc, raw);
        let f = finish(&mut sc);
        let r = residual(&mut sc);
        let canonical = cps_step(&mut sc, p.clone(), f.clone());
        let actual = pointwise_actual(&mut sc, canonical.clone());
        let law = pointwise_observed(&mut sc, canonical);
        let count = match which {
            "zero" => 0,
            "terminal-state" => 3,
            "error-payload" | "pulse" => 2,
            _ => 1,
        };
        let replaced = if which == "step" {
            let k = sc.local(Expr::arrow(state(), answer()));
            let s = sc.local(state());
            lams(&[k.clone(), s], Expr::app(k.term, state_value(88, 99)))
        } else {
            actual
        };
        let selected_pulse = if which == "pulse" {
            let changed = cut(&mut sc, true);
            pulse(&mut sc, changed)
        } else {
            p
        };
        let expected = match which {
            "zero" => side(state(), done(), true, terminal(2, 40, false, 40)),
            "terminal-state" => side(state(), done(), true, terminal(0, 40, false, 42)),
            "error-payload" => side(state(), done(), true, terminal(0, 42, true, 10)),
            "pulse" => side(state(), done(), true, terminal(0, 42, true, 9)),
            "output" => side(state(), done(), false, state_value(1, 99)),
            _ => side(state(), done(), false, state_value(1, 41)),
        };
        let initial = state_value(2, 40);
        check(
            &e,
            &format!("refuse-changed-{which}"),
            eq(
                answer(),
                prefix(replaced.clone(), r.clone(), count, initial.clone()),
                expected,
            ),
            observed_prefix(replaced, selected_pulse, f, law, r, count, initial),
            false,
        );
    }
}
#[test]
fn observation_instantiates_a_different_state_terminal_and_answer_type() {
    let e = environment();
    let mut sc = Scope::default();
    let st = Expr::const_str("Bool");
    let d = nat();
    let out = nat();
    let s = sc.local(st.clone());
    let pt = sum(st.clone(), d.clone());
    let pulse = s.lam(choose(
        &mut sc,
        pt,
        s.term.clone(),
        side(st.clone(), d.clone(), true, n(42)),
        side(st.clone(), d.clone(), false, Expr::const_str("Bool.false")),
    ));
    let value = sc.local(d.clone());
    let finish = value.lam(Expr::app(Expr::const_str("Nat.succ"), value.term.clone()));
    let s = sc.local(st.clone());
    let residual = s.lam(n(77));
    let r = sc.local(Expr::arrow(st.clone(), out.clone()));
    let s = sc.local(st.clone());
    let step = lams(
        &[r.clone(), s.clone()],
        cases(
            &mut sc,
            st.clone(),
            d.clone(),
            out.clone(),
            Expr::app(pulse.clone(), s.term.clone()),
            r.term.clone(),
            finish.clone(),
        ),
    );
    let r = sc.local(Expr::arrow(st.clone(), out.clone()));
    let s = sc.local(st.clone());
    let observed = lams(
        &[r.clone(), s.clone()],
        refl(
            out.clone(),
            Expr::apps(step.clone(), [r.term.clone(), s.term.clone()]),
        ),
    );
    check(
        &e,
        "different-types-all-resume",
        observed_type(&mut sc, st.clone(), out.clone(), step.clone(), step.clone()),
        observed.clone(),
        true,
    );
    for (flag, count, expected) in [(true, 0, 77), (true, 1, 43), (true, 8, 43), (false, 8, 77)] {
        let initial = Expr::const_str(if flag { "Bool.true" } else { "Bool.false" });
        let actual = z(
            eval::LOOP_CPS_PREFIX,
            [
                st.clone(),
                out.clone(),
                step.clone(),
                residual.clone(),
                n(count),
                initial.clone(),
            ],
        );
        let proof = z(
            eval::LOOP_CPS_PREFIX_OBSERVATION,
            [
                st.clone(),
                d.clone(),
                out.clone(),
                step.clone(),
                pulse.clone(),
                finish.clone(),
                observed.clone(),
                residual.clone(),
                n(count),
                initial,
            ],
        );
        check(
            &e,
            &format!("different-types-{flag}-{count}"),
            eq(out.clone(), actual, n(expected)),
            proof,
            true,
        );
    }
}
#[test]
fn one_none_continuation_cannot_supply_the_all_resume_premise() {
    let e = environment();
    let mut sc = Scope::default();
    let st = Expr::const_str("Bool");
    let out = z("Option", [nat()]);
    let none = z("Option.none", [nat()]);
    let s = sc.local(st.clone());
    let pulse = s.lam(side(st.clone(), st.clone(), false, s.term.clone()));
    let d = sc.local(st.clone());
    let finish = d.lam(z("Option.some", [nat(), n(99)]));
    let r = sc.local(Expr::arrow(st.clone(), out.clone()));
    let s = sc.local(st.clone());
    let value = sc.local(out.clone());
    let number = sc.local(nat());
    let changed = Expr::apps(
        Expr::const_(
            Name::from_string("Option.rec"),
            vec![Level::succ(Level::zero()), Level::zero()],
        ),
        [
            nat(),
            value.lam(out.clone()),
            none.clone(),
            number.lam(z(
                "Option.some",
                [
                    nat(),
                    Expr::app(Expr::const_str("Nat.succ"), number.term.clone()),
                ],
            )),
            Expr::app(r.term.clone(), s.term.clone()),
        ],
    );
    let actual = lams(&[r, s], changed);
    let r = sc.local(Expr::arrow(st.clone(), out.clone()));
    let s = sc.local(st.clone());
    let canonical = lams(
        &[r.clone(), s.clone()],
        Expr::app(r.term.clone(), s.term.clone()),
    );
    let s = sc.local(st.clone());
    let none_resume = s.lam(none.clone());
    let s = sc.local(st.clone());
    let none_goal = s.pi(eq(
        out.clone(),
        Expr::apps(actual.clone(), [none_resume, s.term.clone()]),
        none.clone(),
    ));
    let none_proof = s.lam(refl(out.clone(), none.clone()));
    check(&e, "one-none-premise-is-true", none_goal, none_proof, true);
    let r = sc.local(Expr::arrow(st.clone(), out.clone()));
    let s = sc.local(st.clone());
    let fabricated_all = lams(&[r, s], refl(out.clone(), none.clone()));
    check(
        &e,
        "refuse-none-as-all-resume",
        observed_type(&mut sc, st.clone(), out.clone(), actual.clone(), canonical),
        fabricated_all.clone(),
        false,
    );
    let s = sc.local(st.clone());
    let residual = s.lam(z("Option.some", [nat(), n(0)]));
    let initial = Expr::const_str("Bool.true");
    for count in [0, 2] {
        let actual_prefix = z(
            eval::LOOP_CPS_PREFIX,
            [
                st.clone(),
                out.clone(),
                actual.clone(),
                residual.clone(),
                n(count),
                initial.clone(),
            ],
        );
        let expected = z("Option.some", [nat(), n(count)]);
        // This independently checks the actual step's different behavior at
        // Some; it grants no prefix-observation premise.
        check(
            &e,
            &format!("one-none-actual-prefix-{count}"),
            eq(out.clone(), actual_prefix.clone(), expected),
            refl(out.clone(), actual_prefix.clone()),
            true,
        );
        let forged = z(
            eval::LOOP_CPS_PREFIX_OBSERVATION,
            [
                st.clone(),
                st.clone(),
                out.clone(),
                actual.clone(),
                pulse.clone(),
                finish.clone(),
                fabricated_all.clone(),
                residual.clone(),
                n(count),
                initial.clone(),
            ],
        );
        check(
            &e,
            &format!("refuse-none-prefix-transport-{count}"),
            eq(out.clone(), actual_prefix, z("Option.some", [nat(), n(0)])),
            forged,
            false,
        );
    }
}
#[test]
fn generic_observation_preserves_existing_declarations_and_limits() {
    let mut e = eval::build_environment().unwrap();
    eval::install_loop_into(&mut e).unwrap();
    eval::install_cps_loop_into(&mut e).unwrap();
    let before: Vec<_> = e.constants().map(|i| (i.name.clone(), i.clone())).collect();
    let options = [
        e.get_option("maxHeartbeats").cloned(),
        e.get_option("tcMaxCacheEntries").cloned(),
    ];
    let mode = e.mode();
    eval::install_cps_observation_into(&mut e).unwrap();
    assert_eq!(e.num_constants(), before.len() + 1);
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
    let info = e
        .get_const(&Name::from_string(eval::LOOP_CPS_PREFIX_OBSERVATION))
        .unwrap();
    check(
        &e,
        "generic-observation-theorem",
        info.type_.clone(),
        info.value.clone().unwrap(),
        true,
    );
}
#[test]
fn observation_installation_requires_prerequisite_and_rejects_collision_before_mutation() {
    let mut absent = Environment::default();
    let generation = absent.generation();
    let count = absent.num_constants();
    assert!(eval::install_cps_observation_into(&mut absent).is_err());
    assert_eq!(absent.generation(), generation);
    assert_eq!(absent.num_constants(), count);
    let mut collision = Environment::default();
    collision
        .add_decl(clean_kernel::Declaration::Definition {
            name: Name::from_string(eval::LOOP_CPS_PREFIX_OBSERVATION),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: Expr::prop(),
            is_reducible: true,
        })
        .unwrap();
    let generation = collision.generation();
    let count = collision.num_constants();
    assert_eq!(
        eval::install_cps_observation_into(&mut collision)
            .unwrap_err()
            .declaration,
        eval::LOOP_CPS_PREFIX_OBSERVATION
    );
    assert_eq!(collision.generation(), generation);
    assert_eq!(collision.num_constants(), count);
}
