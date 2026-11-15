// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Ordinary shared-arithmetic consumers, not fetched/source/native execution.

use super::*;
use clean_kernel::{BinderInfo, KernelTypeError};
use std::sync::OnceLock;

fn limits(operations: usize) -> Limits {
    Limits {
        max_operations: operations,
        max_locals: 1,
        max_list_items: 1,
        max_lookup_candidates: 1,
        lookup_heartbeats: 1,
        lookup_cache_entries: 1,
    }
}

fn environment() -> &'static Environment {
    static ENVIRONMENT: OnceLock<Environment> = OnceLock::new();
    ENVIRONMENT.get_or_init(|| {
        clean_verify::eval_ir::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
            .expect("actual public checked canonical arithmetic owner")
            .env()
            .clone()
    })
}

fn checker() -> TypeChecker<'static> {
    let mut tc = TypeChecker::new(environment());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    assert_eq!(tc.heartbeat_limit(), 2_000_000);
    tc
}

fn replay(claim: &Expr, term: &Expr, accepted: bool) {
    assert!(!claim.has_fvar_quick() && !claim.has_loose_bvars());
    assert!(!term.has_fvar_quick() && !term.has_loose_bvars());
    checker().check_type(claim, &Expr::prop()).unwrap();
    let claim_bytes = trust_ir::proof::encode_clean_expr_dag_v2(claim).unwrap();
    let term_bytes = trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap();
    let decoded_claim = trust_ir::proof::decode_clean_expr_dag_v2(&claim_bytes).unwrap();
    let decoded_term = trust_ir::proof::decode_clean_expr_dag_v2(&term_bytes).unwrap();
    assert_eq!(&decoded_claim, claim);
    assert_eq!(&decoded_term, term);
    for (goal, proof) in [(claim, term), (&decoded_claim, &decoded_term)] {
        let tc = checker();
        let result = tc.check_type(proof, goal);
        assert!(!tc.heartbeat_spent(), "budget is not a verdict: {result:?}");
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        if accepted {
            result.unwrap();
            let audit = environment().audit_certification(goal, proof);
            assert!(audit.is_certified(), "{audit:#?}");
            for name in &audit.dependencies {
                assert!(environment().axiom_deps(name).unwrap().is_empty());
                assert!(
                    environment()
                        .foundational_axiom_deps(name)
                        .unwrap()
                        .is_empty()
                );
                assert!(environment().trust_marker_deps(name).unwrap().is_empty());
            }
        } else {
            assert!(
                matches!(result, Err(KernelTypeError::TypeMismatch { .. })),
                "{result:?}"
            );
        }
    }
}

// Independent source propositions, not projections of pending metadata.
fn raw(bits: u64, word: Expr) -> Expr {
    Expr::apps(Expr::const_str("ir_wrap"), [Expr::nat_lit(bits), word])
}

fn bool_claim(bits: u64, word: Expr) -> Expr {
    eq(
        &constant("Bool"),
        app(
            "ir_nat_ltb",
            [raw(bits, word), app("ir_nat_pow2", [nat(bits)])],
        ),
        constant("Bool.true"),
    )
}

fn strict_claim(bits: u64, word: Expr) -> Expr {
    app("Nat.lt", [raw(bits, word), app("ir_nat_pow2", [nat(bits)])])
}

fn derive(bits: u64, input: Expr) -> WrappedWordBound {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(4)).unwrap();
    let candidate = assembler.wrapped_word_bound(bits, input).unwrap();
    assert_eq!(assembler.operations(), 4);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 0);
    assert!(assembler.cons_congruence.is_none());
    assert!(assembler.run_one_candidate.is_none());
    candidate
}

#[test]
fn wrapped_word_bounds_retain_raw_all_widths_and_neutral_argument_placement() {
    for bits in 1..=64 {
        for input in [nat(0), constant("caller_word"), Expr::bvar(2)] {
            let candidate = derive(bits, input.clone());
            assert_eq!(candidate.word, raw(bits, input.clone()));
            assert_eq!(
                candidate.fits.proposition(),
                bool_claim(bits, input.clone())
            );
            assert_eq!(
                candidate.strict_bound.proposition(),
                &strict_claim(bits, input.clone())
            );
            for proof in [candidate.fits.term(), candidate.strict_bound.term()] {
                let head = proof.get_app_fn();
                assert!(matches!(head.kind(), ExprKind::Lam(_, _, _)));
                assert!(!head.has_fvar_quick() && !head.has_loose_bvars());
                assert_eq!(proof.get_app_args().as_slice(), &[&input]);
            }
        }
    }
}

#[test]
fn wrapped_word_symbolic_bounds_replay_all_widths_without_input_or_answer_premises() {
    for bits in 1..=64 {
        let candidate = derive(bits, Expr::bvar(0));
        for (claim, proof) in [
            (bool_claim(bits, Expr::bvar(0)), candidate.fits.term()),
            (
                strict_claim(bits, Expr::bvar(0)),
                candidate.strict_bound.term(),
            ),
        ] {
            let proposition = Expr::pi(BinderInfo::Default, constant("Nat"), claim);
            let term = Expr::lam(BinderInfo::Default, constant("Nat"), proof.clone());
            replay(&proposition, &term, true);
        }
    }
}

#[test]
fn wrapped_word_concrete_high_bits_and_unbounded_inputs_replay_original_and_dag() {
    for bits in [1, 7, 8, 16, 31, 32, 63, 64] {
        for word in [0, 1, 1_u64 << 63, u64::MAX] {
            let candidate = derive(bits, nat(word));
            replay(&bool_claim(bits, nat(word)), candidate.fits.term(), true);
            replay(
                &strict_claim(bits, nat(word)),
                candidate.strict_bound.term(),
                true,
            );
        }
    }
    // The input is not restricted to a u64 literal or already-canonical word.
    for input in [
        app("Nat.succ", [nat(u64::MAX)]),
        app("Nat.mul", [nat(u64::MAX), nat(u64::MAX)]),
    ] {
        let candidate = derive(64, input.clone());
        replay(&bool_claim(64, input.clone()), candidate.fits.term(), true);
        replay(
            &strict_claim(64, input),
            candidate.strict_bound.term(),
            true,
        );
    }
}

#[test]
fn wrapped_word_caller_free_and_de_bruijn_inputs_are_not_recaptured() {
    let mut scope = Scope::new();
    let first = scope.try_local(constant("Nat")).unwrap();
    let second = scope.try_local(constant("Nat")).unwrap();
    let mut assembler = Assembler::new(&mut scope, limits(4)).unwrap();
    let input = app("Nat.add", [first.term().clone(), second.term().clone()]);
    let candidate = assembler.wrapped_word_bound(16, input.clone()).unwrap();
    assert_eq!(assembler.operations(), 4);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 2);
    for proof in [candidate.fits.term(), candidate.strict_bound.term()] {
        assert!(!proof.get_app_fn().has_fvar_quick());
        assert!(!proof.get_app_fn().has_loose_bvars());
        assert_eq!(proof.get_app_args().as_slice(), &[&input]);
    }
    let independent_input = app("Nat.add", [Expr::bvar(1), Expr::bvar(0)]);
    for (claim, proof) in [
        (
            bool_claim(16, independent_input.clone()),
            candidate.fits.term(),
        ),
        (
            strict_claim(16, independent_input),
            candidate.strict_bound.term(),
        ),
    ] {
        let term = assembler
            .local_scope()
            .close(&first.lam(second.lam(proof.clone())))
            .unwrap();
        let proposition = Expr::pi(
            BinderInfo::Default,
            constant("Nat"),
            Expr::pi(BinderInfo::Default, constant("Nat"), claim),
        );
        replay(&proposition, &term, true);
    }
    let input = app("Nat.add", [Expr::bvar(1), Expr::bvar(0)]);
    let candidate = derive(8, input.clone());
    let term = Expr::lam(
        BinderInfo::Default,
        constant("Nat"),
        Expr::lam(
            BinderInfo::Default,
            constant("Nat"),
            candidate.fits.term().clone(),
        ),
    );
    let proposition = Expr::pi(
        BinderInfo::Default,
        constant("Nat"),
        Expr::pi(BinderInfo::Default, constant("Nat"), bool_claim(8, input)),
    );
    replay(&proposition, &term, true);
}

#[test]
fn wrapped_word_false_raw_width_type_and_non_nat_candidates_are_kernel_refused() {
    let candidate = derive(8, nat(255));
    replay(&bool_claim(8, nat(255)), candidate.fits.term(), true);
    for (changed_word, changed_bound, endpoint) in [
        (
            nat(256),
            app("ir_nat_pow2", [nat(8)]),
            constant("Bool.true"),
        ),
        (
            raw(8, nat(255)),
            app("ir_nat_pow2", [nat(7)]),
            constant("Bool.true"),
        ),
        (
            raw(8, nat(255)),
            app("ir_nat_pow2", [nat(8)]),
            constant("Bool.false"),
        ),
    ] {
        let false_goal = eq(
            &constant("Bool"),
            app("ir_nat_ltb", [changed_word.clone(), changed_bound.clone()]),
            endpoint,
        );
        replay(&false_goal, candidate.fits.term(), false);
    }
    replay(
        &app(
            "Nat.lt",
            [candidate.word.clone(), app("ir_nat_pow2", [nat(7)])],
        ),
        candidate.strict_bound.term(),
        false,
    );
    replay(
        &eq(&constant("Nat"), nat(0), nat(0)),
        candidate.fits.term(),
        false,
    );
    // Rust candidate metadata cannot make a non-Nat actual argument valid.
    let ill_typed = derive(8, constant("Bool.true"));
    replay(&bool_claim(8, nat(0)), ill_typed.fits.term(), false);
    replay(
        &strict_claim(8, nat(0)),
        ill_typed.strict_bound.term(),
        false,
    );
}

#[test]
fn wrapped_word_width_preflight_and_partial_or_overflowing_work_never_refund() {
    for bits in [0, 65, u64::MAX] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(1)).unwrap();
        assert_eq!(
            assembler.wrapped_word_bound(bits, nat(0)).err().unwrap(),
            "wrapped word bound requires a width in 1..=64"
        );
        assert_eq!(assembler.operations(), 0);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
    for cap in 1..=4 {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(cap)).unwrap();
        let candidate = assembler.wrapped_word_bound(8, nat(256));
        if cap < 4 {
            assert_eq!(
                candidate.err().unwrap(),
                "execution construction operation budget exceeded"
            );
        } else {
            candidate.unwrap();
        }
        assert_eq!(assembler.operations(), cap);
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.local_scope().allocated(), 0);
        assert_eq!(
            assembler.wrapped_word_bound(16, nat(1)).err().unwrap(),
            "execution construction operation budget exceeded"
        );
        assert_eq!(assembler.operations(), cap);
        assembler.operations = usize::MAX;
        assert_eq!(
            assembler.wrapped_word_bound(16, nat(1)).err().unwrap(),
            "operation counter overflow"
        );
        assert_eq!(assembler.operations(), usize::MAX);
        assert_eq!(assembler.local_scope().allocated(), 0);
        assert_eq!(
            assembler.wrapped_word_bound(0, nat(0)).err().unwrap(),
            "wrapped word bound requires a width in 1..=64"
        );
        assert_eq!(assembler.operations(), usize::MAX);
    }
    let mut scope = Scope::new();
    assert!(Assembler::new(&mut scope, limits(0)).is_err());
    assert_eq!(scope.allocated(), 0);
}
