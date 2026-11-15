// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Ordinary shared-assembler arithmetic consumers, not a program execution,
//! extracted Rust/TLA, default-vocabulary or native-refinement proof. Exact
//! source endpoints are constructed independently of the candidate producer.
//! Actual checked Clean roots and strict default2M kernel replay are required.

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker, TypeError};
use std::sync::OnceLock;
use trust_ir_build::{
    core_execution::{Assembler, Limits, PendingEquality},
    scoped_local::LocalScope,
};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}

fn eq_bool(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c("Bool"), left, right],
    )
}

// This mathematical source claim does not project producer metadata or use a
// supplied remainder answer. It preserves the selected original definition.
fn claim(operation: &str, dividend: Expr, divisor: Expr, upper_bound: Expr) -> Expr {
    eq_bool(
        app(
            "ir_nat_ltb",
            [app(operation, [dividend, divisor]), upper_bound],
        ),
        c("Bool.true"),
    )
}

fn environment() -> &'static Environment {
    static ENVIRONMENT: OnceLock<Environment> = OnceLock::new();
    ENVIRONMENT.get_or_init(|| {
        let mut owner =
            clean_verify::eval_ir::build_positive_division_byte_prelude_spec_v1_with_stack()
                .expect("actual public checked positive-division owner");
        for law in [
            "ir_nat_rem_positive_bound_v1",
            "ir_nat_rem_total_positive_bound_v1",
        ] {
            assert!(owner.env().get_const(&Name::from_string(law)).is_none());
        }
        owner
            .install_eval_ir_total_restoring_division_laws_v1()
            .expect("actual public checked total restoring package");
        owner.env().clone()
    })
}

fn limits(operations: usize, locals: usize) -> Limits {
    Limits {
        max_operations: operations,
        max_locals: locals,
        max_list_items: 1,
        max_lookup_candidates: 1,
        lookup_heartbeats: 1,
        lookup_cache_entries: 1,
    }
}

fn derive(
    assembler: &mut Assembler<'_>,
    total: bool,
    dividend: Expr,
    predecessor: Expr,
) -> PendingEquality {
    if total {
        assembler.total_remainder_positive_bound(dividend, predecessor)
    } else {
        assembler.remainder_positive_bound(dividend, predecessor)
    }
    .expect("charged pending candidate, not proof admission")
}

fn replay(proposition: &Expr, proof: &Expr, accepted: bool) {
    assert!(!proposition.has_fvar_quick() && !proposition.has_loose_bvars());
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
    let mut kernel = TypeChecker::new(environment());
    kernel.set_allow_unsafe(false);
    kernel.set_allow_partial(false);
    assert_eq!(clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT, 2_000_000);
    assert_eq!(kernel.heartbeat_limit(), 2_000_000);
    // No heartbeat/cache/declaration reset or raised work allowance.
    kernel
        .check_type(proposition, &Expr::sort(Level::zero()))
        .expect("independent source proposition is well typed");
    let result = kernel.check_type(proof, proposition);
    assert!(
        !kernel.heartbeat_spent(),
        "budget is not a verdict: {result:?}"
    );
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    if accepted {
        result.expect("actual independent strict kernel replay");
        let audit = environment().audit_certification(proposition, proof);
        assert!(audit.is_certified(), "{audit:#?}");
    } else {
        assert!(
            matches!(result, Err(TypeError::TypeMismatch { .. })),
            "{result:?}"
        );
    }
}

fn concrete(total: bool, dividend: Expr, predecessor: Expr) -> PendingEquality {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
    let candidate = derive(&mut assembler, total, dividend, predecessor);
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.local_scope().allocated(), 0);
    candidate
}

#[test]
fn symbolic_remainder_bounds_replay_without_answer_premises_and_have_zero_axiom_roots() {
    for (total, operation, law) in [
        (false, "ir_nat_rem", "ir_nat_rem_positive_bound_v1"),
        (
            true,
            "ir_nat_rem_total_v1",
            "ir_nat_rem_total_positive_bound_v1",
        ),
    ] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits(3, 2)).unwrap();
        let dividend = assembler.local(c("Nat")).unwrap();
        let predecessor = assembler.local(c("Nat")).unwrap();
        let candidate = derive(
            &mut assembler,
            total,
            dividend.term().clone(),
            predecessor.term().clone(),
        );
        let proof = assembler
            .local_scope()
            .close(&dividend.lam(predecessor.lam(candidate.term().clone())))
            .unwrap();
        // An independently constructed telescope and body, not candidate.goal.
        let divisor = app("Nat.succ", [Expr::bvar(0)]);
        let proposition = Expr::pi(
            BinderInfo::Default,
            c("Nat"),
            Expr::pi(
                BinderInfo::Default,
                c("Nat"),
                claim(operation, Expr::bvar(1), divisor.clone(), divisor),
            ),
        );
        replay(&proposition, &proof, true);
        let key = Name::from_string(law);
        let audit = environment().audit_certification(&proposition, &proof);
        assert!(audit.dependencies.contains(&key));
        assert!(environment().axiom_deps(&key).unwrap().is_empty());
        assert!(
            environment()
                .foundational_axiom_deps(&key)
                .unwrap()
                .is_empty()
        );
        assert!(environment().trust_marker_deps(&key).unwrap().is_empty());
        assert_eq!(assembler.operations(), 3);
        assert_eq!(assembler.local_scope().allocated(), 2);
    }
}

#[test]
fn remainder_bound_candidates_replay_full64_moduli_and_oversized_dividends() {
    let limit = app("ir_nat_pow2", [Expr::nat_lit(64)]);
    for (total, operation) in [(false, "ir_nat_rem"), (true, "ir_nat_rem_total_v1")] {
        for dividend in [
            Expr::nat_lit(0),
            Expr::nat_lit(u64::MAX),
            app("Nat.succ", [Expr::nat_lit(u64::MAX)]),
            app(
                "Nat.mul",
                [Expr::nat_lit(u64::MAX), Expr::nat_lit(u64::MAX)],
            ),
        ] {
            let mut scope = LocalScope::new();
            let mut assembler = Assembler::new(&mut scope, limits(2, 1)).unwrap();
            let candidate = derive(
                &mut assembler,
                total,
                dividend.clone(),
                Expr::nat_lit(u64::MAX),
            );
            let proposition = claim(operation, dividend, limit.clone(), limit.clone());
            let independent_left = (*proposition.get_app_args()[1]).clone();
            let converted = assembler
                .convert_endpoints(candidate, independent_left, c("Bool.true"))
                .unwrap();
            replay(&proposition, converted.term(), true);
            assert_eq!(assembler.operations(), 2);
            assert_eq!(assembler.local_scope().allocated(), 0);
        }
    }
}

#[test]
fn remainder_bound_candidates_reject_false_bounds_zero_projection_and_wrong_types_semantically() {
    for (total, operation, quotient) in [
        (false, "ir_nat_rem", "ir_nat_div"),
        (true, "ir_nat_rem_total_v1", "ir_nat_div_total_v1"),
    ] {
        let one = Expr::nat_lit(1);
        let two = Expr::nat_lit(2);
        let candidate = concrete(total, one.clone(), one.clone());
        replay(
            &claim(operation, one.clone(), two.clone(), two.clone()),
            candidate.term(),
            true,
        );
        for (divisor, bound) in [
            (two.clone(), one.clone()),
            (Expr::nat_lit(0), Expr::nat_lit(0)),
        ] {
            replay(
                &claim(operation, one.clone(), divisor, bound),
                candidate.term(),
                false,
            );
        }
        let candidate = concrete(total, Expr::nat_lit(17), Expr::nat_lit(0));
        replay(
            &claim(operation, Expr::nat_lit(17), one.clone(), one.clone()),
            candidate.term(),
            true,
        );
        replay(
            &claim(quotient, Expr::nat_lit(17), one.clone(), one.clone()),
            candidate.term(),
            false,
        );

        // The Expr-input API is intentionally only candidate construction.
        // Actual Nat typing is checked here, not asserted by matching metadata.
        let malformed = concrete(total, c("Bool.true"), one.clone());
        replay(
            &claim(operation, one, two.clone(), two),
            malformed.term(),
            false,
        );
    }
}
