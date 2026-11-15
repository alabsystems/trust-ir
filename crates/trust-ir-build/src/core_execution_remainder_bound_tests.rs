// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Structural/work checks only. Uninstalled candidates grant no proof facts.

use super::*;

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
) -> Result<PendingEquality> {
    if total {
        assembler.total_remainder_positive_bound(dividend, predecessor)
    } else {
        assembler.remainder_positive_bound(dividend, predecessor)
    }
}

// Independent literal oracle, not the producer's selector or predicate.
fn expected(total: bool, dividend: Expr, predecessor: Expr) -> (Expr, Expr) {
    let divisor = Expr::apps(Expr::const_str("Nat.succ"), [predecessor.clone()]);
    let (operation, law) = if total {
        ("ir_nat_rem_total_v1", "ir_nat_rem_total_positive_bound_v1")
    } else {
        ("ir_nat_rem", "ir_nat_rem_positive_bound_v1")
    };
    let remainder = Expr::apps(
        Expr::const_str(operation),
        [dividend.clone(), divisor.clone()],
    );
    (
        Expr::apps(Expr::const_str("ir_nat_ltb"), [remainder, divisor]),
        Expr::apps(Expr::const_str(law), [dividend, predecessor]),
    )
}

#[test]
fn remainder_bounds_retain_exact_original_total_endpoints_and_two_law_arguments() {
    for total in [false, true] {
        for (word, predecessor) in [
            (nat(0), nat(0)),
            (nat(17), nat(4)),
            (constant("symbolic_word"), constant("symbolic_predecessor")),
        ] {
            let mut scope = Scope::new();
            let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
            let proof = derive(&mut assembler, total, word.clone(), predecessor.clone()).unwrap();
            let (predicate, term) = expected(total, word, predecessor);
            proof
                .endpoints(&constant("Bool"), &predicate, &constant("Bool.true"))
                .unwrap();
            assert_eq!(proof.term(), &term);
            assert_eq!(proof.term().get_app_args().len(), 2);
            assert_eq!(assembler.operations(), 1);
            assert_eq!(assembler.locals, 0);
            assert_eq!(assembler.local_scope().allocated(), 0);
        }
    }
}

#[test]
fn remainder_bounds_close_all_nat_locals_without_answer_or_fit_hypotheses() {
    for total in [false, true] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(3, 2)).unwrap();
        let word = assembler.local(constant("Nat")).unwrap();
        let predecessor = assembler.local(constant("Nat")).unwrap();
        let proof = derive(
            &mut assembler,
            total,
            word.term().clone(),
            predecessor.term().clone(),
        )
        .unwrap();
        let closed = assembler
            .local_scope()
            .close(&word.lam(predecessor.lam(proof.term().clone())))
            .unwrap();
        let (_, body) = expected(total, Expr::bvar(1), Expr::bvar(0));
        let independent = Expr::lam(
            clean_kernel::BinderInfo::Default,
            constant("Nat"),
            Expr::lam(clean_kernel::BinderInfo::Default, constant("Nat"), body),
        );
        assert_eq!(closed, independent);
        assert!(!closed.has_fvar_quick() && !closed.has_loose_bvars());
        assert_eq!(assembler.operations(), 3);
        assert_eq!(assembler.locals, 2);
        assert_eq!(assembler.local_scope().allocated(), 2);
    }
}

#[test]
fn remainder_bounds_keep_full64_positive_modulus_and_unbounded_dividend_expression() {
    for total in [false, true] {
        let word = app("Nat.mul", [nat(u64::MAX), nat(u64::MAX)]);
        let predecessor = nat(u64::MAX);
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
        let proof = derive(&mut assembler, total, word.clone(), predecessor.clone()).unwrap();
        let (predicate, term) = expected(total, word, predecessor);
        assert_eq!(proof.left(), &predicate);
        assert_eq!(proof.term(), &term);
        assert_eq!(proof.right(), &constant("Bool.true"));
        assert!(!proof.term().has_fvar_quick() && !proof.term().has_loose_bvars());
        // succ(MAX) is retained, not a wrapped host-u64 zero or fixed4200.
        assert_eq!(
            proof.left().get_app_args()[1],
            &app("Nat.succ", [nat(u64::MAX)])
        );
        assert_eq!(assembler.operations(), 1);
    }
}

#[test]
fn remainder_bounds_share_existing_charges_and_never_refund_failed_composition() {
    for total in [false, true] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(2, 1)).unwrap();
        let proof = derive(&mut assembler, total, nat(1), nat(1)).unwrap();
        let forged = PendingEquality::candidate(
            constant("Bool"),
            constant("Bool.false"),
            constant("Bool.true"),
            constant("untrusted_forged_bound"),
        );
        assert!(
            assembler
                .compose(proof, forged)
                .err()
                .unwrap()
                .contains("composition middle endpoint")
        );
        assert_eq!(assembler.operations(), 2);
        assert!(
            derive(&mut assembler, total, nat(0), nat(0))
                .err()
                .unwrap()
                .contains("operation budget exceeded")
        );
        assert_eq!(assembler.operations(), 2);
        assert_eq!(assembler.local_scope().allocated(), 0);

        assembler.operations = usize::MAX;
        assert_eq!(
            derive(&mut assembler, total, nat(0), nat(0)).err().unwrap(),
            "operation counter overflow"
        );
        assert_eq!(assembler.operations(), usize::MAX);
    }
}
