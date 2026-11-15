// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Exact syntax and charged work only; pending metadata is not proof authority.

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

fn bound(word: Expr, evidence: Expr) -> PendingProof {
    PendingProof::candidate(
        app("Nat.lt", [word, app("ir_nat_pow2", [nat(64)])]),
        evidence,
    )
}

// Literal independent expression, including the original false/true branch
// ordering. Do not obtain the expected word from producer endpoints.
fn conditional(a: Expr, b: Expr) -> Expr {
    let sum = app("Nat.add", [a, b]);
    let limit = app("ir_nat_pow2", [nat(64)]);
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                constant("Bool"),
                constant("Nat"),
            ),
            app("Nat.sub", [sum.clone(), limit.clone()]),
            sum.clone(),
            app("ir_nat_ltb", [sum, limit]),
        ],
    )
}

#[test]
fn wrapped_add_retains_raw_word_conditional_order_and_checked_bound_chain() {
    for (a, b) in [
        (constant("a"), constant("b")),
        (nat(0), nat(0)),
        (nat(u64::MAX), nat(1)),
        (nat(u64::MAX), nat(u64::MAX)),
    ] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
        let (raw, equality, output_bound) = assembler
            .byte_add_word64_canonical(
                a.clone(),
                b.clone(),
                bound(a.clone(), constant("lhs_evidence")),
                bound(b.clone(), constant("rhs_evidence")),
            )
            .unwrap();
        let limit = app("ir_nat_pow2", [nat(64)]);
        let expected_raw = app("ir_wrap", [nat(64), app("Nat.add", [a.clone(), b.clone()])]);
        let fast = conditional(a.clone(), b.clone());
        let arguments = [
            nat(64),
            a.clone(),
            b.clone(),
            app(
                "ir_byte_ltb_of_lt_v1",
                [a, limit.clone(), constant("lhs_evidence")],
            ),
            app(
                "ir_byte_ltb_of_lt_v1",
                [b, limit.clone(), constant("rhs_evidence")],
            ),
        ];
        let wrap_proof = app("ir_byte_add_wrap_bounded_sum_v1", arguments.clone());
        equality
            .endpoints(&constant("Nat"), &expected_raw, &fast)
            .unwrap();
        assert_eq!(raw, expected_raw);
        assert_eq!(*equality.term(), wrap_proof);
        assert_eq!(
            *output_bound.proposition(),
            app("Nat.lt", [raw.clone(), limit.clone()])
        );
        let observer = Expr::lam(
            clean_kernel::BinderInfo::Default,
            constant("Nat"),
            app("ir_nat_ltb", [Expr::bvar(0), limit.clone()]),
        );
        let congruence = app(
            "ir_eq_cong",
            [
                constant("Nat"),
                constant("Bool"),
                observer.clone(),
                raw.clone(),
                fast.clone(),
                wrap_proof,
            ],
        );
        let chain = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            ),
            [
                constant("Bool"),
                app("ir_nat_ltb", [raw.clone(), limit.clone()]),
                app("ir_nat_ltb", [fast, limit.clone()]),
                constant("Bool.true"),
                congruence,
                app("ir_byte_add_word_bound_v1", arguments),
            ],
        );
        assert_eq!(
            *output_bound.term(),
            app("ir_byte_separation_lt_of_ltb_v1", [raw, limit, chain])
        );
        assert!(!observer.has_fvar_quick() && !observer.has_loose_bvars());
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.local_scope().allocated(), 0);
        assert!(assembler.cons_congruence.is_none());
        assert!(assembler.run_one_candidate.is_none());
    }
}

#[test]
fn wrapped_add_refuses_wrong_width_operand_relation_and_bound_order_after_charging() {
    let a = constant("a");
    let b = constant("b");
    let limit = app("ir_nat_pow2", [nat(64)]);
    let malformed = [
        bound(b.clone(), constant("wrong_operand")),
        PendingProof::candidate(
            app("Nat.lt", [a.clone(), app("ir_nat_pow2", [nat(32)])]),
            constant("wrong_width"),
        ),
        PendingProof::candidate(
            app("Nat.lt", [limit.clone(), a.clone()]),
            constant("reversed"),
        ),
        PendingProof::candidate(
            app("Nat.le", [a.clone(), limit.clone()]),
            constant("non_strict"),
        ),
        PendingProof::candidate(
            eq(
                &constant("Bool"),
                app("ir_nat_ltb", [a.clone(), limit]),
                constant("Bool.true"),
            ),
            constant("wrong_type"),
        ),
    ];
    for side in ["lhs", "rhs"] {
        for bad in &malformed {
            let mut scope = Scope::new();
            let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
            let result = if side == "lhs" {
                assembler.byte_add_word64_canonical(
                    a.clone(),
                    b.clone(),
                    bad.clone(),
                    bound(b.clone(), constant("good")),
                )
            } else {
                assembler.byte_add_word64_canonical(
                    b.clone(),
                    a.clone(),
                    bound(b.clone(), constant("good")),
                    bad.clone(),
                )
            };
            assert!(
                result
                    .err()
                    .unwrap()
                    .contains(&format!("wrapped add {side} canonical word bound"))
            );
            assert_eq!(assembler.operations(), 1);
            assert_eq!(assembler.local_scope().allocated(), 0);
        }
    }
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
    assert!(
        assembler
            .byte_add_word64_canonical(
                a.clone(),
                b.clone(),
                bound(b, constant("b")),
                bound(a, constant("a")),
            )
            .is_err(),
        "swapped premise roles cannot be silently commuted"
    );
    assert_eq!(assembler.operations(), 1);
}

#[test]
fn wrapped_add_closes_caller_locals_and_leaves_legacy_carrier_terms_and_charges_unchanged() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(5, 4)).unwrap();
    let a = assembler.local(constant("Nat")).unwrap();
    let b = assembler.local(constant("Nat")).unwrap();
    let ha = assembler
        .local(
            bound(a.term().clone(), constant("unused"))
                .proposition()
                .clone(),
        )
        .unwrap();
    let hb = assembler
        .local(
            bound(b.term().clone(), constant("unused"))
                .proposition()
                .clone(),
        )
        .unwrap();
    let (_, equality, proof) = assembler
        .byte_add_word64_canonical(
            a.term().clone(),
            b.term().clone(),
            bound(a.term().clone(), ha.term().clone()),
            bound(b.term().clone(), hb.term().clone()),
        )
        .unwrap();
    for term in [equality.term(), proof.term()] {
        let closed = assembler
            .local_scope()
            .close(&a.lam(b.lam(ha.lam(hb.lam(term.clone())))))
            .unwrap();
        assert!(!closed.has_fvar_quick() && !closed.has_loose_bvars());
    }
    assert_eq!(assembler.operations(), 5);
    assert_eq!(assembler.locals, 4);
    assert_eq!(assembler.local_scope().allocated(), 4);
    for signed in [false, true] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(2, 1)).unwrap();
        let a = nat(u64::MAX);
        let b = nat(1);
        let ha = bound(a.clone(), constant("ha"));
        let hb = bound(b.clone(), constant("hb"));
        let old = if signed {
            assembler.byte_add_i64_canonical(a.clone(), b.clone(), ha.clone(), hb.clone())
        } else {
            assembler.byte_add_u64_canonical(a.clone(), b.clone(), ha.clone(), hb.clone())
        }
        .unwrap();
        let new = assembler
            .byte_add_word64_canonical(a.clone(), b.clone(), ha, hb)
            .unwrap();
        assert_eq!(
            old.0,
            app("IRScalar.int_", [conditional(a.clone(), b.clone())])
        );
        assert_eq!(*new.1.right(), conditional(a, b));
        assert_eq!(
            old.1.term().get_app_fn(),
            &constant(if signed {
                "ir_byte_add_int_canonical_v1"
            } else {
                "ir_byte_add_uint_canonical_v1"
            })
        );
        assert_eq!(old.1.term().get_app_args().len(), 5);
        assert_eq!(assembler.operations(), 2);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
}

#[test]
fn wrapped_add_spent_failed_and_overflowing_work_counters_never_refund_or_publish() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
    assert!(
        assembler
            .byte_add_word64_canonical(
                nat(1),
                nat(2),
                bound(nat(2), constant("bad")),
                bound(nat(2), constant("good")),
            )
            .is_err()
    );
    assert_eq!(assembler.operations(), 1);
    assert!(
        assembler
            .byte_add_word64_canonical(
                nat(1),
                nat(2),
                bound(nat(1), constant("good")),
                bound(nat(2), constant("good")),
            )
            .err()
            .unwrap()
            .contains("operation budget exceeded")
    );
    assert_eq!(assembler.operations(), 1);
    assembler.operations = usize::MAX;
    assert_eq!(
        assembler
            .byte_add_word64_canonical(
                nat(1),
                nat(2),
                bound(nat(1), constant("good")),
                bound(nat(2), constant("good")),
            )
            .err()
            .unwrap(),
        "operation counter overflow"
    );
    assert_eq!(assembler.operations(), usize::MAX);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 0);
}
