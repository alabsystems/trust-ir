// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Shape/work controls only: uninstalled candidate terms carry no proof credit.

use super::*;

fn limits() -> Limits {
    Limits {
        max_operations: 1,
        max_locals: 1,
        max_list_items: 1,
        max_lookup_candidates: 1,
        lookup_heartbeats: 1,
        lookup_cache_entries: 1,
    }
}

fn bound(word: Expr, evidence: &str) -> PendingProof {
    PendingProof::candidate(
        app("Nat.lt", [word, app("ir_nat_pow2", [nat(64)])]),
        constant(evidence),
    )
}

fn derive(
    assembler: &mut Assembler<'_>,
    carrier: UnsignedComparisonCarrier,
    op: ICmpOp,
    a: Expr,
    b: Expr,
    a_bound: PendingProof,
    b_bound: PendingProof,
) -> Result<(Expr, PendingEquality)> {
    match carrier {
        UnsignedComparisonCarrier::Unsigned => {
            assembler.byte_unsigned_compare_u64_canonical(op, a, b, a_bound, b_bound)
        }
        UnsignedComparisonCarrier::Signed => {
            assembler.byte_unsigned_compare_i64_canonical(op, a, b, a_bound, b_bound)
        }
    }
}

#[test]
fn canonical_unsigned_compare_candidates_keep_exact_nominal_opcodes_operands_and_observers() {
    // Independent opcode/observer/argument order and root inventory.
    for (op, opcode, observer, reversed, uint_law, int_law) in [
        (
            ICmpOp::Ult,
            "IRICmpOp.ult",
            "ir_nat_ltb",
            false,
            "ir_byte_icmp_uint_ult_canonical_v1",
            "ir_byte_icmp_int_ult_canonical_v1",
        ),
        (
            ICmpOp::Ule,
            "IRICmpOp.ule",
            "ir_nat_leb",
            false,
            "ir_byte_icmp_uint_ule_canonical_v1",
            "ir_byte_icmp_int_ule_canonical_v1",
        ),
        (
            ICmpOp::Ugt,
            "IRICmpOp.ugt",
            "ir_nat_ltb",
            true,
            "ir_byte_icmp_uint_ugt_canonical_v1",
            "ir_byte_icmp_int_ugt_canonical_v1",
        ),
        (
            ICmpOp::Uge,
            "IRICmpOp.uge",
            "ir_nat_leb",
            true,
            "ir_byte_icmp_uint_uge_canonical_v1",
            "ir_byte_icmp_int_uge_canonical_v1",
        ),
    ] {
        for (carrier, ty, law) in [
            (UnsignedComparisonCarrier::Unsigned, "IRTy.uint_", uint_law),
            (UnsignedComparisonCarrier::Signed, "IRTy.int_", int_law),
        ] {
            for (a, b) in [
                (constant("a"), constant("b")),
                (nat(0), nat(0)),
                (nat(u64::MAX), nat(u64::MAX)),
                (nat(i64::MIN as u64), nat(i64::MAX as u64)),
                (nat(1_u64 << 31), nat(1_u64 << 32)),
            ] {
                let mut scope = Scope::new();
                let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
                let (value, evaluated) = derive(
                    &mut assembler,
                    carrier,
                    op,
                    a.clone(),
                    b.clone(),
                    bound(a.clone(), "a_evidence"),
                    bound(b.clone(), "b_evidence"),
                )
                .unwrap();
                let args = if reversed {
                    [b.clone(), a.clone()]
                } else {
                    [a.clone(), b.clone()]
                };
                let expected = Expr::apps(
                    Expr::const_str("IRScalar.bool_"),
                    [Expr::apps(Expr::const_str(observer), args)],
                );
                assert_eq!(value, expected);
                assert_eq!(evaluated.ty, constant("IRStepResult"));
                assert_eq!(
                    *evaluated.left(),
                    Expr::apps(
                        Expr::const_str("ir_icmp_eval"),
                        [
                            Expr::const_str(opcode),
                            Expr::apps(Expr::const_str(ty), [Expr::nat_lit(64)]),
                            Expr::apps(Expr::const_str("IRScalar.int_"), [a.clone()]),
                            Expr::apps(Expr::const_str("IRScalar.int_"), [b.clone()]),
                        ]
                    )
                );
                assert_eq!(
                    *evaluated.right(),
                    Expr::apps(Expr::const_str("IRStepResult.value"), [expected])
                );
                assert_eq!(
                    *evaluated.term(),
                    Expr::apps(
                        Expr::const_str(law),
                        [
                            Expr::nat_lit(64),
                            a,
                            b,
                            Expr::const_str("a_evidence"),
                            Expr::const_str("b_evidence"),
                        ]
                    )
                );
                assert_eq!(assembler.operations(), 1);
                assert_eq!(assembler.locals, 0);
                assert_eq!(assembler.local_scope().allocated(), 0);
            }
        }
    }
}

#[test]
fn canonical_unsigned_compare_refuses_all_other_opcodes_after_charging_before_shapes() {
    for carrier in [
        UnsignedComparisonCarrier::Unsigned,
        UnsignedComparisonCarrier::Signed,
    ] {
        for op in [
            ICmpOp::Eq,
            ICmpOp::Ne,
            ICmpOp::Slt,
            ICmpOp::Sle,
            ICmpOp::Sgt,
            ICmpOp::Sge,
        ] {
            let mut scope = Scope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let error = derive(
                &mut assembler,
                carrier,
                op,
                nat(8),
                nat(3),
                bound(nat(7), "wrong_lhs"),
                bound(nat(4), "wrong_rhs"),
            )
            .err()
            .expect("unsupported opcode refuses even with malformed input bounds");
            assert_eq!(error, "unsigned comparison requires Ult, Ule, Ugt or Uge");
            assert_eq!(assembler.operations(), 1);
            assert_eq!(assembler.locals, 0);
            assert_eq!(assembler.local_scope().allocated(), 0);
            let error = derive(
                &mut assembler,
                carrier,
                ICmpOp::Uge,
                nat(8),
                nat(3),
                bound(nat(8), "lhs"),
                bound(nat(3), "rhs"),
            )
            .err()
            .expect("failed unsupported opcode spends the operation");
            assert_eq!(error, "execution construction operation budget exceeded");
            assert_eq!(assembler.operations(), 1);
        }
    }
}

#[test]
fn canonical_unsigned_compare_refuses_wrong_word_width_relation_and_foreign_bound_shapes() {
    let a = constant("a");
    let b = constant("b");
    let limit = app("ir_nat_pow2", [nat(64)]);
    let malformed = [
        (a.clone(), bound(b, "wrong_word")),
        (
            a.clone(),
            PendingProof::candidate(
                app("Nat.lt", [a.clone(), app("ir_nat_pow2", [nat(32)])]),
                constant("wrong_width"),
            ),
        ),
        (
            a.clone(),
            PendingProof::candidate(
                app("Nat.lt", [limit.clone(), a.clone()]),
                constant("reversed"),
            ),
        ),
        (
            a.clone(),
            PendingProof::candidate(
                app("Nat.le", [a.clone(), limit.clone()]),
                constant("weak_relation"),
            ),
        ),
        (
            a.clone(),
            PendingProof::candidate(
                eq(
                    &constant("Bool"),
                    app("ir_nat_ltb", [a.clone(), limit]),
                    constant("Bool.true"),
                ),
                constant("bool_fit_is_not_nat_bound"),
            ),
        ),
        (
            app("IRScalar.int_", [a.clone()]),
            bound(a, "foreign_carrier"),
        ),
    ];
    for carrier in [
        UnsignedComparisonCarrier::Unsigned,
        UnsignedComparisonCarrier::Signed,
    ] {
        for op in [ICmpOp::Ult, ICmpOp::Ule, ICmpOp::Ugt, ICmpOp::Uge] {
            for (word, bad_bound) in &malformed {
                for side in ["lhs", "rhs"] {
                    let mut scope = Scope::new();
                    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
                    let (lhs, rhs, lhs_bound, rhs_bound) = if side == "lhs" {
                        (
                            word.clone(),
                            nat(3),
                            bad_bound.clone(),
                            bound(nat(3), "valid"),
                        )
                    } else {
                        (
                            nat(3),
                            word.clone(),
                            bound(nat(3), "valid"),
                            bad_bound.clone(),
                        )
                    };
                    let error = derive(&mut assembler, carrier, op, lhs, rhs, lhs_bound, rhs_bound)
                        .err()
                        .expect("exact canonical input proposition required");
                    assert!(
                        error.contains(&format!("unsigned compare {side} canonical word bound")),
                        "{error}"
                    );
                    assert_eq!(assembler.operations(), 1);
                    assert_eq!(assembler.locals, 0);
                    assert_eq!(assembler.local_scope().allocated(), 0);
                }
            }
        }
    }
}

#[test]
fn canonical_unsigned_compare_shape_failures_do_not_refund_budget_or_allocate_locals() {
    for carrier in [
        UnsignedComparisonCarrier::Unsigned,
        UnsignedComparisonCarrier::Signed,
    ] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        derive(
            &mut assembler,
            carrier,
            ICmpOp::Uge,
            nat(8),
            nat(3),
            bound(nat(8), "valid"),
            bound(nat(4), "invalid"),
        )
        .err()
        .expect("rhs bound mismatch charges first");
        let error = derive(
            &mut assembler,
            carrier,
            ICmpOp::Eq,
            nat(8),
            nat(3),
            bound(nat(8), "valid"),
            bound(nat(3), "valid"),
        )
        .err()
        .expect("budget check precedes unsupported opcode refusal");
        assert_eq!(error, "execution construction operation budget exceeded");
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
}

#[test]
fn canonical_unsigned_compare_matching_forged_carriers_stay_unchecked_pending_data() {
    for carrier in [
        UnsignedComparisonCarrier::Unsigned,
        UnsignedComparisonCarrier::Signed,
    ] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let foreign = app("IRScalar.int_", [nat(8)]);
        let (value, evaluated) = derive(
            &mut assembler,
            carrier,
            ICmpOp::Uge,
            foreign.clone(),
            nat(3),
            bound(foreign.clone(), "uninstalled"),
            bound(nat(3), "uninstalled"),
        )
        .expect("matching metadata is not type checking or certification");
        assert_eq!(
            value,
            app(
                "IRScalar.bool_",
                [app("ir_nat_leb", [nat(3), foreign.clone()])]
            )
        );
        assert_eq!(
            *evaluated.left(),
            app(
                "ir_icmp_eval",
                [
                    constant("IRICmpOp.uge"),
                    app(
                        match carrier {
                            UnsignedComparisonCarrier::Unsigned => "IRTy.uint_",
                            UnsignedComparisonCarrier::Signed => "IRTy.int_",
                        },
                        [nat(64)]
                    ),
                    app("IRScalar.int_", [foreign]),
                    app("IRScalar.int_", [nat(3)]),
                ]
            )
        );
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
}
