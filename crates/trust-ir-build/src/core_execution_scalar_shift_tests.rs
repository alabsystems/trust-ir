// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural controls only. Uninstalled symbols below are candidate data,
//! never checked facts. Ordinary opt-in kernel/whole-world replay is separate.

use super::*;

fn limits() -> Limits {
    Limits {
        max_operations: 8,
        max_locals: 1,
        max_list_items: 1,
        max_lookup_candidates: 1,
        lookup_heartbeats: 1,
        lookup_cache_entries: 1,
    }
}

fn bound(word: Expr) -> PendingProof {
    PendingProof::candidate(
        app("Nat.lt", [word, app("ir_nat_pow2", [nat(64)])]),
        constant("uninstalled_canonical_evidence"),
    )
}

fn derive(
    assembler: &mut Assembler<'_>,
    word: Expr,
    bounded: PendingProof,
    arithmetic: bool,
) -> Result<(Expr, PendingEquality)> {
    if arithmetic {
        assembler.byte_ashr_i64_by_three(word, bounded)
    } else {
        assembler.byte_lshr_u64_by_three(word, bounded)
    }
}

// Reconstruct the expected endpoints independently of the production helper.
fn expected_quotient(word: Expr) -> Expr {
    Expr::apps(
        Expr::const_str("ir_dm_quot"),
        [Expr::apps(
            Expr::const_str("ir_dm_go"),
            [
                Expr::nat_lit(1),
                word.clone(),
                Expr::nat_lit(64),
                Expr::nat_lit(8),
                Expr::apps(Expr::const_str("IRDivMod.mk"), [word, Expr::nat_lit(0)]),
            ],
        )],
    )
}

#[test]
fn scalar_shift_candidates_derive_exact_original_operations_and_both_sign_arms() {
    for arithmetic in [false, true] {
        for word in [constant("uninstalled_word"), nat(0), nat(u64::MAX)] {
            let mut scope = Scope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let (value, proof) = derive(
                &mut assembler,
                word.clone(),
                bound(word.clone()),
                arithmetic,
            )
            .expect("construct a pending canonical-word operation");
            let logical = expected_quotient(word.clone());
            let result = if arithmetic {
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
                        logical.clone(),
                        app(
                            "Nat.add",
                            [
                                logical,
                                app(
                                    "Nat.sub",
                                    [
                                        app("ir_nat_pow2", [nat(64)]),
                                        expected_quotient(app("ir_nat_pow2", [nat(64)])),
                                    ],
                                ),
                            ],
                        ),
                        app("ir_sign_bit", [nat(64), word.clone()]),
                    ],
                )
            } else {
                logical
            };
            assert_eq!(value, app("IRScalar.int_", [result]));
            let (opcode, ty, law) = if arithmetic {
                ("IRBinOp.ashr", "IRTy.int_", "ir_byte_ashr_i64_by_three_v1")
            } else {
                ("IRBinOp.lshr", "IRTy.uint_", "ir_byte_lshr_u64_by_three_v1")
            };
            assert_eq!(proof.ty, constant("IRStepResult"));
            assert_eq!(
                *proof.left(),
                app(
                    "ir_binop_eval",
                    [
                        constant(opcode),
                        app(ty, [nat(64)]),
                        app("IRScalar.int_", [word.clone()]),
                        app("IRScalar.int_", [nat(3)])
                    ],
                )
            );
            assert_eq!(*proof.right(), app("IRStepResult.value", [value]));
            assert_eq!(
                *proof.term(),
                app(
                    law,
                    [
                        word.clone(),
                        app(
                            "ir_byte_ltb_of_lt_v1",
                            [
                                word,
                                app("ir_nat_pow2", [nat(64)]),
                                constant("uninstalled_canonical_evidence")
                            ]
                        )
                    ]
                )
            );
            assert_eq!(assembler.operations(), 1);
            assert_eq!(assembler.locals, 0);
            assert_eq!(assembler.local_scope().allocated(), 0);
        }
    }
}

#[test]
fn scalar_shift_candidates_reject_other_words_widths_reversed_bounds_and_carriers() {
    let word = constant("uninstalled_word");
    let limit = app("ir_nat_pow2", [nat(64)]);
    let malformed = [
        ("wrong word", word.clone(), bound(constant("other_word"))),
        (
            "wrong width",
            word.clone(),
            PendingProof::candidate(
                app("Nat.lt", [word.clone(), app("ir_nat_pow2", [nat(32)])]),
                constant("uninstalled_evidence"),
            ),
        ),
        (
            "reversed bound",
            word.clone(),
            PendingProof::candidate(
                app("Nat.lt", [limit.clone(), word.clone()]),
                constant("uninstalled_evidence"),
            ),
        ),
        (
            "nonstrict bound",
            word.clone(),
            PendingProof::candidate(
                app("Nat.le", [word.clone(), limit.clone()]),
                constant("uninstalled_evidence"),
            ),
        ),
        (
            "Boolean guard",
            word.clone(),
            PendingProof::candidate(
                eq(
                    &constant("Bool"),
                    app("ir_nat_ltb", [word.clone(), limit]),
                    constant("Bool.true"),
                ),
                constant("uninstalled_evidence"),
            ),
        ),
        (
            "foreign scalar carrier",
            app("IRScalar.int_", [word.clone()]),
            bound(word),
        ),
    ];
    for arithmetic in [false, true] {
        for (label, supplied_word, supplied_bound) in &malformed {
            let mut scope = Scope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let error = derive(
                &mut assembler,
                supplied_word.clone(),
                supplied_bound.clone(),
                arithmetic,
            )
            .err()
            .expect(label);
            assert!(
                error.contains("shift canonical word bound"),
                "{label}: {error}"
            );
            assert_eq!(assembler.operations(), 1, "charge before checking: {label}");
            assert_eq!(assembler.locals, 0);
            assert_eq!(assembler.local_scope().allocated(), 0);
        }
    }
}

#[test]
fn scalar_shift_candidates_keep_consumed_budget_and_allocate_no_locals() {
    for arithmetic in [false, true] {
        let mut scope = Scope::new();
        let mut policy = limits();
        policy.max_operations = 1;
        let mut assembler = Assembler::new(&mut scope, policy).unwrap();
        derive(&mut assembler, nat(7), bound(nat(8)), arithmetic)
            .err()
            .expect("wrong bound must refuse after charging");
        let error = derive(&mut assembler, nat(7), bound(nat(7)), arithmetic)
            .err()
            .expect("failed construction must not reset its charge");
        assert_eq!(error, "execution construction operation budget exceeded");
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.local_scope().allocated(), 0);

        let mut scope = Scope::new();
        let mut policy = limits();
        policy.max_operations = 1;
        let mut assembler = Assembler::new(&mut scope, policy).unwrap();
        let (_, proof) = derive(&mut assembler, nat(7), bound(nat(7)), arithmetic)
            .expect("one operation fits the unchanged budget");
        assert_eq!(proof.ty, constant("IRStepResult"));
        let error = derive(&mut assembler, nat(7), bound(nat(7)), arithmetic)
            .err()
            .expect("second operation must be refused");
        assert_eq!(error, "execution construction operation budget exceeded");
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
}
