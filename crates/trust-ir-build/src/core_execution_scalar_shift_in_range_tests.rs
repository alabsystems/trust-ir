// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Shape/work controls only: uninstalled proof terms remain untrusted data.

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

fn bound(word: Expr) -> PendingProof {
    PendingProof::candidate(
        app("Nat.lt", [word, app("ir_nat_pow2", [nat(64)])]),
        constant("uninstalled_word_evidence"),
    )
}

fn range(amount: Expr) -> PendingProof {
    PendingProof::candidate(
        app("Nat.lt", [amount, nat(64)]),
        constant("uninstalled_range_evidence"),
    )
}

fn derive(
    assembler: &mut Assembler<'_>,
    word: Expr,
    amount: Expr,
    bounded: PendingProof,
    in_range: PendingProof,
    arithmetic: bool,
) -> Result<(Expr, PendingEquality, PendingProof)> {
    if arithmetic {
        assembler.byte_ashr_i64_in_range(word, amount, bounded, in_range)
    } else {
        assembler.byte_lshr_u64_in_range(word, amount, bounded, in_range)
    }
}

// Independent endpoint reconstruction: no production quotient/result helper.
fn expected_result(word: Expr, amount: Expr, arithmetic: bool) -> Expr {
    let q = |word: Expr, fuel| {
        Expr::apps(
            Expr::const_str("ir_dm_quot"),
            [Expr::apps(
                Expr::const_str("ir_dm_go"),
                [
                    Expr::nat_lit(1),
                    word.clone(),
                    Expr::nat_lit(fuel),
                    Expr::apps(Expr::const_str("ir_nat_pow2"), [amount.clone()]),
                    Expr::apps(Expr::const_str("IRDivMod.mk"), [word, Expr::nat_lit(0)]),
                ],
            )],
        )
    };
    let logical = q(word.clone(), 64);
    if !arithmetic {
        return logical;
    }
    let limit = Expr::apps(Expr::const_str("ir_nat_pow2"), [Expr::nat_lit(64)]);
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
                [logical, app("Nat.sub", [limit.clone(), q(limit, 65)])],
            ),
            app("ir_sign_bit", [nat(64), word]),
        ],
    )
}

#[test]
fn in_range_shift_candidates_retain_exact_operations_fuels_and_derived_bounds() {
    for arithmetic in [false, true] {
        for word in [constant("symbolic_word"), nat(0), nat(u64::MAX)] {
            for amount in [
                constant("symbolic_amount"),
                nat(0),
                nat(1),
                nat(3),
                nat(31),
                nat(63),
            ] {
                let mut scope = Scope::new();
                let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
                let (value, evaluation, output) = derive(
                    &mut assembler,
                    word.clone(),
                    amount.clone(),
                    bound(word.clone()),
                    range(amount.clone()),
                    arithmetic,
                )
                .unwrap();
                let expected = expected_result(word.clone(), amount.clone(), arithmetic);
                let (opcode, ty, law, result_law) = if arithmetic {
                    (
                        "IRBinOp.ashr",
                        "IRTy.int_",
                        "ir_byte_ashr_i64_in_range_v1",
                        "ir_byte_ashr_i64_in_range_result_bound_v1",
                    )
                } else {
                    (
                        "IRBinOp.lshr",
                        "IRTy.uint_",
                        "ir_byte_lshr_u64_in_range_v1",
                        "ir_byte_lshr_u64_in_range_result_bound_v1",
                    )
                };
                let limit = app("ir_nat_pow2", [nat(64)]);
                let arguments = [
                    word.clone(),
                    amount.clone(),
                    app(
                        "ir_byte_ltb_of_lt_v1",
                        [
                            word.clone(),
                            limit.clone(),
                            constant("uninstalled_word_evidence"),
                        ],
                    ),
                    constant("uninstalled_range_evidence"),
                ];
                assert_eq!(value, app("IRScalar.int_", [expected.clone()]));
                assert_eq!(evaluation.ty, constant("IRStepResult"));
                assert_eq!(
                    *evaluation.left(),
                    app(
                        "ir_binop_eval",
                        [
                            constant(opcode),
                            app(ty, [nat(64)]),
                            app("IRScalar.int_", [word.clone()]),
                            app("IRScalar.int_", [amount]),
                        ]
                    )
                );
                assert_eq!(*evaluation.right(), app("IRStepResult.value", [value]));
                assert_eq!(*evaluation.term(), app(law, arguments.clone()));
                assert_eq!(
                    *output.proposition(),
                    app("Nat.lt", [expected.clone(), limit.clone()])
                );
                assert_eq!(
                    *output.term(),
                    app(
                        "ir_byte_separation_lt_of_ltb_v1",
                        [expected, limit, app(result_law, arguments),]
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
fn in_range_shift_candidates_refuse_wrong_words_widths_ranges_and_carriers() {
    let word = constant("symbolic_word");
    let amount = constant("symbolic_amount");
    let cases = [
        (
            word.clone(),
            amount.clone(),
            bound(nat(9)),
            range(amount.clone()),
            "shift canonical word bound",
        ),
        (
            word.clone(),
            amount.clone(),
            PendingProof::candidate(
                app("Nat.lt", [word.clone(), app("ir_nat_pow2", [nat(32)])]),
                constant("bad"),
            ),
            range(amount.clone()),
            "shift canonical word bound",
        ),
        (
            word.clone(),
            amount.clone(),
            PendingProof::candidate(
                app("Nat.lt", [app("ir_nat_pow2", [nat(64)]), word.clone()]),
                constant("bad"),
            ),
            range(amount.clone()),
            "shift canonical word bound",
        ),
        (
            app("IRScalar.int_", [word.clone()]),
            amount.clone(),
            bound(word.clone()),
            range(amount.clone()),
            "shift canonical word bound",
        ),
        (
            word.clone(),
            amount.clone(),
            bound(word.clone()),
            range(nat(3)),
            "shift amount range",
        ),
        (
            word.clone(),
            amount.clone(),
            bound(word.clone()),
            PendingProof::candidate(app("Nat.lt", [amount.clone(), nat(65)]), constant("bad")),
            "shift amount range",
        ),
        (
            word.clone(),
            amount.clone(),
            bound(word.clone()),
            PendingProof::candidate(app("Nat.lt", [nat(64), amount.clone()]), constant("bad")),
            "shift amount range",
        ),
        (
            word.clone(),
            amount.clone(),
            bound(word.clone()),
            PendingProof::candidate(app("Nat.le", [amount.clone(), nat(64)]), constant("bad")),
            "shift amount range",
        ),
        (
            word.clone(),
            app("IRScalar.int_", [amount.clone()]),
            bound(word.clone()),
            range(amount.clone()),
            "shift amount range",
        ),
    ];
    for arithmetic in [false, true] {
        for (word, amount, bound, range, diagnostic) in &cases {
            let mut scope = Scope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let error = derive(
                &mut assembler,
                word.clone(),
                amount.clone(),
                bound.clone(),
                range.clone(),
                arithmetic,
            )
            .err()
            .unwrap();
            assert!(error.contains(diagnostic), "{error}");
            assert_eq!(assembler.operations(), 1);
            assert_eq!(assembler.locals, 0);
            assert_eq!(assembler.local_scope().allocated(), 0);
        }
    }
}

#[test]
fn in_range_shift_candidates_charge_failed_attempts_without_new_locals() {
    for arithmetic in [false, true] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        derive(
            &mut assembler,
            nat(8),
            nat(3),
            bound(nat(8)),
            range(nat(4)),
            arithmetic,
        )
        .err()
        .expect("wrong range consumes the one operation");
        let error = derive(
            &mut assembler,
            nat(8),
            nat(3),
            bound(nat(8)),
            range(nat(3)),
            arithmetic,
        )
        .err()
        .expect("failed attempt cannot reset its charge");
        assert_eq!(error, "execution construction operation budget exceeded");
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
}

#[test]
fn in_range_shift_candidates_do_not_certify_forged_matching_evidence() {
    // Even a false but structurally matching range is still just candidate
    // data here. The independent strict replay test rejects its proof term.
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let (_, evaluation, output) = assembler
        .byte_ashr_i64_in_range(nat(8), nat(64), bound(nat(8)), range(nat(64)))
        .expect("shape checks are not a type checker or mathematical oracle");
    let arguments = [
        nat(8),
        nat(64),
        app(
            "ir_byte_ltb_of_lt_v1",
            [
                nat(8),
                app("ir_nat_pow2", [nat(64)]),
                constant("uninstalled_word_evidence"),
            ],
        ),
        constant("uninstalled_range_evidence"),
    ];
    assert_eq!(
        *evaluation.term(),
        app("ir_byte_ashr_i64_in_range_v1", arguments.clone())
    );
    assert_eq!(
        *output.term(),
        app(
            "ir_byte_separation_lt_of_ltb_v1",
            [
                expected_result(nat(8), nat(64), true),
                app("ir_nat_pow2", [nat(64)]),
                app("ir_byte_ashr_i64_in_range_result_bound_v1", arguments),
            ]
        )
    );
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.local_scope().allocated(), 0);
}
