// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Structural/work controls. Uninstalled terms are pending data, not facts.

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
    a: Expr,
    b: Expr,
    a_bound: PendingProof,
    b_bound: PendingProof,
    carrier: AddCarrier,
) -> Result<(Expr, PendingEquality, PendingProof)> {
    match carrier {
        AddCarrier::Unsigned => assembler.byte_add_u64_canonical(a, b, a_bound, b_bound),
        AddCarrier::Signed => assembler.byte_add_i64_canonical(a, b, a_bound, b_bound),
    }
}
// Independent result expression, not a call to the producer's helper.
fn expected_word(a: Expr, b: Expr) -> Expr {
    let sum = Expr::apps(Expr::const_str("Nat.add"), [a, b]);
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
            app("Nat.sub", [sum.clone(), limit.clone()]),
            sum.clone(),
            app("ir_nat_ltb", [sum, limit]),
        ],
    )
}

#[test]
fn canonical_add_candidates_preserve_original_opcode_carriers_branches_and_bound_roots() {
    for carrier in [AddCarrier::Unsigned, AddCarrier::Signed] {
        for (a, b) in [
            (constant("a"), constant("b")),
            (nat(0), nat(0)),
            (nat(u64::MAX), nat(1)),
            (nat(u64::MAX), nat(u64::MAX)),
        ] {
            let mut scope = Scope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let (value, evaluated, output_bound) = derive(
                &mut assembler,
                a.clone(),
                b.clone(),
                bound(a.clone(), "a_evidence"),
                bound(b.clone(), "b_evidence"),
                carrier,
            )
            .unwrap();
            let (ty, law, bound_law) = match carrier {
                AddCarrier::Unsigned => (
                    "IRTy.uint_",
                    "ir_byte_add_uint_canonical_v1",
                    "ir_byte_add_uint_canonical_result_bound_v1",
                ),
                AddCarrier::Signed => (
                    "IRTy.int_",
                    "ir_byte_add_int_canonical_v1",
                    "ir_byte_add_int_canonical_result_bound_v1",
                ),
            };
            let word = expected_word(a.clone(), b.clone());
            let limit = app("ir_nat_pow2", [nat(64)]);
            let arguments = [
                nat(64),
                a.clone(),
                b.clone(),
                app(
                    "ir_byte_ltb_of_lt_v1",
                    [a.clone(), limit.clone(), constant("a_evidence")],
                ),
                app(
                    "ir_byte_ltb_of_lt_v1",
                    [b.clone(), limit.clone(), constant("b_evidence")],
                ),
            ];
            assert_eq!(value, app("IRScalar.int_", [word.clone()]));
            assert_eq!(evaluated.ty, constant("IRStepResult"));
            assert_eq!(
                *evaluated.left(),
                app(
                    "ir_binop_eval",
                    [
                        constant("IRBinOp.add"),
                        app(ty, [nat(64)]),
                        app("IRScalar.int_", [a]),
                        app("IRScalar.int_", [b])
                    ]
                )
            );
            assert_eq!(*evaluated.right(), app("IRStepResult.value", [value]));
            assert_eq!(*evaluated.term(), app(law, arguments.clone()));
            assert_eq!(
                *output_bound.proposition(),
                app("Nat.lt", [word.clone(), limit.clone()])
            );
            assert_eq!(
                *output_bound.term(),
                app(
                    "ir_byte_separation_lt_of_ltb_v1",
                    [word, limit, app(bound_law, arguments)]
                )
            );
            assert_eq!(assembler.operations(), 1);
            assert_eq!(assembler.locals, 0);
            assert_eq!(assembler.local_scope().allocated(), 0);
        }
    }
}

#[test]
fn canonical_add_candidates_refuse_wrong_operands_widths_relations_and_carriers() {
    let a = constant("a");
    let b = constant("b");
    let limit = app("ir_nat_pow2", [nat(64)]);
    let malformed = [
        (a.clone(), bound(b.clone(), "bad")),
        (
            a.clone(),
            PendingProof::candidate(
                app("Nat.lt", [a.clone(), app("ir_nat_pow2", [nat(32)])]),
                constant("bad"),
            ),
        ),
        (
            a.clone(),
            PendingProof::candidate(app("Nat.lt", [limit.clone(), a.clone()]), constant("bad")),
        ),
        (
            a.clone(),
            PendingProof::candidate(app("Nat.le", [a.clone(), limit.clone()]), constant("bad")),
        ),
        (
            a.clone(),
            PendingProof::candidate(
                eq(
                    &constant("Bool"),
                    app("ir_nat_ltb", [a.clone(), limit]),
                    constant("Bool.true"),
                ),
                constant("bad"),
            ),
        ),
        (app("IRScalar.int_", [a.clone()]), bound(a.clone(), "bad")),
    ];
    for carrier in [AddCarrier::Unsigned, AddCarrier::Signed] {
        for (word, bad_bound) in &malformed {
            for side in ["lhs", "rhs"] {
                let mut scope = Scope::new();
                let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
                let error = if side == "lhs" {
                    derive(
                        &mut assembler,
                        word.clone(),
                        b.clone(),
                        bad_bound.clone(),
                        bound(b.clone(), "good"),
                        carrier,
                    )
                } else {
                    derive(
                        &mut assembler,
                        b.clone(),
                        word.clone(),
                        bound(b.clone(), "good"),
                        bad_bound.clone(),
                        carrier,
                    )
                }
                .err()
                .expect("malformed exact input bound refuses");
                assert!(
                    error.contains(&format!("add {side} canonical word bound")),
                    "{error}"
                );
                assert_eq!(assembler.operations(), 1);
                assert_eq!(assembler.locals, 0);
                assert_eq!(assembler.local_scope().allocated(), 0);
            }
        }
    }
}

#[test]
fn canonical_add_candidates_keep_failure_budget_consumed_and_allocate_no_locals() {
    for carrier in [AddCarrier::Unsigned, AddCarrier::Signed] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        derive(
            &mut assembler,
            nat(8),
            nat(3),
            bound(nat(8), "good"),
            bound(nat(4), "bad"),
            carrier,
        )
        .err()
        .expect("rhs mismatch charges first");
        let error = derive(
            &mut assembler,
            nat(8),
            nat(3),
            bound(nat(8), "good"),
            bound(nat(3), "good"),
            carrier,
        )
        .err()
        .expect("failed attempt cannot reset the one-operation limit");
        assert_eq!(error, "execution construction operation budget exceeded");
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
}

#[test]
fn canonical_add_matching_forged_carriers_are_still_pending_until_strict_replay() {
    for carrier in [AddCarrier::Unsigned, AddCarrier::Signed] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let foreign = app("IRScalar.int_", [nat(8)]);
        let (value, evaluated, bound_proof) = derive(
            &mut assembler,
            foreign.clone(),
            nat(3),
            bound(foreign.clone(), "uninstalled"),
            bound(nat(3), "uninstalled"),
            carrier,
        )
        .expect("shape matching is not type inference or certification");
        assert_eq!(
            value,
            app("IRScalar.int_", [expected_word(foreign.clone(), nat(3))])
        );
        assert_eq!(
            *evaluated.left(),
            app(
                "ir_binop_eval",
                [
                    constant("IRBinOp.add"),
                    app(
                        match carrier {
                            AddCarrier::Unsigned => "IRTy.uint_",
                            AddCarrier::Signed => "IRTy.int_",
                        },
                        [nat(64)]
                    ),
                    app("IRScalar.int_", [foreign.clone()]),
                    app("IRScalar.int_", [nat(3)])
                ]
            )
        );
        assert_eq!(
            *bound_proof.proposition(),
            app(
                "Nat.lt",
                [
                    expected_word(foreign, nat(3)),
                    app("ir_nat_pow2", [nat(64)])
                ]
            )
        );
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
}
