// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Structural controls only: forged evidence stays pending, never a proof.

use super::*;
use clean_kernel::BinderInfo;

fn limits(operations: usize, items: usize) -> Limits {
    Limits {
        max_operations: operations,
        max_locals: 1,
        max_list_items: items,
        max_lookup_candidates: 1,
        lookup_heartbeats: 1,
        lookup_cache_entries: 1,
    }
}

fn fixture(op: &str, carrier: &str, width: u64) -> (FetchedSite, MachineModel, Current) {
    let model = MachineModel {
        world_type: constant("W"),
        context: constant("context"),
        providers: constant("providers"),
    };
    let current = Current {
        frame: constant("frame"),
        tail: constant("tail"),
        legacy_memory: constant("legacy"),
        legacy_cursor: constant("cursor"),
        world: constant("world"),
    };
    let instruction = app(
        "IRInst.overflow",
        [constant(op), app(carrier, [nat(width)]), nat(7), nat(8)],
    );
    let results = list("Nat", &[nat(9), nat(10)]);
    let site = FetchedSite {
        context: model.context.clone(),
        coordinate: Coordinate {
            function: FuncId::new(0),
            block: BlockId::new(1),
            instruction: 2,
        },
        function: constant("function"),
        block: constant("block"),
        node: app("IRNode.mk", [instruction.clone(), results.clone()]),
        instruction,
        results,
        site: constant("site"),
    };
    (site, model, current)
}

fn premises(
    site: &FetchedSite,
    model: &MachineModel,
    current: &Current,
    a: Expr,
    b: Expr,
) -> OverflowPremises {
    let ty =
        exact_constructor_fields::<4>(&site.instruction, "IRInst.overflow").unwrap()[1].clone();
    let candidate = |ty, left, right| {
        PendingEquality::candidate(ty, left, right, constant("untrusted_evidence"))
    };
    let fits = |word| {
        candidate(
            constant("Bool"),
            app("ir_byte_integer_fits_v1", [ty.clone(), word]),
            constant("Bool.true"),
        )
    };
    OverflowPremises {
        left: candidate(
            constant("IRScalar"),
            app("ir_getd", [current.machine(), nat(7)]),
            app("IRScalar.int_", [a.clone()]),
        ),
        right: candidate(
            constant("IRScalar"),
            app("ir_getd", [current.machine(), nat(8)]),
            app("IRScalar.int_", [b.clone()]),
        ),
        left_fits: fits(a),
        right_fits: fits(b),
        result_types: candidate(
            constant("Bool"),
            app(
                "ir_byte_ty_list_eq_v1",
                [
                    app("ir_byte_site_results_v1", [site.site.clone()]),
                    list("IRTy", &[ty, constant("IRTy.bool_")]),
                ],
            ),
            constant("Bool.true"),
        ),
        before: candidate(
            constant("Bool"),
            current.valid(model),
            constant("Bool.true"),
        ),
    }
}

#[test]
fn overflow_candidates_retain_opcode_nominal_carrier_width_and_two_ordered_lanes() {
    for opcode in [
        "IROverflowOp.addoverflow",
        "IROverflowOp.suboverflow",
        "IROverflowOp.muloverflow",
    ] {
        for (carrier, signed, law) in [
            ("IRTy.uint_", "Bool.false", "ir_byte_step_overflow_uint_v1"),
            ("IRTy.int_", "Bool.true", "ir_byte_step_overflow_int_v1"),
        ] {
            for width in [1, 8, 64, 128] {
                let (site, model, current) = fixture(opcode, carrier, width);
                let mut scope = Scope::new();
                let mut assembler = Assembler::new(&mut scope, limits(11, 2)).unwrap();
                let [a, b] = [constant("a"), constant("b")];
                let transfer = site
                    .overflow(
                        &mut assembler,
                        &model,
                        &current,
                        [a.clone(), b.clone()],
                        premises(&site, &model, &current, a.clone(), b.clone()),
                    )
                    .unwrap();
                let expected = [
                    app(
                        "IRScalar.int_",
                        [app(
                            "ir_overflow_value",
                            [constant(opcode), nat(width), a.clone(), b.clone()],
                        )],
                    ),
                    app(
                        "IRScalar.bool_",
                        [app(
                            "ir_overflow_flag",
                            [constant(opcode), constant(signed), nat(width), a, b],
                        )],
                    ),
                ];
                assert_eq!(transfer.values(), &expected);
                let bound = app(
                    "ir_byte_bind_values_v1",
                    [
                        model.world_type.clone(),
                        model.context.clone(),
                        current.machine(),
                        current.world.clone(),
                        site.results.clone(),
                        app("ir_byte_site_results_v1", [site.site.clone()]),
                        list("IRScalar", &expected),
                    ],
                );
                assert_eq!(*transfer.step().left(), model.step(current.running(&model)));
                assert_eq!(*transfer.step().right(), bound);
                assert_eq!(*transfer.run().reached(), bound);
                assert_eq!(*transfer.run().fuel().term(), nat(1));
                assert_eq!(transfer.step().term().get_app_fn(), &constant(law));
                assert_eq!(transfer.step().term().get_app_args().len(), 29);
                assert_eq!(assembler.operations(), 11);
                assert_eq!(assembler.local_scope().allocated(), 0);
            }
        }
    }
}

#[test]
fn overflow_candidates_refuse_foreign_context_and_instruction_shapes_after_charging() {
    for mutation in 0..7 {
        let (mut site, model, current) = fixture("IROverflowOp.addoverflow", "IRTy.uint_", 64);
        let args = premises(&site, &model, &current, nat(1), nat(2));
        match mutation {
            0 => site.context = constant("foreign_context"),
            1 => {
                site.instruction = app(
                    "IRInst.binop",
                    [
                        constant("IRBinOp.add"),
                        app("IRTy.uint_", [nat(64)]),
                        nat(7),
                        nat(8),
                    ],
                )
            }
            2 => {
                site.instruction = app(
                    "IRInst.overflow",
                    [
                        constant("IROverflowOp.addoverflow"),
                        app("IRTy.uint_", [nat(64)]),
                        nat(7),
                    ],
                )
            }
            3 => {
                site.instruction = app(
                    "IRInst.overflow",
                    [
                        constant("IROverflowOp.div"),
                        app("IRTy.uint_", [nat(64)]),
                        nat(7),
                        nat(8),
                    ],
                )
            }
            4 => {
                site.instruction = app(
                    "IRInst.overflow",
                    [
                        app("IROverflowOp.addoverflow", [nat(1)]),
                        app("IRTy.uint_", [nat(64)]),
                        nat(7),
                        nat(8),
                    ],
                )
            }
            5 => {
                site.instruction = app(
                    "IRInst.overflow",
                    [
                        constant("IROverflowOp.addoverflow"),
                        constant("IRTy.usize_"),
                        nat(7),
                        nat(8),
                    ],
                )
            }
            6 => {
                site.instruction = app(
                    "IRInst.overflow",
                    [
                        constant("IROverflowOp.addoverflow"),
                        app("IRTy.int_", [nat(64), nat(1)]),
                        nat(7),
                        nat(8),
                    ],
                )
            }
            _ => unreachable!(),
        }
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(1, 2)).unwrap();
        assert!(
            site.overflow(&mut assembler, &model, &current, [nat(1), nat(2)], args)
                .is_err()
        );
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
}

#[test]
fn overflow_candidates_refuse_mismatched_reads_fits_result_catalog_and_world_premises() {
    for mutation in 0..6 {
        let (site, model, current) = fixture("IROverflowOp.suboverflow", "IRTy.int_", 64);
        let mut args = premises(&site, &model, &current, nat(1), nat(2));
        let fake = PendingEquality::reflexive(constant("Bool"), constant("Bool.true"));
        match mutation {
            0 => args.left = fake,
            1 => args.right = fake,
            2 => args.left_fits = fake,
            3 => args.right_fits = fake,
            4 => args.result_types = fake,
            5 => args.before = fake,
            _ => unreachable!(),
        }
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(1, 2)).unwrap();
        assert!(
            site.overflow(&mut assembler, &model, &current, [nat(1), nat(2)], args)
                .is_err()
        );
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
}

#[test]
fn overflow_failure_cannot_refund_operation_or_two_lane_list_budget() {
    let (site, model, current) = fixture("IROverflowOp.muloverflow", "IRTy.uint_", 64);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
    let first = site
        .overflow(
            &mut assembler,
            &model,
            &current,
            [nat(1), nat(2)],
            premises(&site, &model, &current, nat(1), nat(2)),
        )
        .err()
        .unwrap();
    assert_eq!(first, "execution construction list budget exceeded");
    let second = site
        .overflow(
            &mut assembler,
            &model,
            &current,
            [nat(1), nat(2)],
            premises(&site, &model, &current, nat(1), nat(2)),
        )
        .err()
        .unwrap();
    assert_eq!(second, "execution construction operation budget exceeded");
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.local_scope().allocated(), 0);
}

#[test]
fn normalized_mul_keeps_nominal_width_order_and_checked_binding_world() {
    for carrier in ["IRTy.uint_", "IRTy.int_"] {
        for width in [1, 8, 64, 128] {
            let (site, model, current) = fixture("IROverflowOp.muloverflow", carrier, width);
            let mut scope = Scope::new();
            let mut policy = limits(100, 2);
            policy.max_locals = 10;
            let mut assembler = Assembler::new(&mut scope, policy).unwrap();
            let transfer = site
                .overflow_mul_normalized(
                    &mut assembler,
                    &model,
                    &current,
                    [constant("a"), constant("b")],
                    premises(&site, &model, &current, constant("a"), constant("b")),
                )
                .unwrap();
            assert_eq!(
                transfer.values[0],
                app(
                    "IRScalar.int_",
                    [app(
                        "ir_nat_rem_total_v1",
                        [
                            app("Nat.mul", [constant("a"), constant("b")]),
                            app("ir_nat_pow2", [nat(width)]),
                        ],
                    )]
                )
            );
            // Independently spell the sign branches and unequal comparisons,
            // including the actual emitted beta endpoints.
            let operand = |name| {
                if carrier == "IRTy.int_" {
                    app("ir_signed_magnitude", [nat(width), constant(name)])
                } else {
                    constant(name)
                }
            };
            let product = app("Nat.mul", [operand("a"), operand("b")]);
            let flag_body = if carrier == "IRTy.int_" {
                let limit = app("ir_nat_pow2", [app("Nat.pred", [nat(width)])]);
                Expr::apps(
                    Expr::const_(
                        Name::from_string("Bool.rec"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [
                        Expr::lam(BinderInfo::Default, constant("Bool"), constant("Bool")),
                        app("ir_nat_leb", [limit.clone(), Expr::bvar(0)]),
                        app("ir_nat_ltb", [limit, Expr::bvar(0)]),
                        app(
                            "ir_bool_xor",
                            [
                                app("ir_sign_bit", [nat(width), constant("a")]),
                                app("ir_sign_bit", [nat(width), constant("b")]),
                            ],
                        ),
                    ],
                )
            } else {
                app(
                    "ir_nat_leb",
                    [app("ir_nat_pow2", [nat(width)]), Expr::bvar(0)],
                )
            };
            let flag = Expr::app(
                Expr::lam(BinderInfo::Default, constant("Nat"), flag_body),
                product,
            );
            let flag_scalar = Expr::app(
                Expr::lam(
                    BinderInfo::Default,
                    constant("Bool"),
                    app("IRScalar.bool_", [Expr::bvar(0)]),
                ),
                flag,
            );
            // Congruence deliberately defers abstraction to the shared owner.
            // Compare its actual closed endpoint with the independent oracle,
            // not an open FVar-backed candidate with a de Bruijn endpoint.
            let closed_flag = assembler.local_scope().close(&transfer.values[1]).unwrap();
            assert!(!closed_flag.has_fvar_quick() && !closed_flag.has_loose_bvars());
            assert_eq!(closed_flag, flag_scalar);
            assert!(Scope::new().close(&transfer.values[1]).is_err());
            let expected = app(
                "ir_byte_bind_values_v1",
                [
                    model.world_type.clone(),
                    model.context.clone(),
                    current.machine(),
                    current.world.clone(),
                    site.results.clone(),
                    app("ir_byte_site_results_v1", [site.site.clone()]),
                    list("IRScalar", transfer.values()),
                ],
            );
            assert_eq!(transfer.step.right, expected);
            assert_eq!(*transfer.run().reached(), expected);
            assert_eq!(assembler.local_scope().allocated(), 5);
            assert_eq!(
                assembler.operations(),
                23,
                "construct only the final one-step run"
            );
            // Forged input evidence is retained, not promoted to authority.
            let closed = assembler.local_scope().close(transfer.step.term()).unwrap();
            assert!(!closed.has_fvar_quick() && !closed.has_loose_bvars());
            assert_eq!(
                closed.get_app_fn(),
                &Expr::const_(
                    Name::from_string("Eq.trans"),
                    vec![Level::succ(Level::zero())],
                )
            );
        }
    }
}

#[test]
fn normalized_mul_refuses_other_opcodes_and_does_not_refund_charge() {
    for opcode in ["IROverflowOp.addoverflow", "IROverflowOp.suboverflow"] {
        let (site, model, current) = fixture(opcode, "IRTy.uint_", 64);
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(1, 2)).unwrap();
        let error = site
            .overflow_mul_normalized(
                &mut assembler,
                &model,
                &current,
                [nat(1), nat(2)],
                premises(&site, &model, &current, nat(1), nat(2)),
            )
            .err()
            .unwrap();
        assert_eq!(
            error,
            "normalized overflow transfer requires exact MulOverflow"
        );
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.local_scope().allocated(), 0);
        let second = site
            .overflow_mul_normalized(
                &mut assembler,
                &model,
                &current,
                [nat(1), nat(2)],
                premises(&site, &model, &current, nat(1), nat(2)),
            )
            .err()
            .unwrap();
        assert_eq!(second, "execution construction operation budget exceeded");
    }
}
