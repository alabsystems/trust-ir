// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural candidate/closure regressions, not byte-kernel execution tests.
//! No substitute evaluator or private byte vocabulary is installed here. The
//! actual consuming environment must replay these candidates and their facts.

use super::*;

fn limits() -> Limits {
    Limits {
        max_operations: 10_000,
        max_locals: 1_000,
        max_list_items: 1_000,
        max_lookup_candidates: 100,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 16_384,
    }
}

struct Fixture {
    model: MachineModel,
    site: FetchedSite,
    current: Current,
    result: MemoryResult,
    premises: MemoryPremises,
    parameters: Vec<Local>,
}

fn instruction(kind: usize) -> Expr {
    let ty = if kind == 1 || kind == 3 {
        app("IRTy.func_", [nat(53)])
    } else {
        constant("IRTy.ptr_")
    };
    match kind {
        0 | 1 => app("IRInst.load", [ty, nat(11), constant("Bool.false")]),
        2 | 3 => app(
            "IRInst.store",
            [ty, nat(11), nat(19), constant("Bool.false")],
        ),
        4 | 5 => app(
            "IRInst.gep",
            [
                app("IRTy.int_", [nat(8)]),
                nat(11),
                list("Nat", &[nat(19), nat(37)]),
                constant(if kind == 4 { "Bool.true" } else { "Bool.false" }),
            ],
        ),
        6 => app(
            "IRInst.atomic_fetch_add_relaxed_u64_seq",
            [nat(11), nat(19)],
        ),
        _ => panic!("test kind"),
    }
}

fn fixture(scope: &mut Scope, kind: usize) -> Fixture {
    let store = kind == 2 || kind == 3;
    let mut parameters = Vec::new();
    let mut local = |ty| {
        let value = scope.try_local(ty).unwrap();
        parameters.push(value.clone());
        value.term().clone()
    };
    let model = MachineModel::from_terms(
        constant("Nat"),
        constant("actual_test_context"),
        local(app("IRByteProvidersV1", [constant("Nat")])),
    );
    let current = Current {
        frame: app(
            "IRFrame.mk",
            [
                nat(41),
                nat(13),
                nat(9),
                local(app("IRList", [constant("IRBinding")])),
                list("Nat", &[nat(91), nat(7)]),
            ],
        ),
        tail: local(app("IRList", [constant("IRFrame")])),
        legacy_memory: local(app("IRList", [constant("IRMemSlot")])),
        legacy_cursor: local(constant("Nat")),
        // Opaque, not a mk term; this exercises the shared world recursor path.
        world: local(app("IRByteWorldV1", [constant("Nat")])),
    };
    let instruction = instruction(kind);
    let results = if store {
        list("Nat", &[])
    } else {
        list("Nat", &[nat(61)])
    };
    let lane = if kind == 1 {
        app("IRTy.func_", [nat(53)])
    } else if kind == 6 {
        app("IRTy.uint_", [nat(64)])
    } else {
        constant("IRTy.ptr_")
    };
    let site = FetchedSite {
        context: model.context().clone(),
        coordinate: Coordinate {
            function: FuncId::new(41),
            block: BlockId::new(13),
            instruction: 9,
        },
        function: constant("actual_test_function"),
        block: constant("actual_test_block"),
        node: app("IRNode.mk", [instruction.clone(), results.clone()]),
        instruction,
        results,
        site: app(
            "IRByteSiteV1.mk",
            [
                nat(41),
                nat(13),
                nat(9),
                nat(8),
                nat(1),
                if store {
                    list("IRTy", &[])
                } else {
                    list("IRTy", &[lane])
                },
            ],
        ),
    };
    let old_memory = projection(&model, &current.world, "memory");
    let result = MemoryResult {
        value: if store {
            constant("IRScalar.unit_")
        } else if kind == 1 {
            app("IRScalar.fnptr_", [nat(67)])
        } else {
            local(constant("IRScalar"))
        },
        memory: if store || kind == 6 {
            app(
                "IRByteMemoryV1.mk",
                [
                    allocations(old_memory.clone()),
                    // Returned bytes are deliberately distinct from the old map.
                    local(Expr::arrow(
                        constant("Nat"),
                        app("IROption", [constant("Nat")]),
                    )),
                    app("ir_byte_mem_next_v1", [old_memory.clone()]),
                ],
            )
        } else {
            old_memory.clone()
        },
    };
    let checks = site.memory_checks(&model, &current, &result).unwrap();
    let mut fact = |ty: Expr, left: Expr, right: Expr| {
        let proof = local(eq(&ty, left.clone(), right.clone()));
        PendingEquality::candidate(ty, left, right, proof)
    };
    let premises = MemoryPremises {
        evaluated: fact(
            constant("IRByteMemoryResultV1"),
            checks.evaluation,
            result.result(),
        ),
        result: fact(constant("Bool"), checks.result, constant("Bool.true")),
        allocations: fact(
            app("IRList", [constant("IRByteAllocationV1")]),
            allocations(result.memory.clone()),
            allocations(old_memory),
        ),
        before: fact(
            constant("Bool"),
            current.valid(&model),
            constant("Bool.true"),
        ),
    };
    Fixture {
        model,
        site,
        current,
        result,
        premises,
        parameters,
    }
}

fn transfer(scope: &mut Scope, f: &Fixture) -> Result<MemoryTransfer> {
    f.site.memory_value(
        &mut Assembler::new(scope, limits())?,
        &f.model,
        &f.current,
        f.result.clone(),
        f.premises.clone(),
    )
}

#[test]
fn memory_checks_retain_actual_ssa_type_alignment_volatility_and_inbounds() {
    for kind in 0..7 {
        let mut scope = Scope::new();
        let f = fixture(&mut scope, kind);
        let checks = f
            .site
            .memory_checks(&f.model, &f.current, &f.result)
            .unwrap();
        let read = |id| app("ir_getd", [f.current.machine(), nat(id)]);
        let memory = projection(&f.model, &f.current.world, "memory");
        let align = app("ir_byte_site_align_v1", [f.site.site.clone()]);
        let ty = if kind == 1 || kind == 3 {
            app("IRTy.func_", [nat(53)])
        } else {
            constant("IRTy.ptr_")
        };
        let expected = match kind {
            0 | 1 => app(
                "ir_byte_load_v1",
                [
                    f.model.context().clone(),
                    ty,
                    read(11),
                    align,
                    constant("Bool.false"),
                    memory,
                ],
            ),
            2 | 3 => app(
                "ir_byte_store_v1",
                [
                    f.model.context().clone(),
                    ty,
                    read(11),
                    read(19),
                    align,
                    constant("Bool.false"),
                    memory,
                ],
            ),
            4 | 5 => app(
                "ir_byte_gep_v1",
                [
                    f.model.context().clone(),
                    app("IRTy.int_", [nat(8)]),
                    read(11),
                    app(
                        "ir_resolve",
                        [f.current.machine(), list("Nat", &[nat(19), nat(37)])],
                    ),
                    constant(if kind == 4 { "Bool.true" } else { "Bool.false" }),
                    memory,
                ],
            ),
            _ => app(
                "ir_byte_fetch_add_relaxed_u64_seq_v1",
                [f.model.context().clone(), read(11), read(19), memory],
            ),
        };
        assert_eq!(checks.evaluation, expected);
        assert_eq!(checks.allocations, f.premises.allocations.proposition());
        let values = if kind == 2 || kind == 3 {
            list("IRScalar", &[])
        } else {
            list("IRScalar", std::slice::from_ref(&f.result.value))
        };
        assert_eq!(
            checks.result,
            app(
                "Bool.and",
                [
                    app(
                        "ir_nat_eqb",
                        [
                            app(
                                "ir_byte_length_v1",
                                [constant("Nat"), f.site.results.clone()]
                            ),
                            app("ir_byte_length_v1", [constant("IRScalar"), values.clone()])
                        ]
                    ),
                    app(
                        "ir_byte_values_match_v1",
                        [
                            f.model.context().clone(),
                            app("ir_byte_site_results_v1", [f.site.site.clone()]),
                            values
                        ]
                    ),
                ]
            )
        );
    }
    // Metadata is not silently sanitized; any claimed volatile success must
    // still be derived against the actual evaluator by the consuming proof.
    let mut scope = Scope::new();
    let mut f = fixture(&mut scope, 0);
    f.site.instruction = app(
        "IRInst.load",
        [constant("IRTy.ptr_"), nat(11), constant("Bool.true")],
    );
    let checks = f
        .site
        .memory_checks(&f.model, &f.current, &f.result)
        .unwrap();
    assert_eq!(*checks.evaluation.get_app_args()[4], constant("Bool.true"));
}

#[test]
fn memory_transfer_retains_returned_bytes_and_binds_and_advances_exactly_once() {
    for kind in 0..7 {
        let mut scope = Scope::new();
        let f = fixture(&mut scope, kind);
        let got = transfer(&mut scope, &f).unwrap();
        let values = if kind == 2 || kind == 3 {
            list("IRScalar", &[])
        } else {
            list("IRScalar", std::slice::from_ref(&f.result.value))
        };
        let expected_frame = app(
            "ir_frame_advance",
            [app(
                "ir_frame_set_many",
                [f.current.frame.clone(), f.site.results.clone(), values],
            )],
        );
        let expected_world = app(
            "IRByteWorldV1.mk",
            [
                f.model.world_type().clone(),
                f.result.memory.clone(),
                projection(&f.model, &f.current.world, "host"),
                projection(&f.model, &f.current.world, "owners"),
                projection(&f.model, &f.current.world, "next"),
            ],
        );
        assert_eq!(got.current().frame, expected_frame);
        assert_eq!(got.current().world, expected_world);
        assert_eq!(got.current().tail, f.current.tail);
        assert_eq!(got.current().legacy_memory, f.current.legacy_memory);
        assert_eq!(got.current().legacy_cursor, f.current.legacy_cursor);
        assert_eq!(got.memory(), &f.result.memory);
        assert_eq!(got.result().result(), f.result.result());
        if kind == 2 || kind == 3 || kind == 6 {
            assert_ne!(
                got.memory(),
                &projection(&f.model, &f.current.world, "memory")
            );
        }
        assert_eq!(got.step().left, f.model.step(f.current.running(&f.model)));
        assert_eq!(got.step().right, got.current().running(&f.model));
        assert_eq!(got.run().initial(), &f.current.running(&f.model));
        assert_eq!(got.run().reached(), &got.current().running(&f.model));
        assert_eq!(got.run().fuel().term(), &nat(1));
        assert_eq!(got.valid().left, got.current().valid(&f.model));
        assert_eq!(got.valid().right, constant("Bool.true"));
        assert_eq!(
            got.valid().term.get_app_fn(),
            &constant("ir_byte_import_world_shape_v1")
        );
        let fields = got.valid().term.get_app_args();
        assert_eq!(fields.len(), 11);
        assert_eq!(*fields[7], f.result.memory);
        assert_eq!(*fields[8], projection(&f.model, &f.current.world, "host"));
        assert_ne!(got.valid().term, f.premises.before.term);
        for term in [
            got.step().term.clone(),
            got.run().equality().term.clone(),
            got.valid().term.clone(),
        ] {
            let closed = f
                .parameters
                .iter()
                .rev()
                .fold(term, |body, local| local.lam(body));
            assert!(!scope.close(&closed).unwrap().has_fvar_quick());
        }
    }
}

#[test]
fn sequential_atomic_transfer_refuses_operand_arity_result_and_world_substitution() {
    for mutation in 0..8 {
        let mut scope = Scope::new();
        let mut f = fixture(&mut scope, 6);
        match mutation {
            0 => f.site.instruction = app("IRInst.atomic_fetch_add_relaxed_u64_seq", [nat(11)]),
            1 => {
                f.site.instruction = app(
                    "IRInst.atomic_fetch_add_relaxed_u64_seq",
                    [nat(11), nat(19), nat(8)],
                )
            }
            2 => {
                f.site.instruction = app(
                    "IRInst.atomic_fetch_add_relaxed_u64_seq",
                    [nat(12), nat(19)],
                )
            }
            3 => {
                f.site.instruction = app(
                    "IRInst.atomic_fetch_add_relaxed_u64_seq",
                    [nat(11), nat(20)],
                )
            }
            4 => f.site.results = list("Nat", &[]),
            5 => f.result.value = constant("wrong_old_value"),
            6 => f.result.memory = projection(&f.model, &f.current.world, "memory"),
            _ => f.current.world = constant("another_world"),
        }
        assert!(transfer(&mut scope, &f).is_err(), "mutation {mutation}");
    }
}

#[test]
fn memory_transfer_refuses_wrong_evaluator_shape_result_and_framing_endpoints() {
    for mutation in 0..17 {
        let mut scope = Scope::new();
        let mut f = fixture(&mut scope, 3);
        match mutation {
            0 => f.site.instruction = app("IRInst.ret", [list("Nat", &[])]),
            1 => {
                f.site.instruction = app(
                    "IRInst.alloca",
                    [
                        constant("IRTy.ptr_"),
                        app("IROption.none", [constant("Nat")]),
                    ],
                )
            }
            2 => f.site.instruction = app("IRInst.load", [constant("IRTy.ptr_")]),
            3 => f.site.context = constant("another_context"),
            4 => {
                f.site.instruction = app(
                    "IRInst.store",
                    [
                        constant("IRTy.ptr_"),
                        nat(11),
                        nat(19),
                        constant("Bool.false"),
                    ],
                )
            }
            5 => {
                f.site.instruction = app(
                    "IRInst.store",
                    [
                        app("IRTy.func_", [nat(53)]),
                        nat(12),
                        nat(19),
                        constant("Bool.false"),
                    ],
                )
            }
            6 => {
                f.site.instruction = app(
                    "IRInst.store",
                    [
                        app("IRTy.func_", [nat(53)]),
                        nat(11),
                        nat(20),
                        constant("Bool.false"),
                    ],
                )
            }
            7 => f.site.site = constant("different_align_and_result_metadata"),
            8 => f.site.results = list("Nat", &[nat(61)]),
            9 => f.result.memory = constant("wrong_memory"),
            10 => f.result.value = constant("wrong_value"),
            11 => f.premises.evaluated.ty = constant("IRStepResult"),
            12 => f.premises.allocations.left = allocations(constant("another_memory")),
            13 => f.premises.allocations.right = allocations(constant("another_memory")),
            14 => f.premises.allocations.ty = constant("IRByteMemoryV1"),
            15 => f.premises.before.left = constant("Bool.true"),
            _ => f.current.frame = app("ir_frame_advance", [f.current.frame.clone()]),
        }
        assert!(transfer(&mut scope, &f).is_err(), "mutation {mutation}");
    }
}

#[test]
fn memory_candidates_keep_unchecked_facts_and_obey_construction_limits() {
    let mut scope = Scope::new();
    let mut f = fixture(&mut scope, 2);
    // Neither a narrow allocation equation nor a Rust transfer object grants
    // proof authority. Bogus values with unchanged endpoints reach replay.
    f.premises.allocations.term = constant("unchecked_allocation_proof");
    f.premises.evaluated.term = constant("unchecked_evaluation_proof");
    assert!(transfer(&mut scope, &f).is_ok());
    {
        let mut assembler = Assembler::new(
            &mut scope,
            Limits {
                max_operations: 1,
                ..limits()
            },
        )
        .unwrap();
        assert_eq!(
            f.site
                .memory_value(
                    &mut assembler,
                    &f.model,
                    &f.current,
                    f.result.clone(),
                    f.premises.clone(),
                )
                .err()
                .unwrap(),
            "execution construction operation budget exceeded"
        );
        assert_eq!(assembler.operations, 1);
    }
    // The closed memory presenter no longer needs seven helper locals. A
    // caller may spend its sole slot first: transfer still allocates none,
    // while a genuine second local request must fail without refunding work.
    let allocated_before = scope.allocated();
    let mut assembler = Assembler::new(
        &mut scope,
        Limits {
            max_locals: 1,
            ..limits()
        },
    )
    .unwrap();
    let held = assembler.local(constant("Nat")).unwrap();
    f.site
        .memory_value(
            &mut assembler,
            &f.model,
            &f.current,
            f.result.clone(),
            f.premises.clone(),
        )
        .unwrap();
    assert_eq!(assembler.locals, 1);
    assert_eq!(assembler.local_scope().allocated(), allocated_before + 1);
    let spent = assembler.operations;
    assert_eq!(
        assembler.local(constant("Nat")).err().unwrap(),
        "execution construction local budget exceeded"
    );
    assert_eq!(assembler.operations, spent + 1);
    assert!(assembler.local_scope().owns(&held));
}
