// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural tests of untrusted import assembly and scope/budget handling.
//! The named byte terms here have no invented evaluator or kernel axioms. Actual
//! byte-vocabulary replay is a separate consuming-environment requirement.

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
    target: CallTarget,
    site: FetchedSite,
    current: Current,
    result: ImportResult,
    premises: ImportPremises,
    arguments: Expr,
    parameters: Vec<Local>,
}

fn fixture(scope: &mut Scope, arity: usize) -> Fixture {
    let mut parameters = Vec::new();
    let mut local = |ty| {
        let local = scope.try_local(ty).unwrap();
        parameters.push(local.clone());
        local.term().clone()
    };
    let model = MachineModel {
        world_type: constant("Nat"),
        context: constant("test_context"),
        providers: local(app("IRByteProvidersV1", [constant("Nat")])),
    };
    let target = CallTarget {
        context: model.context.clone(),
        function_id: nat(55),
        binding: constant("test_import_binding"),
        signature: constant("test_import_signature"),
    };
    let operand_ids = list("Nat", &[nat(11), nat(5)]);
    let results = list(
        "Nat",
        &(0..arity)
            .map(|i| nat(u64::try_from(17 + i * 3).unwrap()))
            .collect::<Vec<_>>(),
    );
    let instruction = app("IRInst.call", [nat(55), operand_ids.clone()]);
    let site = FetchedSite {
        context: model.context.clone(),
        coordinate: Coordinate {
            function: FuncId::new(41),
            block: BlockId::new(13),
            instruction: 9,
        },
        function: constant("test_function"),
        block: constant("test_block"),
        node: app("IRNode.mk", [instruction.clone(), results.clone()]),
        instruction,
        results,
        site: constant("test_site"),
    };
    let current = Current {
        frame: app(
            "IRFrame.mk",
            [
                nat(41),
                nat(13),
                nat(9),
                local(app("IRList", [constant("IRBinding")])),
                local(app("IRList", [constant("Nat")])),
            ],
        ),
        tail: local(app("IRList", [constant("IRFrame")])),
        legacy_memory: local(app("IRList", [constant("IRMemSlot")])),
        legacy_cursor: local(constant("Nat")),
        world: app(
            "IRByteWorldV1.mk",
            [
                constant("Nat"),
                local(constant("IRByteMemoryV1")),
                local(constant("Nat")),
                local(app("IRList", [constant("Nat")])),
                local(constant("Nat")),
            ],
        ),
    };
    let arguments = list(
        "IRScalar",
        &[local(constant("IRScalar")), local(constant("IRScalar"))],
    );
    let values = if arity == 1 {
        // One aggregate value remains ONE SSA return, regardless of fields.
        list(
            "IRScalar",
            &[app(
                "IRScalar.aggv",
                [app(
                    "IRScalar.vcons",
                    [
                        app("IRScalar.int_", [nat(7)]),
                        app(
                            "IRScalar.vcons",
                            [app("IRScalar.int_", [nat(8)]), constant("IRScalar.vnil")],
                        ),
                    ],
                )],
            )],
        )
    } else {
        list(
            "IRScalar",
            &(0..arity)
                .map(|_| local(constant("IRScalar")))
                .collect::<Vec<_>>(),
        )
    };
    let result = ImportResult {
        values,
        memory: local(constant("IRByteMemoryV1")),
        host: local(constant("Nat")),
    };
    let mut fact = |ty: Expr, left: Expr, right: Expr| {
        let term = local(eq(&ty, left.clone(), right.clone()));
        PendingEquality::candidate(ty, left, right, term)
    };
    let checks = site
        .import_result_checks(&model, &target, &current, &result)
        .unwrap();
    let provider = site
        .import_provider_call(&model, &target, &current, arguments.clone())
        .unwrap();
    let premises = ImportPremises {
        resolved: fact(
            app("IRList", [constant("IRScalar")]),
            app("ir_resolve", [current.machine(), operand_ids]),
            arguments.clone(),
        ),
        imported: fact(constant("Bool"), checks.imported, constant("Bool.true")),
        admitted: fact(
            constant("Bool"),
            target.admission(&model, &site, arguments.clone()),
            constant("Bool.true"),
        ),
        provided: fact(
            app("IRByteImportResultV1", [constant("Nat")]),
            provider,
            result.provider_result(&model),
        ),
        memory_owners: fact(
            constant("Bool"),
            checks.memory_owners,
            constant("Bool.true"),
        ),
        arity: fact(constant("Bool"), checks.arity, constant("Bool.true")),
        typed: fact(constant("Bool"), checks.typed, constant("Bool.true")),
        before: fact(
            constant("Bool"),
            current.valid(&model),
            constant("Bool.true"),
        ),
    };
    Fixture {
        model,
        target,
        site,
        current,
        result,
        premises,
        arguments,
        parameters,
    }
}

fn transfer(scope: &mut Scope, f: &Fixture) -> Result<ImportTransfer> {
    f.site.import_return(
        &mut Assembler::new(scope, limits())?,
        &f.model,
        &f.target,
        &f.current,
        &f.result,
        f.premises.clone(),
    )
}

#[test]
fn import_transfer_preserves_returned_world_and_arbitrary_result_shape() {
    for arity in [0, 1, 3, 5, 7] {
        let mut scope = Scope::new();
        let f = fixture(&mut scope, arity);
        let transfer = transfer(&mut scope, &f).unwrap();
        let expected_frame = app(
            "ir_frame_advance",
            [app(
                "ir_frame_set_many",
                [
                    f.current.frame.clone(),
                    f.site.results.clone(),
                    f.result.values.clone(),
                ],
            )],
        );
        let expected_world = app(
            "IRByteWorldV1.mk",
            [
                constant("Nat"),
                f.result.memory.clone(),
                f.result.host.clone(),
                app(
                    "ir_byte_world_owners_v1",
                    [constant("Nat"), f.current.world.clone()],
                ),
                app(
                    "ir_byte_world_next_v1",
                    [constant("Nat"), f.current.world.clone()],
                ),
            ],
        );
        assert_eq!(transfer.current().frame, expected_frame);
        assert_eq!(transfer.current().world, expected_world);
        assert_eq!(transfer.current().tail, f.current.tail);
        assert_eq!(transfer.current().legacy_memory, f.current.legacy_memory);
        assert_eq!(transfer.current().legacy_cursor, f.current.legacy_cursor);
        assert_eq!(transfer.run().initial(), &f.current.running(&f.model));
        assert_eq!(
            transfer.run().reached(),
            &transfer.current().running(&f.model)
        );
        assert_eq!(transfer.run().fuel().term(), &nat(1));
        assert_eq!(
            transfer.step().left(),
            &f.model.step(f.current.running(&f.model))
        );
        assert_eq!(transfer.step().right(), transfer.run().reached());
        assert_eq!(transfer.valid().left(), &transfer.current().valid(&f.model));
        assert_eq!(transfer.valid().right(), &constant("Bool.true"));
        assert_eq!(
            transfer.valid().term(),
            &app(
                "ir_byte_import_world_shape_v1",
                [
                    constant("Nat"),
                    f.current.world.clone(),
                    f.current.frame.clone(),
                    expected_frame,
                    f.current.tail.clone(),
                    f.current.legacy_memory.clone(),
                    f.current.legacy_cursor.clone(),
                    f.result.memory.clone(),
                    f.result.host.clone(),
                    f.premises.before.term().clone(),
                    f.premises.memory_owners.term().clone(),
                ]
            )
        );
        assert_ne!(transfer.valid().term(), f.premises.before.term());
        for term in [
            transfer.step().term().clone(),
            transfer.run().equality().term().clone(),
            transfer.valid().term().clone(),
        ] {
            let closed = f.parameters.iter().rev().fold(term, |body, p| p.lam(body));
            assert!(!scope.close(&closed).unwrap().has_fvar_quick());
        }
    }
}

#[test]
fn import_transfer_refuses_wrong_call_provider_and_guard_endpoints() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope, 1);
    let run = |scope: &mut Scope, site: &FetchedSite, target: &CallTarget, p: ImportPremises| {
        site.import_return(
            &mut Assembler::new(scope, limits()).unwrap(),
            &f.model,
            target,
            &f.current,
            &f.result,
            p,
        )
    };
    for instruction in [
        app("IRInst.ret", [list("Nat", &[])]),
        app("IRInst.call", [nat(55)]),
        app("IRInst.call", [nat(56), list("Nat", &[nat(11), nat(5)])]),
        app("IRInst.call", [nat(55), list("Nat", &[nat(5), nat(11)])]),
    ] {
        let mut site = f.site.clone();
        site.instruction = instruction;
        assert!(run(&mut scope, &site, &f.target, f.premises.clone()).is_err());
    }
    let mut foreign = f.target.clone();
    foreign.context = constant("other_context");
    assert!(run(&mut scope, &f.site, &foreign, f.premises.clone()).is_err());
    let mut wrong = f.premises.clone();
    wrong.provided.left = Expr::apps(
        f.model.providers.clone(),
        [
            nat(56),
            f.arguments.clone(),
            app(
                "ir_byte_world_memory_v1",
                [constant("Nat"), f.current.world.clone()],
            ),
            app(
                "ir_byte_world_host_v1",
                [constant("Nat"), f.current.world.clone()],
            ),
        ],
    );
    assert!(run(&mut scope, &f.site, &f.target, wrong).is_err());
    let mut wrong = f.premises.clone();
    wrong.provided.left = Expr::apps(
        f.model.providers.clone(),
        [
            app("ir_byte_binding_fid_v1", [f.target.binding.clone()]),
            f.arguments.clone(),
            f.result.memory.clone(),
            f.result.host.clone(),
        ],
    );
    assert!(run(&mut scope, &f.site, &f.target, wrong).is_err());
    let mut wrong = f.premises.clone();
    wrong.provided.right = app(
        "IRByteImportResultV1.mk",
        [
            constant("Nat"),
            app("IROutcome.type_error", [constant("IRFault.bad_field")]),
            f.result.memory.clone(),
            f.result.host.clone(),
        ],
    );
    assert!(run(&mut scope, &f.site, &f.target, wrong).is_err());
    let mut wrong = f.premises.clone();
    wrong.provided.right = app(
        "IRByteImportResultV1.mk",
        [
            constant("Nat"),
            app("IROutcome.ret", [f.result.values.clone()]),
            app(
                "ir_byte_world_memory_v1",
                [constant("Nat"), f.current.world.clone()],
            ),
            app(
                "ir_byte_world_host_v1",
                [constant("Nat"), f.current.world.clone()],
            ),
        ],
    );
    assert!(run(&mut scope, &f.site, &f.target, wrong).is_err());
    for index in 0..6 {
        let mut wrong = f.premises.clone();
        let slot = match index {
            0 => &mut wrong.imported,
            1 => &mut wrong.admitted,
            2 => &mut wrong.memory_owners,
            3 => &mut wrong.arity,
            4 => &mut wrong.typed,
            _ => &mut wrong.before,
        };
        *slot = PendingEquality::reflexive(constant("Bool"), constant("Bool.true"));
        assert!(run(&mut scope, &f.site, &f.target, wrong).is_err());
    }
}

#[test]
fn import_transfer_respects_candidate_operation_limit() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope, 1);
    let mut bounded = limits();
    bounded.max_operations = 1;
    let error = f
        .site
        .import_return(
            &mut Assembler::new(&mut scope, bounded).unwrap(),
            &f.model,
            &f.target,
            &f.current,
            &f.result,
            f.premises,
        )
        .err()
        .expect("full candidate composition cannot fit one operation");
    assert_eq!(error, "execution construction operation budget exceeded");
}

#[test]
fn import_transfer_keeps_exact_cold_operation_boundary_without_argument_local() {
    for max_operations in [28, 29] {
        let mut scope = Scope::new();
        let f = fixture(&mut scope, 1);
        let mut policy = limits();
        policy.max_operations = max_operations;
        policy.max_locals = 1;
        let mut assembler = Assembler::new(&mut scope, policy).unwrap();
        let result = f.site.import_return(
            &mut assembler,
            &f.model,
            &f.target,
            &f.current,
            &f.result,
            f.premises.clone(),
        );
        assert_eq!(assembler.operations, max_operations);
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.local_scope().allocated(), f.parameters.len());
        if max_operations == 29 {
            assert!(result.is_ok());
        } else {
            assert_eq!(
                result.err().unwrap(),
                "execution construction operation budget exceeded"
            );
        }
    }
}

#[test]
fn import_transfer_keeps_cumulative_charges_without_argument_mapper_locals() {
    for max_operations in [48, 49] {
        let mut scope = Scope::new();
        let f = fixture(&mut scope, 1);
        let mut policy = limits();
        policy.max_operations = max_operations;
        policy.max_locals = 1;
        let mut assembler = Assembler::new(&mut scope, policy).unwrap();
        f.site
            .import_return(
                &mut assembler,
                &f.model,
                &f.target,
                &f.current,
                &f.result,
                f.premises.clone(),
            )
            .unwrap();
        assert_eq!((assembler.operations, assembler.locals), (29, 0));
        let result = f.site.import_return(
            &mut assembler,
            &f.model,
            &f.target,
            &f.current,
            &f.result,
            f.premises.clone(),
        );
        assert_eq!(assembler.operations, max_operations);
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.local_scope().allocated(), f.parameters.len());
        if max_operations == 49 {
            assert!(result.is_ok());
        } else {
            assert_eq!(
                result.err().unwrap(),
                "execution construction operation budget exceeded"
            );
        }
    }
}

#[test]
fn import_transfer_with_exhausted_local_allowance_keeps_all_twenty_nine_charges() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope, 1);
    let mut policy = limits();
    policy.max_operations = 30;
    policy.max_locals = 1;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    assembler.local(constant("Nat")).unwrap();
    let operations = assembler.operations;
    f.site
        .import_return(
            &mut assembler,
            &f.model,
            &f.target,
            &f.current,
            &f.result,
            f.premises.clone(),
        )
        .unwrap();
    assert_eq!(assembler.operations - operations, 29);
    assert_eq!((assembler.operations, assembler.locals), (30, 1));
    assert_eq!(assembler.local_scope().allocated(), f.parameters.len() + 1);
    let error = f
        .site
        .import_return(
            &mut assembler,
            &f.model,
            &f.target,
            &f.current,
            &f.result,
            f.premises,
        )
        .err()
        .unwrap();
    assert_eq!(error, "execution construction operation budget exceeded");
    assert_eq!((assembler.operations, assembler.locals), (30, 1));
}
