// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordinary reflected IR and the existing ByteV1 kernel vocabulary. Allocation
//! success is derived from the generic range law, never an assumed step or the
//! specialized frame16 theorem. No TLA semantics or native authority is involved.

use super::*;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{Endianness, Inst, Module, StructPassingPolicy, TargetInfo, Ty};

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}
fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(&ty, right))
}
fn truth(left: Expr) -> PendingEquality {
    conversion(constant("Bool"), left, constant("Bool.true"))
}
fn replay(scope: &Scope, parameters: &[Local], proof: &PendingEquality, accepted: bool) {
    let term = parameters
        .iter()
        .rev()
        .fold(proof.term.clone(), |body, p| p.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(proof.proposition(), |body, p| p.pi(body));
    let term = scope.close(&term).unwrap();
    let claim = scope.close(&claim).unwrap();
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .unwrap();
    if accepted {
        checker.check_type(&term, &claim).unwrap();
        assert!(
            environment()
                .audit_certification(&claim, &term)
                .is_certified()
        );
    } else {
        assert!(matches!(
            checker.check_type(&term, &claim),
            Err(KernelTypeError::TypeMismatch { .. })
        ));
    }
}
fn providers() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        constant("Nat"),
        Expr::lam(
            BinderInfo::Default,
            app("IRList", [constant("IRScalar")]),
            Expr::lam(
                BinderInfo::Default,
                constant("IRByteMemoryV1"),
                Expr::lam(
                    BinderInfo::Default,
                    constant("Nat"),
                    app(
                        "IRByteImportResultV1.mk",
                        [
                            constant("Nat"),
                            app("IROutcome.stuck", [constant("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    )
}
fn world(memory: Expr) -> Expr {
    app(
        "IRByteWorldV1.mk",
        [
            constant("Nat"),
            memory,
            nat(37),
            list("Nat", &[nat(8)]),
            nat(9),
        ],
    )
}
fn old_memory(rows: Expr, bytes: Expr) -> Expr {
    app("IRByteMemoryV1.mk", [rows, bytes, nat(65)])
}
fn row(base: u64, size: u64, owner: u64, live: bool) -> Expr {
    app(
        "IRByteAllocationV1.mk",
        [
            nat(base),
            nat(size),
            nat(owner),
            constant(if live { "Bool.true" } else { "Bool.false" }),
        ],
    )
}
fn fixture(explicit: bool, align: u64, ty: Ty) -> (Module, FuncId, BlockId, ValueId, ValueId) {
    let mut builder = ModuleBuilder::new_with_target_info(
        "ordinary_lexical_allocation",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let ty = if explicit {
        ty
    } else {
        Ty::Array(builder.add_type(ty), 24)
    };
    let signature = builder.add_func_type(vec![Ty::I64], vec![Ty::Ptr]);
    let function = builder.declare_function("scratch", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let count = body.add_block_param(block, Ty::I64);
    body.switch_to_block(block);
    let result = body.emit(Inst::Alloca {
        ty,
        count: explicit.then_some(count),
        align: Some(align),
    });
    body.ret(vec![result]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    (module, function, block, count, result)
}

fn current(function: FuncId, block: BlockId, count: ValueId, value: Expr, memory: Expr) -> Current {
    Current {
        frame: app(
            "IRFrame.mk",
            [
                nat(function.index().into()),
                nat(block.index().into()),
                nat(0),
                list(
                    "IRBinding",
                    &[app("IRBinding.mk", [nat(count.index().into()), value])],
                ),
                list("Nat", &[]),
            ],
        ),
        tail: list("IRFrame", &[]),
        legacy_memory: list("IRMemSlot", &[]),
        legacy_cursor: nat(0),
        world: world(memory),
    }
}

#[allow(clippy::too_many_arguments)] // Explicit generic theorem telescope.
fn premises(
    checks: AllocationChecks,
    before: &Current,
    model: &MachineModel,
    rows: Expr,
    bytes: Expr,
    high_water: Expr,
    old_owners: Expr,
    owner: u64,
    size: u64,
) -> AllocationPremises {
    let positive = |n| app("Nat.zero_lt_succ", [nat(n - 1)]);
    let bound = |n| app("Nat.le_add_right", [nat(n), nat(u64::MAX - n + 1)]);
    // The generic range law handles arbitrary allocation rows and byte maps.
    let evaluated = PendingEquality::candidate(
        constant("IRByteMemoryResultV1"),
        checks.evaluation,
        app(
            "IRByteMemoryResultV1.value",
            [
                app("IRScalar.ptr_", [nat(72)]),
                app(
                    "ir_byte_fresh_memory_v1",
                    [rows.clone(), bytes.clone(), nat(72), nat(size), nat(owner)],
                ),
            ],
        ),
        app(
            "ir_byte_fresh_allocate_range_v1",
            [
                rows.clone(),
                bytes.clone(),
                nat(65),
                nat(8),
                nat(size),
                nat(owner),
                positive(65),
                positive(size),
                app("Nat.le_add_right", [nat(65), nat(7)]),
                refl(&constant("Bool"), constant("Bool.true")),
                bound(73 + size),
                high_water,
            ],
        ),
    );
    AllocationPremises {
        dispatch: conversion(model.config_type(), checks.dispatch, checks.dispatched),
        evaluated,
        result: truth(checks.result),
        owners: PendingEquality::candidate(
            constant("Bool"),
            checks.owners,
            constant("Bool.true"),
            app(
                "ir_byte_memory_owners_fresh_v1",
                [
                    rows,
                    bytes,
                    nat(65),
                    nat(72),
                    nat(size),
                    nat(owner),
                    list("Nat", &[]),
                    nat(9),
                    refl(&constant("Bool"), constant("Bool.true")),
                    old_owners.clone(),
                    positive(72),
                    positive(size),
                    bound(72 + size),
                ],
            ),
        ),
        before: PendingEquality::candidate(
            constant("Bool"),
            before.valid(model),
            constant("Bool.true"),
            old_owners,
        ),
    }
}

#[test]
fn allocation_replays_arbitrary_history_bytes_and_actual_lexical_owner() {
    let (module, function, block, count, destination) = fixture(true, 8, Ty::I64);
    let reflected = reflect_core_module_v1(&module, &[(function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog
        .fetch(Coordinate {
            function,
            block,
            instruction: 0,
        })
        .unwrap();
    let mut scope = Scope::new();
    let rows = scope
        .try_local(app("IRList", [constant("IRByteAllocationV1")]))
        .unwrap();
    let bytes = scope
        .try_local(Expr::pi(
            BinderInfo::Default,
            constant("Nat"),
            app("IROption", [constant("Nat")]),
        ))
        .unwrap();
    let old = old_memory(rows.term().clone(), bytes.term().clone());
    let high_water = scope
        .try_local(app("ir_byte_high_water_v1", [rows.term().clone(), nat(65)]))
        .unwrap();
    let old_guard = app(
        "ir_byte_memory_owners_v1",
        [old.clone(), list("Nat", &[nat(8)]), nat(9)],
    );
    let owners = scope
        .try_local(eq(&constant("Bool"), old_guard, constant("Bool.true")))
        .unwrap();
    let before = current(function, block, count, app("IRScalar.int_", [nat(3)]), old);
    let input = AllocationInput {
        owner: nat(8),
        count: nat(3),
    };
    let result = MemoryResult {
        value: app("IRScalar.ptr_", [nat(72)]),
        memory: app(
            "ir_byte_fresh_memory_v1",
            [
                rows.term().clone(),
                bytes.term().clone(),
                nat(72),
                nat(24),
                nat(8),
            ],
        ),
    };
    let checks = site
        .allocation_checks(&model, &before, &input, &result)
        .unwrap();
    let p = premises(
        checks,
        &before,
        &model,
        rows.term().clone(),
        bytes.term().clone(),
        high_water.term().clone(),
        owners.term().clone(),
        8,
        24,
    );
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let transfer = site
        .allocation_value(&mut assembler, &model, &before, input, result.clone(), p)
        .unwrap();
    // Independently spelled PC, binding, ownership, bytes and cursor endpoint.
    let fields = before.frame.get_app_args();
    let expected = Current {
        frame: app(
            "IRFrame.mk",
            [
                nat(function.index().into()),
                nat(block.index().into()),
                nat(1),
                app(
                    "IRList.cons",
                    [
                        constant("IRBinding"),
                        app(
                            "IRBinding.mk",
                            [nat(destination.index().into()), result.value],
                        ),
                        fields[3].clone(),
                    ],
                ),
                list("Nat", &[]),
            ],
        ),
        world: world(result.memory),
        ..before.clone()
    };
    let goal = PendingEquality::candidate(
        model.config_type(),
        model.run(&NatTerm::literal(1), before.running(&model)),
        expected.running(&model),
        transfer.run().equality().term().clone(),
    );
    drop(assembler);
    let parameters = [rows, bytes, high_water, owners];
    replay(&scope, &parameters, &goal, true);
    replay(&scope, &parameters, transfer.valid(), true);
}

#[test]
fn allocation_inhabited_witness_and_wrong_metadata_are_kernel_checked() {
    // Includes a live global and retired history. Neither may be deleted/reused.
    let rows = list(
        "IRByteAllocationV1",
        &[row(16, 8, 0, true), row(32, 8, 7, false)],
    );
    let bytes = Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(173)));
    // 0/1: live witnesses for explicit/default count. Remaining rows alter
    // count, active owner, alignment, layout/extent, scalar kind, signed bound,
    // zero count, allocation cursor and overlapping live history, respectively.
    for mutant in 0..11 {
        let rows = if mutant == 10 {
            app(
                "IRList.cons",
                [
                    constant("IRByteAllocationV1"),
                    row(72, 16, 0, true),
                    rows.clone(),
                ],
            )
        } else {
            rows.clone()
        };
        let explicit = mutant != 1;
        let ty = if mutant == 5 {
            Ty::I32
        } else if explicit {
            Ty::I64
        } else {
            Ty::I8
        };
        let (module, function, block, count, _) =
            fixture(explicit, if mutant == 4 { 16 } else { 8 }, ty);
        let reflected = reflect_core_module_v1(&module, &[(function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let site = catalog
            .fetch(Coordinate {
                function,
                block,
                instruction: 0,
            })
            .unwrap();
        let value = if mutant == 6 {
            app("IRScalar.ptr_", [nat(3)])
        } else {
            app(
                "IRScalar.int_",
                [nat(if mutant == 7 {
                    1_u64 << 63
                } else if mutant == 8 {
                    0
                } else {
                    3
                })],
            )
        };
        let before = current(
            function,
            block,
            count,
            value,
            if mutant == 9 {
                app("IRByteMemoryV1.mk", [rows.clone(), bytes.clone(), nat(0)])
            } else {
                old_memory(rows.clone(), bytes.clone())
            },
        );
        let owner = if mutant == 3 { 0 } else { 8 };
        let size = 24;
        let input = AllocationInput {
            owner: nat(owner),
            count: nat(if !explicit {
                1
            } else if mutant == 8 {
                0
            } else if mutant == 2 {
                2
            } else {
                3
            }),
        };
        let result = MemoryResult {
            value: app("IRScalar.ptr_", [nat(72)]),
            memory: app(
                "ir_byte_fresh_memory_v1",
                [rows.clone(), bytes.clone(), nat(72), nat(size), nat(owner)],
            ),
        };
        let checks = site
            .allocation_checks(&model, &before, &input, &result)
            .unwrap();
        let high_water = app(
            "And.intro",
            [
                app("Nat.lt", [nat(24), nat(65)]),
                app("And", [app("Nat.lt", [nat(40), nat(65)]), constant("True")]),
                app("Nat.le_add_right", [nat(25), nat(40)]),
                app(
                    "And.intro",
                    [
                        app("Nat.lt", [nat(40), nat(65)]),
                        constant("True"),
                        app("Nat.le_add_right", [nat(41), nat(24)]),
                        constant("True.intro"),
                    ],
                ),
            ],
        );
        let p = premises(
            checks,
            &before,
            &model,
            rows.clone(),
            bytes.clone(),
            high_water,
            refl(&constant("Bool"), constant("Bool.true")),
            owner,
            size,
        );
        let mut scope = Scope::new();
        if mutant == 0 {
            let ret = catalog
                .fetch(Coordinate {
                    function,
                    block,
                    instruction: 1,
                })
                .unwrap();
            assert!(
                ret.allocation_checks(&model, &before, &input, &result)
                    .is_err()
            );
            let mut exhausted = limits();
            exhausted.max_operations = 1;
            let mut limited = Assembler::new(&mut scope, exhausted).unwrap();
            assert!(
                site.allocation_value(
                    &mut limited,
                    &model,
                    &before,
                    input.clone(),
                    result.clone(),
                    p.clone()
                )
                .err()
                .unwrap()
                .contains("budget")
            );
            drop(limited);
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let mut stale = p.clone();
            stale.owners.left = app(
                "ir_byte_memory_owners_v1",
                [
                    old_memory(rows.clone(), bytes.clone()),
                    list("Nat", &[nat(8)]),
                    nat(9),
                ],
            );
            assert!(
                site.allocation_value(
                    &mut assembler,
                    &model,
                    &before,
                    input.clone(),
                    result.clone(),
                    stale
                )
                .is_err()
            );
            let mut stale = p.clone();
            stale.dispatch.right = before.running(&model);
            assert!(
                site.allocation_value(
                    &mut assembler,
                    &model,
                    &before,
                    input.clone(),
                    result.clone(),
                    stale
                )
                .is_err()
            );
        }
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let transfer = site
            .allocation_value(&mut assembler, &model, &before, input, result, p)
            .unwrap();
        drop(assembler);
        replay(&scope, &[], transfer.run().equality(), mutant < 2);
        if mutant < 2 {
            replay(&scope, &[], transfer.valid(), true);
        }
    }
}

#[test]
fn allocation_dispatch_and_binding_guards_reject_independent_counterexamples() {
    let (module, function, block, count, _) = fixture(true, 8, Ty::I64);
    let reflected = reflect_core_module_v1(&module, &[(function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog
        .fetch(Coordinate {
            function,
            block,
            instruction: 0,
        })
        .unwrap();
    let rows = list("IRByteAllocationV1", &[]);
    let bytes = Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(173)));
    let memory = old_memory(rows.clone(), bytes.clone());
    let before = current(
        function,
        block,
        count,
        app("IRScalar.int_", [nat(3)]),
        memory.clone(),
    );
    let input = AllocationInput {
        owner: nat(8),
        count: nat(3),
    };
    let result = MemoryResult {
        value: app("IRScalar.ptr_", [nat(72)]),
        memory: app(
            "ir_byte_fresh_memory_v1",
            [rows.clone(), bytes.clone(), nat(72), nat(24), nat(8)],
        ),
    };
    let scope = Scope::new();
    let mut absent = before.clone();
    absent.world = app(
        "IRByteWorldV1.mk",
        [
            constant("Nat"),
            memory.clone(),
            nat(37),
            list("Nat", &[]),
            nat(9),
        ],
    );
    let checks = site
        .allocation_checks(&model, &absent, &input, &result)
        .unwrap();
    replay(
        &scope,
        &[],
        &conversion(model.config_type(), checks.dispatch, checks.dispatched),
        false,
    );

    // Matching count on both sides: refusal is the signed64 dispatch domain,
    // not a mismatched resolved count or a forged allocator evaluation proof.
    let negative_count = current(
        function,
        block,
        count,
        app("IRScalar.int_", [nat(1_u64 << 63)]),
        memory,
    );
    let negative_input = AllocationInput {
        owner: nat(8),
        count: nat(1_u64 << 63),
    };
    let checks = site
        .allocation_checks(&model, &negative_count, &negative_input, &result)
        .unwrap();
    replay(
        &scope,
        &[],
        &conversion(model.config_type(), checks.dispatch, checks.dispatched),
        false,
    );

    let wrong_value = MemoryResult {
        value: app("IRScalar.int_", [nat(72)]),
        ..result.clone()
    };
    let checks = site
        .allocation_checks(&model, &before, &input, &wrong_value)
        .unwrap();
    replay(&scope, &[], &truth(checks.result), false);
    let mut wrong_arity = site.clone();
    wrong_arity.results = list("Nat", &[]);
    let checks = wrong_arity
        .allocation_checks(&model, &before, &input, &result)
        .unwrap();
    replay(&scope, &[], &truth(checks.result), false);
    let wrong_owner = MemoryResult {
        memory: app(
            "ir_byte_fresh_memory_v1",
            [rows, bytes, nat(72), nat(24), nat(9)],
        ),
        ..result
    };
    let checks = site
        .allocation_checks(&model, &before, &input, &wrong_owner)
        .unwrap();
    replay(&scope, &[], &truth(checks.owners), false);
}
