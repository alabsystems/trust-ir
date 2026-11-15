// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The genuine fetched Const U64 -> Some(original SSA count) Alloca prefix.
//! Source bodies, nominal types, count IDs and complete byte worlds are retained.
//! These are independently replayed shared-model conditional claims, not TY
//! denotation, caller permissions, native receipts or an executed Return.

use super::*;
use crate::ModuleBuilder;
use crate::core_reflection::{
    CoreMemoryIndexProfileV1, reflect_core_module_v1, reflect_core_module_v1_with_memory_profile,
};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{Constant, Endianness, Inst, Module, StructPassingPolicy, TargetInfo, Ty};

#[path = "core_execution_typed_alloca_closed_tests.rs"]
mod closed_dispatch;

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

fn checker() -> TypeChecker<'static> {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
}

fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(&ty, right))
}

fn truth(left: Expr) -> PendingEquality {
    conversion(constant("Bool"), left, constant("Bool.true"))
}

fn close(scope: &Scope, parameters: &[Local], proof: &PendingEquality) -> (Expr, Expr) {
    let term = parameters
        .iter()
        .rev()
        .fold(proof.term().clone(), |body, parameter| parameter.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(proof.proposition(), |body, parameter| parameter.pi(body));
    (scope.close(&term).unwrap(), scope.close(&claim).unwrap())
}

fn replay(scope: &Scope, parameters: &[Local], proof: &PendingEquality, accepted: bool) {
    let (term, claim) = close(scope, parameters, proof);
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let checker = checker();
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
        let error = checker.check_type(&term, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "a genuine mismatch, never a construction or kernel-budget refusal: {error:?}"
        );
    }
}

fn replay_dag(scope: &Scope, parameters: &[Local], proof: &PendingEquality) {
    replay(scope, parameters, proof, true);
    let (term, claim) = close(scope, parameters, proof);
    let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
    assert_eq!(
        decoded, term,
        "the complete changed-world proof is retained"
    );
    checker().check_type(&decoded, &claim).unwrap();
    assert!(
        environment()
            .audit_certification(&claim, &decoded)
            .is_certified()
    );
}

fn providers() -> Expr {
    providers_for(constant("Nat"))
}

fn providers_for(world_type: Expr) -> Expr {
    // Neither fetched source instruction is an import. Keep the actual total
    // model provider argument rather than replacing the evaluator vocabulary.
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
                    world_type.clone(),
                    app(
                        "IRByteImportResultV1.mk",
                        [
                            world_type,
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

fn rows() -> Expr {
    list("IRByteAllocationV1", &[])
}

fn bytes() -> Expr {
    Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(173)))
}

fn memory(rows: Expr, bytes: Expr, cursor: u64) -> Expr {
    app("IRByteMemoryV1.mk", [rows, bytes, nat(cursor)])
}

fn world(memory: Expr, owners: Expr) -> Expr {
    app(
        "IRByteWorldV1.mk",
        [constant("Nat"), memory, nat(37), owners, nat(9)],
    )
}

struct Fixture {
    module: Module,
    function: FuncId,
    block: BlockId,
    count: ValueId,
    pointer: ValueId,
}

fn fixture(count: u64, pointee: Ty, align: u64) -> Fixture {
    fixture_with_count(count, pointee, align, true)
}

fn fixture_with_count(count: u64, pointee: Ty, align: u64, explicit: bool) -> Fixture {
    let mut builder = ModuleBuilder::new_with_target_info(
        "original_typed_const_allocation",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![], vec![Ty::Ptr]);
    let function = builder.declare_function("typed_scratch", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    body.switch_to_block(block);
    let count = body.emit(Inst::Const {
        ty: Ty::U64,
        value: Constant::Int(i128::from(count)),
    });
    let pointer = body.emit(Inst::Alloca {
        ty: pointee,
        count: explicit.then_some(count),
        align: Some(align),
    });
    // This source terminator makes the ordinary fixture valid. The claims
    // below stop after the real two-instruction prefix, never fetch Return.
    body.ret(vec![pointer]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    Fixture {
        module,
        function,
        block,
        count,
        pointer,
    }
}

impl Fixture {
    fn coordinate(&self, instruction: usize) -> Coordinate {
        Coordinate {
            function: self.function,
            block: self.block,
            instruction,
        }
    }

    fn current(&self, memory: Expr, owners: Expr, pc: u64, bindings: Expr) -> Current {
        Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(self.function.index().into()),
                    nat(self.block.index().into()),
                    nat(pc),
                    bindings,
                    list("Nat", &[]),
                ],
            ),
            tail: list("IRFrame", &[]),
            legacy_memory: list("IRMemSlot", &[]),
            legacy_cursor: nat(0),
            world: world(memory, owners),
        }
    }

    fn before(&self, memory: Expr) -> Current {
        self.current(memory, list("Nat", &[nat(8)]), 0, list("IRBinding", &[]))
    }

    fn after_const(&self, memory: Expr, count: Expr) -> Current {
        self.current(
            memory,
            list("Nat", &[nat(8)]),
            1,
            list("IRBinding", &[binding(self.count, count)]),
        )
    }
}

fn binding(id: ValueId, value: Expr) -> Expr {
    app("IRBinding.mk", [nat(id.index().into()), value])
}

fn scalar(
    site: &FetchedSite,
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    before: &Current,
    value: Expr,
    before_valid: PendingEquality,
) -> ScalarTransfer {
    let checks = site.scalar_checks(model, before, value.clone()).unwrap();
    site.scalar_value(
        assembler,
        model,
        before,
        value.clone(),
        ScalarPremises {
            evaluated: conversion(
                constant("IRStepResult"),
                checks.evaluation,
                app("IRStepResult.value", [value]),
            ),
            operands: truth(checks.operands),
            result: truth(checks.result),
            before: before_valid,
        },
    )
    .unwrap()
}

fn result(rows: Expr, bytes: Expr, owner: u64, size: u64) -> MemoryResult {
    MemoryResult {
        value: app("IRScalar.ptr_", [nat(72)]),
        memory: app(
            "ir_byte_fresh_memory_v1",
            [rows, bytes, nat(72), nat(size), nat(owner)],
        ),
    }
}

fn concrete_premises(
    checks: AllocationChecks,
    model: &MachineModel,
    before: &Current,
    result: &MemoryResult,
) -> AllocationPremises {
    AllocationPremises {
        dispatch: conversion(model.config_type(), checks.dispatch, checks.dispatched),
        evaluated: conversion(
            constant("IRByteMemoryResultV1"),
            checks.evaluation,
            result.result(),
        ),
        result: truth(checks.result),
        owners: truth(checks.owners),
        before: truth(before.valid(model)),
    }
}

fn dispatch(
    assembler: &mut Assembler<'_>,
    site: &FetchedSite,
    model: &MachineModel,
    before: &Current,
    input: &AllocationInput,
    literal: u64,
) -> PendingEquality {
    dispatch_with_tail(
        assembler,
        site,
        model,
        before,
        input,
        literal,
        list("Nat", &[]),
    )
}

fn dispatch_with_tail(
    assembler: &mut Assembler<'_>,
    site: &FetchedSite,
    model: &MachineModel,
    before: &Current,
    input: &AllocationInput,
    literal: u64,
    tail: Expr,
) -> PendingEquality {
    assert_eq!(input.count, nat(literal));
    let checks = site
        .allocation_dispatch_checks(model, before, input, tail.clone())
        .unwrap();
    let equality = |(ty, left, right): (Expr, Expr, Expr)| conversion(ty, left, right);
    let bound = PendingProof::candidate(
        checks.count_bound,
        app(
            "Nat.le_add_right",
            [
                app("Nat.succ", [input.count.clone()]),
                nat((1_u64 << 63).saturating_sub(literal.saturating_add(1))),
            ],
        ),
    );
    site.allocation_dispatch(
        assembler,
        model,
        before,
        input,
        tail,
        AllocationDispatchPremises {
            owners: equality(checks.owners),
            count: equality(checks.count),
            count_bound: bound,
        },
    )
    .unwrap()
}

#[test]
fn typed_alloca_fetched_const_u64_one_and_original_count_replay_complete_world_dag_v2() {
    let f = fixture(1, Ty::I64, 8);
    let original = f.module.clone(); // Source identity oracle only.
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap();
    assert!(std::ptr::eq(reflected.module(), &f.module));
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let constant_site = catalog.fetch(f.coordinate(0)).unwrap();
    let allocation_site = catalog.fetch(f.coordinate(1)).unwrap();
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
    let high_water = scope
        .try_local(app("ir_byte_high_water_v1", [rows.term().clone(), nat(65)]))
        .unwrap();
    let old_memory = memory(rows.term().clone(), bytes.term().clone(), 65);
    let old_guard = app(
        "ir_byte_memory_owners_v1",
        [old_memory.clone(), list("Nat", &[nat(8)]), nat(9)],
    );
    let owners = scope
        .try_local(eq(
            &constant("Bool"),
            old_guard.clone(),
            constant("Bool.true"),
        ))
        .unwrap();
    let before = f.before(old_memory);
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let owner_proof = PendingEquality::candidate(
        constant("Bool"),
        old_guard.clone(),
        constant("Bool.true"),
        owners.term().clone(),
    );
    let before_valid = assembler
        .conversion(constant("Bool"), before.valid(&model), old_guard)
        .unwrap();
    let before_valid = assembler.compose(before_valid, owner_proof).unwrap();
    let first = scalar(
        &constant_site,
        &mut assembler,
        &model,
        &before,
        app("IRScalar.int_", [nat(1)]),
        before_valid,
    );
    let input = AllocationInput {
        owner: nat(8),
        count: nat(1),
    };
    let result = result(rows.term().clone(), bytes.term().clone(), 8, 8);
    let checks = allocation_site
        .allocation_checks(&model, first.current(), &input, &result)
        .unwrap();
    let dispatch = dispatch(
        &mut assembler,
        &allocation_site,
        &model,
        first.current(),
        &input,
        1,
    );
    let positive = |n: u64| app("Nat.zero_lt_succ", [nat(n - 1)]);
    let bound = |n| app("Nat.le_add_right", [nat(n), nat(u64::MAX - n + 1)]);
    let evaluated = PendingEquality::candidate(
        constant("IRByteMemoryResultV1"),
        checks.evaluation,
        result.result(),
        app(
            "ir_byte_fresh_allocate_range_v1",
            [
                rows.term().clone(),
                bytes.term().clone(),
                nat(65),
                nat(8),
                nat(8),
                nat(8),
                positive(65),
                positive(8),
                app("Nat.le_add_right", [nat(65), nat(7)]),
                refl(&constant("Bool"), constant("Bool.true")),
                bound(81),
                high_water.term().clone(),
            ],
        ),
    );
    let returned_owners = PendingEquality::candidate(
        constant("Bool"),
        checks.owners,
        constant("Bool.true"),
        app(
            "ir_byte_memory_owners_fresh_v1",
            [
                rows.term().clone(),
                bytes.term().clone(),
                nat(65),
                nat(72),
                nat(8),
                nat(8),
                list("Nat", &[]),
                nat(9),
                refl(&constant("Bool"), constant("Bool.true")),
                owners.term().clone(),
                positive(72),
                positive(8),
                bound(80),
            ],
        ),
    );
    let second = allocation_site
        .allocation_value(
            &mut assembler,
            &model,
            first.current(),
            input,
            result.clone(),
            AllocationPremises {
                dispatch,
                evaluated,
                result: truth(checks.result),
                owners: returned_owners,
                before: first.valid().clone(),
            },
        )
        .unwrap();
    let boundary = assembler
        .conversion(
            model.config_type(),
            first.run().reached().clone(),
            second.run().initial().clone(),
        )
        .unwrap();
    let first_run = assembler
        .transport_reached(first.run().clone(), boundary)
        .unwrap();
    let run = assembler
        .concatenate(first_run, second.run().clone())
        .unwrap();
    // Independent endpoint: both original SSA results, PC=2, unchanged host,
    // lexical owners/next, and the entire new allocation history/bytes/cursor.
    let expected = f.current(
        result.memory.clone(),
        list("Nat", &[nat(8)]),
        2,
        list(
            "IRBinding",
            &[
                binding(f.pointer, result.value),
                binding(f.count, app("IRScalar.int_", [nat(1)])),
            ],
        ),
    );
    let endpoint = assembler
        .conversion(
            model.config_type(),
            run.reached().clone(),
            expected.running(&model),
        )
        .unwrap();
    let run = assembler.transport_reached(run, endpoint).unwrap();
    let fuel = assembler
        .conversion(constant("Nat"), run.fuel().term().clone(), nat(2))
        .unwrap();
    drop(assembler);
    let parameters = [rows, bytes, high_water, owners];
    replay_dag(&scope, &parameters, run.equality());
    replay(&scope, &parameters, second.valid(), true);
    replay(&scope, &parameters, &fuel, true);
    assert_eq!(f.module, original);
}

#[test]
fn typed_alloca_nominal_u64_original_some_count_is_not_rewritten_for_reflection() {
    let f = fixture(1, Ty::I64, 8);
    assert_eq!(
        reflect_core_module_v1(&f.module, &[(f.function, 4096)])
            .unwrap_err()
            .to_string(),
        "byte profile requires typed I64 allocation count"
    );
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap();
    assert!(std::ptr::eq(reflected.module(), &f.module));
    let body = &reflected.module().functions[0].blocks[0].body;
    assert_eq!(body.len(), 3);
    assert!(matches!(
        body[0].inst,
        Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(1)
        }
    ));
    assert_eq!(body[0].results, [f.count]);
    assert!(
        matches!(body[1].inst, Inst::Alloca { ty: Ty::I64, count: Some(count), align: Some(8) } if count == f.count)
    );
    assert_eq!(body[1].results, [f.pointer]);
}

#[test]
fn typed_alloca_actual_dispatch_rejects_forged_count_read_and_owner_candidates() {
    let f = fixture(1, Ty::I64, 8);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog.fetch(f.coordinate(1)).unwrap();
    let old = memory(rows(), bytes(), 65);
    for mutant in 0..6 {
        let mut before = f.after_const(old.clone(), app("IRScalar.int_", [nat(1)]));
        let mut input = AllocationInput {
            owner: nat(8),
            count: nat(1),
        };
        match mutant {
            1 => {
                before = f.current(
                    old.clone(),
                    list("Nat", &[nat(8)]),
                    1,
                    list("IRBinding", &[]),
                )
            }
            2 => before = f.after_const(old.clone(), app("IRScalar.ptr_", [nat(1)])),
            3 => input.count = nat(2),
            4 => input.owner = nat(9),
            5 => before.world = world(old.clone(), list("Nat", &[])),
            _ => {}
        }
        let mut scope = Scope::new();
        let proof = dispatch(
            &mut Assembler::new(&mut scope, limits()).unwrap(),
            &site,
            &model,
            &before,
            &input,
            if mutant == 3 { 2 } else { 1 },
        );
        replay(&scope, &[], &proof, mutant == 0);
    }
}

#[test]
fn typed_alloca_source_const_value_and_high_half_bound_are_kernel_checked() {
    for (literal, value, accepted) in [
        (1, 1, true),
        (1, 2, false),
        (1_u64 << 63, 1_u64 << 63, true),
    ] {
        let f = fixture(literal, Ty::I64, 8);
        let reflected = reflect_core_module_v1_with_memory_profile(
            &f.module,
            &[(f.function, 4096)],
            CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
        )
        .unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let before = f.before(memory(rows(), bytes(), 65));
        let mut scope = Scope::new();
        let first = scalar(
            &catalog.fetch(f.coordinate(0)).unwrap(),
            &mut Assembler::new(&mut scope, limits()).unwrap(),
            &model,
            &before,
            app("IRScalar.int_", [nat(value)]),
            truth(before.valid(&model)),
        );
        replay(&scope, &[], first.run().equality(), accepted);
        if literal == 1_u64 << 63 {
            let input = AllocationInput {
                owner: nat(8),
                count: nat(literal),
            };
            let proof = dispatch(
                &mut Assembler::new(&mut scope, limits()).unwrap(),
                &catalog.fetch(f.coordinate(1)).unwrap(),
                &model,
                first.current(),
                &input,
                literal,
            );
            replay(&scope, &[], &proof, false);
        }
    }
}

#[test]
fn typed_alloca_actual_layout_alignment_zero_overflow_and_stale_memory_refute() {
    for (literal, ty, align, cursor, accepted) in [
        (1, Ty::I64, 8, 65, true),
        (1, Ty::I32, 8, 65, false),
        (1, Ty::I64, 16, 65, false),
        (0, Ty::I64, 8, 65, false),
        ((1_u64 << 63) - 1, Ty::I64, 8, 65, false),
        (1, Ty::I64, 8, 0, false),
        (1, Ty::I64, 8, 97, false),
    ] {
        let f = fixture(literal, ty, align);
        let reflected = reflect_core_module_v1_with_memory_profile(
            &f.module,
            &[(f.function, 4096)],
            CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
        )
        .unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let site = catalog.fetch(f.coordinate(1)).unwrap();
        let before = f.after_const(
            memory(rows(), bytes(), cursor),
            app("IRScalar.int_", [nat(literal)]),
        );
        let input = AllocationInput {
            owner: nat(8),
            count: nat(literal),
        };
        // Deliberately retain the baseline eight-byte allocation/cursor. A
        // wrong layout, alignment, extent or CURRENT memory cannot prove it.
        let result = result(rows(), bytes(), 8, 8);
        let checks = site
            .allocation_checks(&model, &before, &input, &result)
            .unwrap();
        replay(
            &Scope::new(),
            &[],
            &conversion(
                constant("IRByteMemoryResultV1"),
                checks.evaluation,
                result.result(),
            ),
            accepted,
        );
    }
}

#[test]
fn typed_alloca_returned_owner_result_kind_and_original_read_id_refute() {
    let f = fixture(1, Ty::I64, 8);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog.fetch(f.coordinate(1)).unwrap();
    let before = f.after_const(memory(rows(), bytes(), 65), app("IRScalar.int_", [nat(1)]));
    let input = AllocationInput {
        owner: nat(8),
        count: nat(1),
    };
    for (owner, pointer, accepted) in [(8, true, true), (9, true, false), (8, false, false)] {
        let mut result = result(rows(), bytes(), owner, 8);
        if !pointer {
            result.value = app("IRScalar.int_", [nat(72)]);
        }
        let checks = site
            .allocation_checks(&model, &before, &input, &result)
            .unwrap();
        let proof = if pointer {
            truth(checks.owners)
        } else {
            truth(checks.result)
        };
        replay(&Scope::new(), &[], &proof, accepted);
    }
    let tail = list("Nat", &[]);
    let checks = site
        .allocation_dispatch_checks(&model, &before, &input, tail)
        .unwrap();
    let (ty, exact_read, value) = checks.count;
    replay(
        &Scope::new(),
        &[],
        &conversion(ty.clone(), exact_read.clone(), value.clone()),
        true,
    );
    // Bind the same value to a different SSA ID. It is not the original
    // count read merely because its bits and nominal type happen to match.
    let foreign = f.current(
        memory(rows(), bytes(), 65),
        list("Nat", &[nat(8)]),
        1,
        list(
            "IRBinding",
            &[binding(f.pointer, app("IRScalar.int_", [nat(1)]))],
        ),
    );
    let checks = site
        .allocation_dispatch_checks(&model, &foreign, &input, list("Nat", &[]))
        .unwrap();
    let (ty, actual, value) = checks.count;
    replay(&Scope::new(), &[], &conversion(ty, actual, value), false);
}

#[test]
fn typed_alloca_foreign_endpoints_wrong_fetched_kind_and_resource_caps_refuse() {
    let f = fixture(1, Ty::I64, 8);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog.fetch(f.coordinate(1)).unwrap();
    let before = f.after_const(memory(rows(), bytes(), 65), app("IRScalar.int_", [nat(1)]));
    let input = AllocationInput {
        owner: nat(8),
        count: nat(1),
    };
    let result = result(rows(), bytes(), 8, 8);
    assert!(
        catalog
            .fetch(f.coordinate(0))
            .unwrap()
            .allocation_checks(&model, &before, &input, &result)
            .is_err()
    );
    assert!(
        catalog
            .fetch(f.coordinate(2))
            .unwrap()
            .allocation_dispatch_checks(&model, &before, &input, list("Nat", &[]))
            .is_err()
    );
    let checks = site
        .allocation_dispatch_checks(&model, &before, &input, list("Nat", &[]))
        .unwrap();
    let (ty, left, right) = checks.owners;
    let owners = conversion(ty, left, right);
    let (ty, left, right) = checks.count;
    let exact_count = conversion(ty, left, right);
    let bound = PendingProof::candidate(
        checks.count_bound,
        app("Nat.le_add_right", [nat(2), nat((1_u64 << 63) - 2)]),
    );
    for mode in 0..3 {
        let mut scope = Scope::new();
        let mut cap = limits();
        if mode == 0 {
            cap.max_operations = 1;
        } else if mode == 1 {
            // Closed dispatch consumes no caller locals; retain this resource
            // refusal at the exact cold forty-operation boundary instead.
            cap.max_operations = 39;
        }
        let mut assembler = Assembler::new(&mut scope, cap).unwrap();
        let count = if mode == 2 {
            conversion(
                constant("IRScalar"),
                app("IRScalar.int_", [nat(1)]),
                app("IRScalar.int_", [nat(1)]),
            )
        } else {
            exact_count.clone()
        };
        assert!(
            site.allocation_dispatch(
                &mut assembler,
                &model,
                &before,
                &input,
                list("Nat", &[]),
                AllocationDispatchPremises {
                    owners: owners.clone(),
                    count,
                    count_bound: bound.clone()
                },
            )
            .is_err()
        );
    }
    let checks = site
        .allocation_checks(&model, &before, &input, &result)
        .unwrap();
    let mut p = concrete_premises(checks, &model, &before, &result);
    // This is a distinct structural refusal: the evaluation endpoint names
    // another current memory. The false same-endpoint allocation claims were
    // independently kernel-refuted above; do not credit this shape refusal.
    let stale = f.after_const(memory(rows(), bytes(), 97), app("IRScalar.int_", [nat(1)]));
    let stale_checks = site
        .allocation_checks(&model, &stale, &input, &result)
        .unwrap();
    p.evaluated = conversion(
        constant("IRByteMemoryResultV1"),
        stale_checks.evaluation,
        result.result(),
    );
    let mut scope = Scope::new();
    assert!(
        site.allocation_value(
            &mut Assembler::new(&mut scope, limits()).unwrap(),
            &model,
            &before,
            input,
            result,
            p
        )
        .is_err()
    );
}

fn typed_reflection(
    f: &Fixture,
    address: u64,
) -> crate::core_reflection::ReflectedCoreModuleV1<'_> {
    reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, address)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap()
}

#[test]
fn typed_alloca_dispatch_actual_none_defaults_to_one_without_reading_unused_ssa() {
    let f = fixture_with_count(7, Ty::I64, 8, false);
    let original = f.module.clone();
    let reflected = typed_reflection(&f, 4096);
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(1))
        .unwrap();
    assert!(matches!(
        f.module.functions[0].blocks[0].body[1].inst,
        Inst::Alloca { count: None, .. }
    ));
    // Dispatch only: this need not be a state reached from the fixture's
    // Const. None must not resolve its unused count ID or require its type.
    let before = f.after_const(memory(rows(), bytes(), 65), app("IRScalar.ptr_", [nat(7)]));
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mut proofs = Vec::new();
    for literal in [1, 2] {
        let input = AllocationInput {
            owner: nat(8),
            count: nat(literal),
        };
        proofs.push(dispatch(
            &mut assembler,
            &site,
            &model,
            &before,
            &input,
            literal,
        ));
    }
    drop(assembler);
    replay_dag(&scope, &[], &proofs[0]);
    replay(&scope, &[], &proofs[1], false);
    assert_eq!(f.module, original);
}

#[test]
fn typed_alloca_dispatch_preserves_nonempty_actual_lexical_owner_tail() {
    let f = fixture(1, Ty::I64, 8);
    let reflected = typed_reflection(&f, 4096);
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(1))
        .unwrap();
    let mut before = f.after_const(memory(rows(), bytes(), 65), app("IRScalar.int_", [nat(1)]));
    before.world = world(memory(rows(), bytes(), 65), list("Nat", &[nat(8), nat(7)]));
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mut proofs = Vec::new();
    for (owner, tail) in [
        (8, list("Nat", &[nat(7)])),
        (8, list("Nat", &[])),
        (7, list("Nat", &[nat(8)])),
    ] {
        let input = AllocationInput {
            owner: nat(owner),
            count: nat(1),
        };
        proofs.push(dispatch_with_tail(
            &mut assembler,
            &site,
            &model,
            &before,
            &input,
            1,
            tail,
        ));
    }
    drop(assembler);
    // This checks exact dispatch, not owner-stack validity or access rights.
    replay_dag(&scope, &[], &proofs[0]);
    for proof in &proofs[1..] {
        replay(&scope, &[], proof, false);
    }
}

#[test]
fn typed_alloca_dispatch_closed_cache_reuses_changed_context_count_and_nat_bool_worlds() {
    let fixtures = [fixture(1, Ty::I64, 8), fixture(2, Ty::U32, 4)];
    let originals = fixtures.each_ref().map(|f| f.module.clone());
    let reflected = [
        typed_reflection(&fixtures[0], 4096),
        typed_reflection(&fixtures[1], 8192),
    ];
    assert_ne!(reflected[0].context_term(), reflected[1].context_term());
    let mut scope = Scope::new();
    let arbitrary_bytes = scope
        .try_local(Expr::pi(
            BinderInfo::Default,
            constant("Nat"),
            app("IROption", [constant("Nat")]),
        ))
        .unwrap();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mut proofs = Vec::new();
    let mut cached: Option<Expr> = None;
    for (index, (world_type, host, literal, owner, tail)) in [
        (constant("Nat"), nat(37), 1, 8, list("Nat", &[])),
        (
            constant("Bool"),
            constant("Bool.true"),
            2,
            7,
            list("Nat", &[nat(6)]),
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let f = &fixtures[index];
        let model = MachineModel::new(
            world_type.clone(),
            &reflected[index],
            providers_for(world_type.clone()),
        );
        let site = Catalog::new(environment(), &reflected[index], limits())
            .unwrap()
            .fetch(f.coordinate(1))
            .unwrap();
        let mut before = f.after_const(
            memory(
                rows(),
                arbitrary_bytes.term().clone(),
                65 + index as u64 * 32,
            ),
            app("IRScalar.int_", [nat(literal)]),
        );
        let owners = app("IRList.cons", [constant("Nat"), nat(owner), tail.clone()]);
        before.world = app(
            "IRByteWorldV1.mk",
            [
                world_type,
                memory(
                    rows(),
                    arbitrary_bytes.term().clone(),
                    65 + index as u64 * 32,
                ),
                host,
                owners,
                nat(9),
            ],
        );
        let input = AllocationInput {
            owner: nat(owner),
            count: nat(literal),
        };
        let locals_before = assembler.locals;
        let operations_before = assembler.operations;
        proofs.push(dispatch_with_tail(
            &mut assembler,
            &site,
            &model,
            &before,
            &input,
            literal,
            tail,
        ));
        let actual = assembler.allocation_dispatch_candidate.as_ref().unwrap();
        assert!(
            !actual.has_fvar_quick(),
            "the reusable template is closed, not a captured world/context"
        );
        if let Some(cached) = &cached {
            assert_eq!(actual, cached);
            // Expr owns its outer kind inline; cloning that shell is not a
            // cache miss. Its lambda children are the shared Arc-backed DAG.
            let (
                ExprKind::Lam(_, actual_ty, actual_body),
                ExprKind::Lam(_, cached_ty, cached_body),
            ) = (actual.kind(), cached.kind())
            else {
                panic!("the closed dispatch template must be a lambda");
            };
            assert!(
                std::sync::Arc::ptr_eq(actual_ty, cached_ty)
                    && std::sync::Arc::ptr_eq(actual_body, cached_body),
                "the same cached template DAG is reused"
            );
            assert_eq!(
                assembler.locals, locals_before,
                "cache reuse creates no new locals"
            );
            assert_eq!(
                assembler.operations,
                operations_before + 1,
                "cache reuse charges only the actual dispatch operation"
            );
        } else {
            cached = Some(actual.clone());
        }
    }
    drop(assembler);
    for proof in &proofs {
        replay_dag(&scope, std::slice::from_ref(&arbitrary_bytes), proof);
    }
    for (f, original) in fixtures.iter().zip(originals) {
        assert_eq!(f.module, original);
    }
}
