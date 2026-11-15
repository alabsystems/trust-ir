// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Real validated modules, reflection and fetched transfers in the canonical
//! byte environment. No replacement instructions/evaluator, custom axioms or
//! assumed load result. These are model tests, not native/performance evidence.

use super::*;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{Endianness, Module, StructPassingPolicy, TargetInfo, Ty};

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}
fn checker() -> TypeChecker<'static> {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
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
fn replay(scope: &Scope, proof: &PendingEquality, accepted: bool) {
    let term = scope.close(proof.term()).unwrap();
    let claim = scope.close(&proof.proposition()).unwrap();
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let checker = checker();
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .expect("claim must itself typecheck");
    if accepted {
        checker.check_type(&term, &claim).unwrap();
        let audit = environment().audit_certification(&claim, &term);
        assert!(audit.is_certified(), "{audit:#?}");
    } else {
        let error = checker.check_type(&term, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "{error:?}"
        );
    }
}
fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(&ty, right))
}
fn truth(left: Expr) -> PendingEquality {
    conversion(constant("Bool"), left, constant("Bool.true"))
}
fn bounded(word: Expr, literal: u64) -> PendingProof {
    PendingProof::candidate(
        app("Nat.lt", [word.clone(), limit()]),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [word]), nat(u64::MAX - literal)],
        ),
    )
}
fn providers() -> Expr {
    // Total, unused import provider. No provider assertion is involved here.
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
fn memory(kind: usize) -> Expr {
    let allocation = |base, size, owner, live| {
        app(
            "IRByteAllocationV1.mk",
            [
                nat(base),
                nat(size),
                nat(owner),
                constant(if live { "Bool.true" } else { "Bool.false" }),
            ],
        )
    };
    let mut rows = vec![
        allocation(16, 16, 8, true),
        allocation(80, if kind == 2 { 7 } else { 16 }, 0, kind != 1),
        allocation(128, 8, 7, false),
    ];
    if kind == 3 {
        rows.push(allocation(80, 16, 0, true));
    }
    app(
        "IRByteMemoryV1.mk",
        [
            list("IRByteAllocationV1", &rows),
            Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(173))),
            // Deliberately NOT above existing records: no hidden freshness theorem.
            nat(1),
        ],
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
fn current_memory(current: &Current) -> Expr {
    app(
        "ir_byte_world_memory_v1",
        [constant("Nat"), current.world.clone()],
    )
}

struct Fixture {
    module: Module,
    function: FuncId,
    block: BlockId,
    pointer: ValueId,
    offset: ValueId,
    value: ValueId,
    alternate: ValueId,
    result: ValueId,
    loaded: ValueId,
}
fn fixture(
    pointee: Ty,
    index: Ty,
    word: Ty,
    inbounds: bool,
    align: u64,
    volatile: bool,
    alternate: bool,
) -> Fixture {
    let mut builder = ModuleBuilder::new_with_target_info(
        "memory_access_replay",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(
        vec![Ty::Ptr, index.clone(), word.clone(), Ty::Ptr],
        vec![word.clone()],
    );
    let function = builder.declare_function("scratch", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let pointer = body.add_block_param(block, Ty::Ptr);
    let offset = body.add_block_param(block, index);
    let value = body.add_block_param(block, word.clone());
    let other = body.add_block_param(block, Ty::Ptr);
    body.switch_to_block(block);
    let result = if inbounds {
        body.gep_inbounds(pointee, pointer, vec![offset])
    } else {
        body.gep(pointee, pointer, vec![offset])
    };
    let destination = if alternate { other } else { result };
    if volatile {
        body.store_volatile(word.clone(), destination, value);
    } else {
        body.store_aligned(word.clone(), destination, value, align);
    }
    let loaded = body.load_aligned(word, destination, align);
    body.ret(vec![loaded]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(
        crate::validate_module(&module).is_empty(),
        "fixture must be an actual valid module"
    );
    Fixture {
        module,
        function,
        block,
        pointer,
        offset,
        value,
        alternate: other,
        result,
        loaded,
    }
}
fn ordinary() -> Fixture {
    fixture(Ty::I8, Ty::I64, Ty::I64, false, 8, false, false)
}
impl Fixture {
    fn coordinate(&self, instruction: usize) -> Coordinate {
        Coordinate {
            function: self.function,
            block: self.block,
            instruction,
        }
    }
    fn current(&self, base: u64, offset: u64, word: Expr, memory: Expr, pc: u64) -> Current {
        let binding = |id: ValueId, value| app("IRBinding.mk", [nat(u64::from(id.index())), value]);
        let mut bindings = vec![
            binding(self.pointer, app("IRScalar.ptr_", [nat(base)])),
            binding(self.offset, scalar(nat(offset))),
            binding(self.value, scalar(word)),
            binding(self.alternate, app("IRScalar.ptr_", [nat(128)])),
        ];
        if pc != 0 {
            bindings.insert(
                0,
                binding(
                    self.result,
                    app("IRScalar.ptr_", [nat(base.wrapping_add(offset))]),
                ),
            );
        }
        Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(u64::from(self.function.index())),
                    nat(u64::from(self.block.index())),
                    nat(pc),
                    list("IRBinding", &bindings),
                    list("Nat", &[]),
                ],
            ),
            tail: list("IRFrame", &[]),
            legacy_memory: list("IRMemSlot", &[]),
            legacy_cursor: nat(0),
            world: world(memory),
        }
    }
    fn expected(
        &self,
        before: &Current,
        pc: u64,
        new_memory: Expr,
        binding: Option<(ValueId, Expr)>,
    ) -> Current {
        let fields = before.frame.get_app_args();
        let mut bindings = fields[3].clone();
        if let Some((id, value)) = binding {
            bindings = app(
                "IRList.cons",
                [
                    constant("IRBinding"),
                    app("IRBinding.mk", [nat(u64::from(id.index())), value]),
                    bindings,
                ],
            );
        }
        Current {
            frame: app(
                "IRFrame.mk",
                [
                    fields[0].clone(),
                    fields[1].clone(),
                    nat(pc),
                    bindings,
                    fields[4].clone(),
                ],
            ),
            world: world(new_memory),
            ..before.clone()
        }
    }
}
fn gep(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    f: &Fixture,
    before: &Current,
    base: u64,
    offset: u64,
) -> ByteGepI8Result {
    gep_with_membership(assembler, model, f, before, base, offset, None).unwrap()
}

fn gep_with_membership(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    f: &Fixture,
    before: &Current,
    base: u64,
    offset: u64,
    membership: Option<PendingEquality>,
) -> Result<ByteGepI8Result> {
    let read = |id: ValueId| app("ir_getd", [before.machine(), nat(u64::from(id.index()))]);
    let input = ByteGepI8 {
        pointer: read(f.pointer),
        indices: app(
            "ir_resolve",
            [
                before.machine(),
                list("Nat", &[nat(u64::from(f.offset.index()))]),
            ],
        ),
        base: nat(base),
        offset: nat(offset),
        memory: current_memory(before),
    };
    let positive = PendingProof::candidate(
        app("Nat.lt", [nat(0), nat(base)]),
        app("Nat.zero_lt_succ", [nat(base.saturating_sub(1))]),
    );
    let index_bound = PendingProof::candidate(
        app("Nat.lt", [nat(offset), nat(1_u64 << 63)]),
        app(
            "Nat.le_add_right",
            [
                app("Nat.succ", [nat(offset)]),
                nat((1_u64 << 63).saturating_sub(offset.saturating_add(1))),
            ],
        ),
    );
    let result_bound = PendingProof::candidate(
        app("Nat.lt", [input.address(), limit()]),
        bounded(nat(base.wrapping_add(offset)), base.wrapping_add(offset)).term,
    );
    let equations = input.premise_equalities(model.context());
    let premises = ByteGepI8Premises {
        layout: conversion(
            equations[0].0.clone(),
            equations[0].1.clone(),
            equations[0].2.clone(),
        ),
        pointer: conversion(
            equations[1].0.clone(),
            equations[1].1.clone(),
            equations[1].2.clone(),
        ),
        indices: conversion(
            equations[2].0.clone(),
            equations[2].1.clone(),
            equations[2].2.clone(),
        ),
        positive,
        index_bound,
        result_bound,
    };
    match membership {
        Some(proof) => {
            assembler.byte_gep_i8_inbounds(model.context().clone(), input, premises, proof)
        }
        None => assembler.byte_gep_i8_noninbounds(model.context().clone(), input, premises),
    }
}

#[test]
fn memory_access_inbounds_fetched_gep_replays_and_refuses_forged_membership() {
    let f = fixture(Ty::I8, Ty::I64, Ty::I32, true, 4, false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(0))
        .unwrap();
    // Interior and one-past both form pointers; no dereference claim follows.
    for (kind, base, offset, accepted) in [
        (0, 80, 0, true),
        (0, 80, 8, true),
        (0, 80, 16, true),
        (0, 80, 17, false),
        (1, 80, 8, false),
        (0, 40, 0, false),
        (0, 16, 64, false),
    ] {
        let before = f.current(base, offset, nat(7), memory(kind), 0);
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let membership = truth(app(
            "ir_byte_same_allocation_v1",
            [
                allocs(current_memory(&before)),
                nat(base),
                app("Nat.add", [nat(base), nat(offset)]),
            ],
        ));
        let result = gep_with_membership(
            &mut assembler,
            &model,
            &f,
            &before,
            base,
            offset,
            Some(membership.clone()),
        )
        .unwrap();
        let locals = assembler.locals;
        assert!(
            assembler.byte_gep_i8_candidate.is_none(),
            "inbounds constructed unused noninbounds helper"
        );
        let again = gep_with_membership(
            &mut assembler,
            &model,
            &f,
            &before,
            base,
            offset,
            Some(membership),
        )
        .unwrap();
        assert_eq!(
            assembler.locals, locals,
            "inbounds cache hit rebuilt binders"
        );
        assert_eq!(again.evaluated.term(), result.evaluated.term());
        assert!(
            !assembler
                .byte_gep_i8_inbounds_candidate
                .as_ref()
                .unwrap()
                .has_fvar_quick()
        );
        let first = transfer(
            &mut assembler,
            &model,
            &site,
            &before,
            result.result,
            result.evaluated,
            result.allocations,
        );
        drop(assembler);
        replay(&scope, first.step(), accepted);
        if accepted {
            let term = scope.close(first.step().term()).unwrap();
            let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
            let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
            checker()
                .check_type(&decoded, &scope.close(&first.step().proposition()).unwrap())
                .unwrap();
        }
    }
}

#[test]
fn memory_access_inbounds_rejects_wrong_memory_endpoints_flag_and_proof() {
    let f = fixture(Ty::I8, Ty::I64, Ty::I32, true, 4, false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(0))
        .unwrap();
    let before = f.current(80, 8, nat(7), memory(0), 0);
    let membership = app(
        "ir_byte_same_allocation_v1",
        [
            allocs(current_memory(&before)),
            nat(80),
            app("Nat.add", [nat(80), nat(8)]),
        ],
    );
    for wrong in [
        app(
            "ir_byte_same_allocation_v1",
            [allocs(memory(1)), nat(80), nat(88)],
        ),
        app(
            "ir_byte_same_allocation_v1",
            [allocs(current_memory(&before)), nat(16), nat(24)],
        ),
    ] {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        assert!(
            gep_with_membership(&mut a, &model, &f, &before, 80, 8, Some(truth(wrong))).is_err()
        );
    }
    for wrong_flag in [false, true] {
        let before = if wrong_flag {
            f.current(80, 8, nat(7), memory(1), 0)
        } else {
            before.clone()
        };
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let result = if wrong_flag {
            gep(&mut a, &model, &f, &before, 80, 8)
        } else {
            gep_with_membership(
                &mut a,
                &model,
                &f,
                &before,
                80,
                8,
                Some(PendingEquality::candidate(
                    constant("Bool"),
                    membership.clone(),
                    constant("Bool.true"),
                    constant("True.intro"),
                )),
            )
            .unwrap()
        };
        let step = transfer(
            &mut a,
            &model,
            &site,
            &before,
            result.result,
            result.evaluated,
            result.allocations,
        );
        drop(a);
        replay(&scope, step.step(), false);
    }
}
fn store(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    f: &Fixture,
    before: &Current,
    address: u64,
    word: Expr,
    literal: u64,
    requested_align: u64,
) -> ByteStoreEightResult {
    let ty = app("IRTy.int_", [nat(64)]);
    let found = conversion(
        option("IRByteLayoutV1"),
        app("ir_byte_layout_v1", [model.context().clone(), ty.clone()]),
        some("IRByteLayoutV1", layout(ty, 8)),
    );
    let codec = assembler
        .byte_i64_codec(
            model.context().clone(),
            word.clone(),
            found,
            bounded(word, literal),
        )
        .unwrap();
    let input = ByteStoreEight {
        pointer: app(
            "ir_getd",
            [before.machine(), nat(u64::from(f.result.index()))],
        ),
        address: nat(address),
        requested_align: nat(requested_align),
        memory: current_memory(before),
    };
    let pointer = conversion(
        option("Nat"),
        pointer_address(input.pointer.clone()),
        some("Nat", nat(address)),
    );
    let accessible = truth(app(
        "ir_byte_accessible_v1",
        [
            allocs(input.memory.clone()),
            nat(address),
            nat(8),
            app(
                "ir_byte_effective_align_v1",
                [
                    nat(requested_align),
                    app("ir_byte_layout_align_v1", [codec.layout.clone()]),
                ],
            ),
        ],
    ));
    assembler
        .byte_store_eight(
            &codec,
            input,
            ByteStoreEightPremises {
                pointer,
                accessible,
            },
        )
        .unwrap()
}
fn transfer(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    site: &FetchedSite,
    before: &Current,
    result: MemoryResult,
    evaluated: PendingEquality,
    allocations: PendingEquality,
) -> MemoryTransfer {
    let checks = site.memory_checks(model, before, &result).unwrap();
    let bridge = assembler
        .conversion(
            constant("IRByteMemoryResultV1"),
            checks.evaluation,
            evaluated.left.clone(),
        )
        .unwrap();
    let evaluated = assembler.compose(bridge, evaluated).unwrap();
    site.memory_value(
        assembler,
        model,
        before,
        result,
        MemoryPremises {
            evaluated,
            allocations,
            result: truth(checks.result),
            before: truth(before.valid(model)),
        },
    )
    .unwrap()
}

#[test]
fn memory_access_fetched_gep_store_and_load_replay_existing_memory_and_canonical_words() {
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let gep_site = catalog.fetch(f.coordinate(0)).unwrap();
    let store_site = catalog.fetch(f.coordinate(1)).unwrap();
    let load_site = catalog.fetch(f.coordinate(2)).unwrap();
    for (offset, word) in [(0, 0), (8, 1_u64 << 63), (8, u64::MAX)] {
        let before = f.current(80, offset, nat(word), memory(0), 0);
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let gep = gep(&mut assembler, &model, &f, &before, 80, offset);
        let gep_fit = gep.result_fits.clone();
        let first = transfer(
            &mut assembler,
            &model,
            &gep_site,
            &before,
            gep.result,
            gep.evaluated,
            gep.allocations,
        );
        let stored = store(
            &mut assembler,
            &model,
            &f,
            first.current(),
            80 + offset,
            nat(word),
            word,
            8,
        );
        let second = transfer(
            &mut assembler,
            &model,
            &store_site,
            first.current(),
            stored.result.clone(),
            stored.evaluated.clone(),
            stored.allocations.clone(),
        );
        let loaded = MemoryResult {
            value: scalar(nat(word)),
            memory: stored.result.memory.clone(),
        };
        let (codec, _, _) = load_fixture(
            model.context().clone(),
            app("IRTy.int_", [nat(64)]),
            scalar(nat(word)),
            word,
        );
        let pointer = app(
            "ir_getd",
            [second.current().machine(), nat(u64::from(f.result.index()))],
        );
        let address = nat(80 + offset);
        let loaded_candidate = assembler
            .byte_load_eight(
                &codec,
                ByteLoadEight {
                    pointer: pointer.clone(),
                    address: address.clone(),
                    requested_align: nat(8),
                    memory: loaded.memory.clone(),
                },
                ByteLoadEightPremises {
                    pointer: conversion(
                        option("Nat"),
                        pointer_address(pointer),
                        some("Nat", address.clone()),
                    ),
                    accessible: truth(app(
                        "ir_byte_accessible_v1",
                        [
                            allocs(loaded.memory.clone()),
                            address,
                            nat(8),
                            app(
                                "ir_byte_effective_align_v1",
                                [
                                    nat(8),
                                    app("ir_byte_layout_align_v1", [codec.layout.clone()]),
                                ],
                            ),
                        ],
                    )),
                    initialized: stored.raw_read.clone(),
                },
            )
            .unwrap();
        let load_allocs = assembler
            .conversion(
                app("IRList", [constant("IRByteAllocationV1")]),
                allocs(loaded.memory.clone()),
                allocs(current_memory(second.current())),
            )
            .unwrap();
        let third = transfer(
            &mut assembler,
            &model,
            &load_site,
            second.current(),
            loaded,
            loaded_candidate,
            load_allocs,
        );
        drop(assembler);
        replay(&scope, &gep_fit, true);
        replay(&scope, first.step(), true);
        replay(&scope, second.run().equality(), true);
        replay(&scope, third.step(), true);
        for equality in [
            &stored.raw_read,
            &stored.typed_readback,
            &stored.allocations,
            &stored.cursor,
            third.valid(),
        ] {
            replay(&scope, equality, true);
        }
        let expected = f.expected(
            &before,
            1,
            memory(0),
            Some((f.result, app("IRScalar.ptr_", [nat(80 + offset)]))),
        );
        replay(
            &scope,
            &PendingEquality::candidate(
                model.config_type(),
                model.step(before.running(&model)),
                expected.running(&model),
                first.step().term().clone(),
            ),
            true,
        );
        let expected_store = f.expected(&expected, 2, stored.result.memory.clone(), None);
        replay(
            &scope,
            &PendingEquality::candidate(
                model.config_type(),
                model.step(expected.running(&model)),
                expected_store.running(&model),
                second.step().term().clone(),
            ),
            true,
        );
        let expected_load = f.expected(
            &expected_store,
            3,
            stored.result.memory.clone(),
            Some((f.loaded, scalar(nat(word)))),
        );
        replay(
            &scope,
            &PendingEquality::candidate(
                model.config_type(),
                model.step(expected_store.running(&model)),
                expected_load.running(&model),
                third.step().term().clone(),
            ),
            true,
        );
    }
}

#[test]
fn memory_access_cached_gep_reuses_closed_helper_for_changed_actual_inputs() {
    let first = ordinary();
    let second = fixture(Ty::I8, Ty::I64, Ty::I32, false, 4, false, false);
    let first_reflected = reflect_core_module_v1(&first.module, &[(first.function, 4096)]).unwrap();
    let second_reflected =
        reflect_core_module_v1(&second.module, &[(second.function, 8192)]).unwrap();
    let first_model = MachineModel::new(constant("Nat"), &first_reflected, providers());
    let second_model = MachineModel::new(constant("Nat"), &second_reflected, providers());
    assert_ne!(first_model.context(), second_model.context());
    let first_site = Catalog::new(environment(), &first_reflected, limits())
        .unwrap()
        .fetch(first.coordinate(0))
        .unwrap();
    let second_site = Catalog::new(environment(), &second_reflected, limits())
        .unwrap()
        .fetch(second.coordinate(0))
        .unwrap();
    let first_memory = memory(0);
    let second_memory = app(
        "IRByteMemoryV1.mk",
        [
            allocs(memory(1)),
            Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(29))),
            nat(3),
        ],
    );
    let first_before = first.current(80, 0, nat(7), first_memory.clone(), 0);
    // This GEP is outside every allocation; neither changed allocation liveness
    // nor the changed byte map/cursor grants or needs an accessibility premise.
    let second_before = second.current(200, 16, nat(19), second_memory.clone(), 0);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    assert!(assembler.byte_gep_i8_candidate.is_none());
    let first_candidate = gep(&mut assembler, &first_model, &first, &first_before, 80, 0);
    let cached = assembler.byte_gep_i8_candidate.clone().unwrap();
    assert!(!cached.has_fvar_quick());
    let helper_locals = assembler.locals;
    let second_candidate = gep(
        &mut assembler,
        &second_model,
        &second,
        &second_before,
        200,
        16,
    );
    assert_eq!(
        assembler.locals, helper_locals,
        "cache hit must not rebuild binders"
    );
    assert_eq!(assembler.byte_gep_i8_candidate.as_ref(), Some(&cached));
    assert_eq!(second_candidate.evaluated.term().get_app_fn(), &cached);
    let applied = second_candidate.evaluated.term().get_app_args();
    assert_eq!(applied.len(), 12);
    assert_eq!(applied[0], second_model.context());
    assert_eq!(
        applied[1],
        &app(
            "ir_getd",
            [
                second_before.machine(),
                nat(u64::from(second.pointer.index()))
            ],
        )
    );
    assert_eq!(
        applied[2],
        &app(
            "ir_resolve",
            [
                second_before.machine(),
                list("Nat", &[nat(u64::from(second.offset.index()))]),
            ],
        )
    );
    assert_eq!(applied[3], &nat(200));
    assert_eq!(applied[4], &nat(16));
    assert_eq!(applied[5], &current_memory(&second_before));
    drop(applied);
    let first_step = transfer(
        &mut assembler,
        &first_model,
        &first_site,
        &first_before,
        first_candidate.result,
        first_candidate.evaluated,
        first_candidate.allocations,
    );
    let second_step = transfer(
        &mut assembler,
        &second_model,
        &second_site,
        &second_before,
        second_candidate.result,
        second_candidate.evaluated,
        second_candidate.allocations,
    );
    drop(assembler);
    for (f, model, before, step, address, unchanged_memory) in [
        (
            &first,
            &first_model,
            &first_before,
            &first_step,
            80,
            first_memory,
        ),
        (
            &second,
            &second_model,
            &second_before,
            &second_step,
            216,
            second_memory,
        ),
    ] {
        let expected = f.expected(
            before,
            1,
            unchanged_memory,
            Some((f.result, app("IRScalar.ptr_", [nat(address)]))),
        );
        replay(
            &scope,
            &PendingEquality::candidate(
                model.config_type(),
                model.step(before.running(model)),
                expected.running(model),
                step.step().term().clone(),
            ),
            true,
        );
        replay(&scope, step.valid(), true);
    }
}

#[test]
fn memory_access_noninbounds_gep_needs_no_allocation_containing_pointer() {
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(0))
        .unwrap();
    let before = f.current(200, 8, nat(0), memory(0), 0);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let result = gep(&mut assembler, &model, &f, &before, 200, 8);
    let step = transfer(
        &mut assembler,
        &model,
        &site,
        &before,
        result.result,
        result.evaluated,
        result.allocations,
    );
    drop(assembler);
    replay(&scope, step.step(), true);
    replay(&scope, step.valid(), true);
}

#[test]
fn memory_access_fetched_gep_refuses_zero_overflow_and_noncanonical_signed_index() {
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(0))
        .unwrap();
    for (base, offset) in [(0, 0), (u64::MAX, 1), (80, 1_u64 << 63)] {
        let before = f.current(base, offset, nat(0), memory(0), 0);
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let candidate = gep(&mut assembler, &model, &f, &before, base, offset);
        let step = transfer(
            &mut assembler,
            &model,
            &site,
            &before,
            candidate.result,
            candidate.evaluated,
            candidate.allocations,
        );
        drop(assembler);
        replay(&scope, step.step(), false);
    }
}

#[test]
fn memory_access_fetched_gep_does_not_replace_actual_type_flag_or_operands() {
    for (pointee, inbounds, base, actual_offset, claimed_offset) in [
        (Ty::I64, false, 80, 8, 8),
        (Ty::I8, true, 200, 8, 8),
        (Ty::I8, false, 80, 8, 0),
    ] {
        let f = fixture(pointee, Ty::I64, Ty::I64, inbounds, 8, false, false);
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let site = Catalog::new(environment(), &reflected, limits())
            .unwrap()
            .fetch(f.coordinate(0))
            .unwrap();
        let before = f.current(base, actual_offset, nat(0), memory(0), 0);
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let candidate = gep(&mut assembler, &model, &f, &before, base, claimed_offset);
        let step = transfer(
            &mut assembler,
            &model,
            &site,
            &before,
            candidate.result,
            candidate.evaluated,
            candidate.allocations,
        );
        drop(assembler);
        replay(&scope, step.step(), false);
    }
    let unsigned = fixture(Ty::I8, Ty::U64, Ty::I64, false, 8, false, false);
    assert!(
        reflect_core_module_v1(&unsigned.module, &[(unsigned.function, 4096)]).is_err(),
        "erased carriers must not grant signed-index reflection authority"
    );
}

#[test]
fn memory_access_store_refuses_dead_short_overlapping_and_misaligned_ranges() {
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(1))
        .unwrap();
    for (kind, address) in [(1, 80), (2, 80), (3, 80), (0, 81)] {
        let before = f.current(address, 0, nat(7), memory(kind), 1);
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let candidate = store(&mut assembler, &model, &f, &before, address, nat(7), 7, 8);
        let step = transfer(
            &mut assembler,
            &model,
            &site,
            &before,
            candidate.result,
            candidate.evaluated,
            candidate.allocations,
        );
        drop(assembler);
        replay(&scope, step.step(), false);
    }
}

#[test]
fn memory_access_volatile_store_is_refused_at_actual_module_reflection() {
    let f = fixture(Ty::I8, Ty::I64, Ty::I64, false, 8, true, false);
    // The fixture is validated by fixture(); this is the real reflector's
    // explicit profile refusal, not a fetched kernel execution failure.
    let error = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap_err();
    assert_eq!(
        error.to_string(),
        "volatile memory operations have no Core byte profile semantics"
    );
}

#[test]
fn memory_access_store_checks_actual_alignment_type_ssa_and_value() {
    for (ty, align, alternate, actual_word, claimed_word) in [
        (Ty::I64, 16, false, 7, 7),
        (Ty::I32, 8, false, 7, 7),
        (Ty::I64, 8, true, 7, 7),
        (Ty::I64, 8, false, 9, 7),
    ] {
        let f = fixture(Ty::I8, Ty::I64, ty, false, align, false, alternate);
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let site = Catalog::new(environment(), &reflected, limits())
            .unwrap()
            .fetch(f.coordinate(1))
            .unwrap();
        let before = f.current(80, 8, nat(actual_word), memory(0), 1);
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let candidate = store(
            &mut assembler,
            &model,
            &f,
            &before,
            88,
            nat(claimed_word),
            claimed_word,
            8,
        );
        let step = transfer(
            &mut assembler,
            &model,
            &site,
            &before,
            candidate.result,
            candidate.evaluated,
            candidate.allocations,
        );
        drop(assembler);
        replay(&scope, step.step(), false);
    }
}

#[test]
fn memory_access_store_rejects_noncanonical_word_and_forged_same_endpoint_proof() {
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(1))
        .unwrap();
    for forge_term in [false, true] {
        let word = if forge_term { nat(7) } else { limit() };
        let before = f.current(80, 0, word.clone(), memory(0), 1);
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let mut candidate = store(&mut assembler, &model, &f, &before, 80, word, 7, 8);
        if forge_term {
            candidate.evaluated.term = refl(&constant("Bool"), constant("Bool.true"));
        }
        let step = transfer(
            &mut assembler,
            &model,
            &site,
            &before,
            candidate.result,
            candidate.evaluated,
            candidate.allocations,
        );
        drop(assembler);
        replay(&scope, step.step(), false);
    }
}

#[test]
fn memory_access_store_final_memory_frames_existing_disjoint_bytes() {
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(1))
        .unwrap();
    let before = f.current(80, 0, nat(7), memory(0), 1);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let candidate = store(&mut assembler, &model, &f, &before, 80, nat(7), 7, 8);
    let step = transfer(
        &mut assembler,
        &model,
        &site,
        &before,
        candidate.result.clone(),
        candidate.evaluated,
        candidate.allocations,
    );
    let old_bytes = bytes(current_memory(&before));
    let framed = PendingEquality::candidate(
        option("Nat"),
        Expr::app(bytes(candidate.result.memory.clone()), nat(128)),
        Expr::app(old_bytes.clone(), nat(128)),
        app(
            "ir_byte_write_outside_v1",
            [
                old_bytes,
                nat(80),
                nat(8),
                nat(7),
                nat(128),
                refl(&constant("Bool"), constant("Bool.false")),
            ],
        ),
    );
    drop(assembler);
    replay(&scope, step.step(), true);
    replay(&scope, &candidate.raw_read, true);
    replay(&scope, &candidate.typed_readback, true);
    replay(&scope, &framed, true);
    // A live write neither changes the retired sentinel nor makes it readable.
    let forbidden = conversion(
        constant("IRByteMemoryResultV1"),
        app(
            "ir_byte_load_v1",
            [
                model.context().clone(),
                app("IRTy.int_", [nat(64)]),
                app("IRScalar.ptr_", [nat(128)]),
                nat(8),
                constant("Bool.false"),
                candidate.result.memory.clone(),
            ],
        ),
        MemoryResult {
            value: scalar(nat(0)),
            memory: candidate.result.memory,
        }
        .result(),
    );
    replay(&scope, &forbidden, false);
}

#[test]
fn memory_access_fetched_store_rejects_stale_final_memory_with_valid_old_proof() {
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(1))
        .unwrap();
    let before = f.current(80, 0, nat(7), memory(0), 1);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let stored = store(&mut assembler, &model, &f, &before, 80, nat(7), 7, 8);
    let step = transfer(
        &mut assembler,
        &model,
        &site,
        &before,
        stored.result.clone(),
        stored.evaluated,
        stored.allocations,
    );
    drop(assembler);
    // Establish that this is a successful, non-no-op write before reusing its
    // exact proof against a changed endpoint. The correct PC and bindings stay.
    replay(&scope, step.step(), true);
    replay(&scope, &stored.raw_read, true);
    replay(
        &scope,
        &conversion(
            option("Nat"),
            Expr::app(bytes(current_memory(&before)), nat(80)),
            some("Nat", nat(173)),
        ),
        true,
    );
    replay(
        &scope,
        &conversion(
            option("Nat"),
            Expr::app(bytes(stored.result.memory), nat(80)),
            some("Nat", nat(7)),
        ),
        true,
    );
    let stale_after = f.expected(&before, 2, current_memory(&before), None);
    replay(
        &scope,
        &PendingEquality::candidate(
            model.config_type(),
            model.step(before.running(&model)),
            stale_after.running(&model),
            step.step().term().clone(),
        ),
        false,
    );
}

#[test]
fn memory_access_transfer_refuses_wrong_pc_duplicate_bindings_and_stale_world() {
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(0))
        .unwrap();
    let before = f.current(80, 8, nat(7), memory(0), 0);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let candidate = gep(&mut assembler, &model, &f, &before, 80, 8);
    let step = transfer(
        &mut assembler,
        &model,
        &site,
        &before,
        candidate.result,
        candidate.evaluated,
        candidate.allocations,
    );
    drop(assembler);
    let expected = f.expected(
        &before,
        1,
        memory(0),
        Some((f.result, app("IRScalar.ptr_", [nat(88)]))),
    );
    for changed in [
        f.expected(
            &before,
            2,
            memory(0),
            Some((f.result, app("IRScalar.ptr_", [nat(88)]))),
        ),
        f.expected(
            &expected,
            1,
            memory(0),
            Some((f.result, app("IRScalar.ptr_", [nat(88)]))),
        ),
        f.expected(
            &before,
            1,
            memory(1),
            Some((f.result, app("IRScalar.ptr_", [nat(88)]))),
        ),
    ] {
        replay(
            &scope,
            &PendingEquality::candidate(
                model.config_type(),
                model.step(before.running(&model)),
                changed.running(&model),
                step.step().term().clone(),
            ),
            false,
        );
    }
}

#[test]
fn memory_access_codec_endpoint_and_construction_limits_remain_fail_closed() {
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let ty = app("IRTy.int_", [nat(64)]);
    let found = conversion(
        option("IRByteLayoutV1"),
        app("ir_byte_layout_v1", [model.context().clone(), ty.clone()]),
        some("IRByteLayoutV1", layout(ty.clone(), 8)),
    );
    let mut codec = assembler
        .byte_i64_codec(model.context().clone(), nat(7), found, bounded(nat(7), 7))
        .unwrap();
    codec.ty = app("IRTy.uint_", [nat(64)]);
    assert!(
        codec.validate().is_err(),
        "a layout/value theorem does not change type identity"
    );
    drop(assembler);
    let mut policy = limits();
    policy.max_operations = 1;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    assembler.local(constant("Nat")).unwrap();
    assert!(
        assembler
            .byte_i64_codec(
                model.context().clone(),
                nat(7),
                codec.layout_found,
                bounded(nat(7), 7)
            )
            .is_err()
    );
}

#[test]
fn memory_access_noninbounds_retained_pre_refactor_dag_bytes_are_unchanged() {
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let before = f.current(80, 8, nat(7), memory(0), 0);
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let result = gep(&mut a, &model, &f, &before, 80, 8);
    drop(a);
    let term = scope.close(result.evaluated.term()).unwrap();
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let baseline = include_bytes!("testdata/noninbounds-gep.dag-v2.bin");
    assert_eq!(bytes.as_slice(), baseline);
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(baseline).unwrap();
    checker()
        .check_type(
            &decoded,
            &scope.close(&result.evaluated.proposition()).unwrap(),
        )
        .unwrap();
}

#[test]
fn memory_access_store_readback_retained_pre_refactor_bytes() {
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let before = f.current(80, 8, nat(7), memory(0), 1);
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let result = store(&mut a, &model, &f, &before, 88, nat(7), 7, 8);
    drop(a);
    for (name, proof) in [
        ("store", &result.evaluated),
        ("readback", &result.typed_readback),
    ] {
        replay(&scope, proof, true);
        let term = scope.close(proof.term()).unwrap();
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
        let expected = match name {
            "store" => include_str!("testdata/store-eight.dag.hex"),
            "readback" => include_str!("testdata/readback-eight.dag.hex"),
            _ => unreachable!(),
        };
        let (pairs, odd) = expected.trim().as_bytes().as_chunks::<2>();
        assert!(
            odd.is_empty(),
            "{name}: hex baseline has an odd digit count"
        );
        let baseline: Vec<u8> = pairs
            .iter()
            .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect();
        assert_eq!(bytes, baseline);
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&baseline).unwrap();
        checker()
            .check_type(&decoded, &scope.close(&proof.proposition()).unwrap())
            .unwrap();
    }
}

fn load_fixture(
    context: Expr,
    ty: Expr,
    value: Expr,
    word: u64,
) -> (ByteEightCodec, ByteLoadEight, ByteLoadEightPremises) {
    let word_expr = nat(word);
    let shape = layout(ty.clone(), 8);
    let codec = ByteEightCodec {
        context: context.clone(),
        ty: ty.clone(),
        value: value.clone(),
        word: word_expr.clone(),
        layout: shape.clone(),
        lane: conversion(
            option("Nat"),
            app("ir_byte_lane_size_v1", [ty.clone()]),
            some("Nat", nat(8)),
        ),
        layout_found: conversion(
            option("IRByteLayoutV1"),
            app("ir_byte_layout_v1", [context.clone(), ty.clone()]),
            some("IRByteLayoutV1", shape.clone()),
        ),
        valid_layout: truth(layout_guard(shape.clone())),
        fits: truth(app(
            "ir_byte_value_matches_v1",
            [context.clone(), ty.clone(), value.clone()],
        )),
        encoded: conversion(
            option("Nat"),
            app("ir_byte_scalar_word_v1", [context.clone(), value.clone()]),
            some("Nat", word_expr.clone()),
        ),
        decoded: conversion(
            option("IRScalar"),
            app("ir_byte_decode_word_v1", [context, ty, word_expr.clone()]),
            some("IRScalar", value),
        ),
        bounded: bounded(word_expr.clone(), word),
    };
    let memory = app(
        "IRByteMemoryV1.mk",
        [
            allocs(memory(0)),
            app(
                "ir_byte_write_word_v1",
                [bytes(memory(0)), nat(80), nat(8), word_expr.clone()],
            ),
            cursor(memory(0)),
        ],
    );
    let input = ByteLoadEight {
        pointer: app("IRScalar.ptr_", [nat(80)]),
        address: nat(80),
        requested_align: nat(8),
        memory: memory.clone(),
    };
    let premises = ByteLoadEightPremises {
        pointer: conversion(
            option("Nat"),
            pointer_address(input.pointer.clone()),
            some("Nat", nat(80)),
        ),
        accessible: truth(app(
            "ir_byte_accessible_v1",
            [
                allocs(memory.clone()),
                nat(80),
                nat(8),
                app(
                    "ir_byte_effective_align_v1",
                    [nat(8), app("ir_byte_layout_align_v1", [shape])],
                ),
            ],
        )),
        initialized: conversion(
            option("Nat"),
            app("ir_byte_read_word_v1", [bytes(memory), nat(8), nat(80)]),
            some("Nat", word_expr),
        ),
    };
    (codec, input, premises)
}

fn typed_load_module() -> (Module, FuncId) {
    let mut builder = ModuleBuilder::new_with_target_info(
        "typed_load_identity",
        ordinary().module.target_info.clone().unwrap(),
    );
    let sig = builder.add_func_type(vec![], vec![Ty::I64]);
    let other_sig = builder.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let function = builder.declare_function("callback", sig);
    let other = builder.declare_function("other_callback", other_sig);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    body.switch_to_block(block);
    // The actual module owns a Func layout as well as the function binding.
    body.const_value(Ty::Func(sig), trust_ir::Constant::FnDef(function));
    body.const_value(Ty::Func(other_sig), trust_ir::Constant::FnDef(other));
    body.null_ptr();
    let value = body.iconst(Ty::I64, 7);
    body.ret(vec![value]);
    body.build();
    let mut body = builder.define_function(other).unwrap();
    let block = body.create_block();
    body.add_block_param(block, Ty::Ptr);
    body.switch_to_block(block);
    let value = body.iconst(Ty::I64, 7);
    body.ret(vec![value]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    (module, function)
}

#[test]
fn memory_access_typed_load_preserves_canonical_function_and_pointer_identity() {
    let (module, function) = typed_load_module();
    let reflected =
        reflect_core_module_v1(&module, &[(function, 4096), (FuncId::new(1), 8192)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    for (ty, value, word) in [
        (app("IRTy.int_", [nat(64)]), scalar(nat(u64::MAX)), u64::MAX),
        (constant("IRTy.ptr_"), constant("IRScalar.nullptr_"), 0),
        (constant("IRTy.ptr_"), app("IRScalar.ptr_", [nat(128)]), 128),
        (
            app("IRTy.func_", [nat(0)]),
            app("IRScalar.fnptr_", [nat(0)]),
            4096,
        ),
    ] {
        let (codec, input, premises) = load_fixture(model.context().clone(), ty, value, word);
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let loaded = a.byte_load_eight(&codec, input.clone(), premises).unwrap();
        assert_eq!(
            loaded.right(),
            &MemoryResult {
                value: codec.value,
                memory: input.memory
            }
            .result()
        );
        drop(a);
        replay(&scope, &loaded, true);
        let closed = scope.close(loaded.term()).unwrap();
        let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&closed).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
        checker()
            .check_type(&decoded, &scope.close(&loaded.proposition()).unwrap())
            .unwrap();
    }
}

#[test]
fn memory_access_typed_load_rejects_wrong_endpoints_and_false_evidence() {
    let (module, function) = typed_load_module();
    let reflected =
        reflect_core_module_v1(&module, &[(function, 4096), (FuncId::new(1), 8192)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let (codec, input, premises) = load_fixture(
        model.context().clone(),
        app("IRTy.int_", [nat(64)]),
        scalar(nat(7)),
        7,
    );
    for mutation in 0..6 {
        let mut input = input.clone();
        let mut premises = premises.clone();
        let mut codec = codec.clone();
        match mutation {
            0 => input.memory = memory(0),
            1 => input.pointer = app("IRScalar.ptr_", [nat(88)]),
            2 => input.requested_align = nat(16),
            3 => codec.word = nat(8),
            4 => premises.initialized.right = some("Nat", nat(8)),
            5 => codec.ty = app("IRTy.func_", [nat(1)]),
            _ => unreachable!(),
        }
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        assert!(
            a.byte_load_eight(&codec, input, premises).is_err(),
            "endpoint mutant {mutation}"
        );
    }
    // Syntactically matching but false evidence is still only a candidate:
    // the kernel, not the builder's endpoint checker, must reject it.
    for mutation in 0..5 {
        let (mut codec, input, mut premises) = load_fixture(
            model.context().clone(),
            app("IRTy.int_", [nat(64)]),
            scalar(nat(7)),
            7,
        );
        match mutation {
            0 => premises.pointer.term = refl(&option("Nat"), some("Nat", nat(88))),
            1 => premises.accessible.term = refl(&constant("Bool"), constant("Bool.false")),
            2 => premises.initialized.term = refl(&option("Nat"), some("Nat", nat(8))),
            3 => codec.decoded.term = refl(&option("IRScalar"), scalar(nat(8))),
            4 => codec.fits.term = refl(&constant("Bool"), constant("Bool.false")),
            _ => unreachable!(),
        }
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let loaded = a.byte_load_eight(&codec, input, premises).unwrap();
        drop(a);
        replay(&scope, &loaded, false);
    }
    for (ty, value, word) in [
        (
            app("IRTy.func_", [nat(1)]),
            app("IRScalar.fnptr_", [nat(0)]),
            4096,
        ),
        (
            app("IRTy.func_", [nat(0)]),
            app("IRScalar.fnptr_", [nat(1)]),
            4096,
        ),
        (constant("IRTy.ptr_"), app("IRScalar.ptr_", [nat(0)]), 0),
    ] {
        let (codec, input, premises) = load_fixture(model.context().clone(), ty, value, word);
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let loaded = a.byte_load_eight(&codec, input, premises).unwrap();
        drop(a);
        replay(&scope, &loaded, false);
    }
    for stale_memory in [true, false] {
        let (codec, mut input, mut premises) = load_fixture(
            model.context().clone(),
            app("IRTy.int_", [nat(64)]),
            scalar(nat(7)),
            7,
        );
        if stale_memory {
            input.memory = memory(0);
            // Correct endpoint, false initialization at the old byte map.
            premises.initialized.left = app(
                "ir_byte_read_word_v1",
                [bytes(input.memory.clone()), nat(8), input.address.clone()],
            );
        } else {
            input.requested_align = nat(32); // address80 is not aligned32
        }
        premises.accessible.left = app(
            "ir_byte_accessible_v1",
            [
                allocs(input.memory.clone()),
                input.address.clone(),
                nat(8),
                app(
                    "ir_byte_effective_align_v1",
                    [
                        input.requested_align.clone(),
                        app("ir_byte_layout_align_v1", [codec.layout.clone()]),
                    ],
                ),
            ],
        );
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let loaded = a.byte_load_eight(&codec, input, premises).unwrap();
        drop(a);
        replay(&scope, &loaded, false);
    }
}

#[test]
fn memory_access_typed_load_keeps_volatile_and_construction_gates() {
    let mut f = ordinary();
    let node = &mut f.module.functions[0].blocks[0].body[2];
    let trust_ir::Inst::Load { volatile, .. } = &mut node.inst else {
        panic!("actual fixture Load");
    };
    *volatile = true;
    assert!(crate::validate_module(&f.module).is_empty());
    assert_eq!(
        reflect_core_module_v1(&f.module, &[(f.function, 4096)])
            .unwrap_err()
            .to_string(),
        "volatile memory operations have no Core byte profile semantics"
    );
    let f = ordinary();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let (codec, input, premises) = load_fixture(
        model.context().clone(),
        app("IRTy.int_", [nat(64)]),
        scalar(nat(7)),
        7,
    );
    let mut scope = Scope::new();
    let mut bounded_limits = limits();
    bounded_limits.max_operations = 1;
    let mut a = Assembler::new(&mut scope, bounded_limits).unwrap();
    assert_eq!(
        a.byte_load_eight(&codec, input, premises)
            .err()
            .expect("construction must be bounded")
            .to_string(),
        "execution construction operation budget exceeded"
    );
}
