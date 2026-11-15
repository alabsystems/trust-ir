// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Actual nominal GEP/catalog and full-world strict model replay. Authored
//! ordinary Core, not extracted source or native execution. Legacy singleton
//! arithmetic remains separate; only checked nominal decoding selects `mki`.

use super::*;
use crate::ModuleBuilder;
use crate::core_reflection::{
    CoreMemoryIndexProfileV1, reflect_core_module_v1_with_memory_profile,
};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{CallingConv, Endianness, Module, StructPassingPolicy, TargetInfo, Ty};

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}

fn checker() -> TypeChecker<'static> {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    assert_eq!(checker.heartbeat_limit(), 2_000_000);
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
    assert!(!term.has_loose_bvars() && !claim.has_loose_bvars());
    let term_bytes = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let claim_bytes = trust_ir::proof::encode_clean_expr_dag_v2(&claim).unwrap();
    let decoded_term = trust_ir::proof::decode_clean_expr_dag_v2(&term_bytes).unwrap();
    let decoded_claim = trust_ir::proof::decode_clean_expr_dag_v2(&claim_bytes).unwrap();
    assert_eq!(decoded_term, term);
    assert_eq!(decoded_claim, claim);
    for (term, claim) in [(term, claim), (decoded_term, decoded_claim)] {
        let kernel = checker();
        kernel
            .check_type(&claim, &Expr::sort(Level::zero()))
            .unwrap();
        let checked = kernel.check_type(&term, &claim);
        assert!(
            !kernel.heartbeat_spent(),
            "resource stop is not a verdict: {checked:?}"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        if accepted {
            checked.unwrap();
            let audit = environment().audit_certification(&claim, &term);
            assert!(audit.is_certified(), "{audit:#?}");
        } else {
            let error = checked.unwrap_err();
            assert!(
                matches!(error, KernelTypeError::TypeMismatch { .. }),
                "semantic refusal, not exhausted work: {error:?}"
            );
        }
    }
}

fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(&ty, right))
}
fn truth(left: Expr) -> PendingEquality {
    conversion(constant("Bool"), left, constant("Bool.true"))
}
fn option_nat() -> Expr {
    app("IROption", [constant("Nat")])
}
fn some_nat(value: Expr) -> Expr {
    app("IROption.some", [constant("Nat"), value])
}
fn scalar(value: Expr) -> Expr {
    app("IRScalar.int_", [value])
}
fn pointer(value: Expr) -> Expr {
    app("IRScalar.ptr_", [value])
}
fn current_memory(current: &Current) -> Expr {
    app(
        "ir_byte_world_memory_v1",
        [constant("Nat"), current.world.clone()],
    )
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

fn memory_with_byte(byte: u64) -> Expr {
    let allocation = |base, length, owner, live| {
        app(
            "IRByteAllocationV1.mk",
            [
                nat(base),
                nat(length),
                nat(owner),
                constant(if live { "Bool.true" } else { "Bool.false" }),
            ],
        )
    };
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[
                    allocation(80, (1_u64 << 32) + 16, 0, true),
                    allocation(16, 8, 7, false),
                ],
            ),
            Expr::lam(BinderInfo::Default, constant("Nat"), some_nat(nat(byte))),
            nat((1_u64 << 32) + 112),
        ],
    )
}
fn memory() -> Expr {
    memory_with_byte(173)
}

struct Fixture {
    module: Module,
    function: FuncId,
    block: BlockId,
    base: ValueId,
    index: ValueId,
    result: ValueId,
}
fn fixture(ty: Ty) -> Fixture {
    let mut builder = ModuleBuilder::new_with_target_info(
        "original_typed_integer_gep",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::Ptr, ty.clone()], vec![Ty::Ptr]);
    let function = builder.declare_function("original", signature);
    let mut body = builder.define_function(function).unwrap();
    body.set_calling_conv(CallingConv::C);
    let block = body.create_block();
    let base = body.add_block_param(block, Ty::Ptr);
    let index = body.add_block_param(block, ty);
    body.switch_to_block(block);
    let result = body.gep(Ty::U8, base, vec![index]);
    body.ret(vec![result]);
    body.build();
    Fixture {
        module: builder.build().unwrap(),
        function,
        block,
        base,
        index,
        result,
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
    fn current(&self, index: u64) -> Current {
        let binding = |id: ValueId, value| app("IRBinding.mk", [nat(u64::from(id.index())), value]);
        Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(u64::from(self.function.index())),
                    nat(u64::from(self.block.index())),
                    nat(0),
                    list(
                        "IRBinding",
                        &[
                            binding(self.base, pointer(nat(80))),
                            binding(self.index, scalar(nat(index))),
                        ],
                    ),
                    list("Nat", &[]),
                ],
            ),
            tail: list("IRFrame", &[]),
            legacy_memory: list("IRMemSlot", &[]),
            legacy_cursor: nat(0),
            world: app(
                "IRByteWorldV1.mk",
                [
                    constant("Nat"),
                    memory(),
                    nat(37),
                    list("Nat", &[nat(8)]),
                    nat(9),
                ],
            ),
        }
    }
}

fn decoder(site: &FetchedSite, current: &Current, index: u64) -> PendingEquality {
    let rows = site.site.get_app_args()[6].clone();
    let ids = site.instruction.get_app_args()[2].clone();
    conversion(
        option_nat(),
        app(
            "ir_byte_gep_typed_indices_v1",
            [rows, current.machine(), ids],
        ),
        some_nat(nat(index)),
    )
}

fn bounded(claim: Expr, value: Expr, literal: u64, upper: u128) -> PendingProof {
    let remainder = upper
        .checked_sub(u128::from(literal) + 1)
        .and_then(|v| u64::try_from(v).ok())
        .unwrap_or(0);
    PendingProof::candidate(
        claim,
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [value]), nat(remainder)],
        ),
    )
}

fn old_singleton(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    f: &Fixture,
    before: &Current,
    index: u64,
) -> ByteGepSingletonResult {
    let pointee = app("IRTy.uint_", [nat(8)]);
    let input = ByteGepSingleton {
        layout: app(
            "IRByteLayoutV1.mk",
            [
                pointee.clone(),
                nat(1),
                nat(1),
                list("IRTy", &[]),
                list("Nat", &[]),
            ],
        ),
        pointee,
        stride: nat(1),
        pointer: app(
            "ir_getd",
            [before.machine(), nat(u64::from(f.base.index()))],
        ),
        indices: app(
            "ir_resolve",
            [
                before.machine(),
                list("Nat", &[nat(u64::from(f.index.index()))]),
            ],
        ),
        base: nat(80),
        index: nat(index),
        memory: current_memory(before),
    };
    let checks = input.checks(model.context());
    let eq = |(ty, left, right): (Expr, Expr, Expr)| conversion(ty, left, right);
    let positive = |n: u64| app("Nat.zero_lt_succ", [nat(n - 1)]);
    let premises = ByteGepSingletonPremises {
        layout: eq(checks.layout),
        layout_size: eq(checks.layout_size),
        pointer: eq(checks.pointer),
        indices: eq(checks.indices),
        base_positive: PendingProof::candidate(checks.base_positive, positive(80)),
        index_bound: bounded(checks.index_bound, nat(index), index, 1_u128 << 63),
        stride_positive: PendingProof::candidate(checks.stride_positive, positive(1)),
        stride_bound: bounded(checks.stride_bound, nat(1), 1, 1_u128 << 64),
        delta_bound: bounded(
            checks.delta_bound,
            app("Nat.mul", [nat(1), nat(index)]),
            index,
            1_u128 << 64,
        ),
        result_bound: bounded(
            checks.result_bound,
            app("Nat.add", [nat(80), app("Nat.mul", [nat(1), nat(index)])]),
            80 + index,
            1_u128 << 64,
        ),
    };
    assembler
        .byte_gep_singleton_noninbounds(model.context().clone(), input, premises)
        .unwrap()
}

fn transfer(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    f: &Fixture,
    site: &FetchedSite,
    before: &Current,
    index: u64,
) -> MemoryTransfer {
    let old = old_singleton(assembler, model, f, before, index);
    let selected = decoder(site, before, index);
    let fields = site.instruction.get_app_args();
    let typed = app(
        "ir_byte_gep_typed_v1",
        [
            model.context().clone(),
            fields[0].clone(),
            app("ir_getd", [before.machine(), fields[1].clone()]),
            some_nat(nat(index)),
            fields[3].clone(),
            current_memory(before),
        ],
    );
    // Independent legacy arithmetic has its original explicit <2^63 premise;
    // conversion never substitutes it for the nominal decoder equality.
    let bridge = assembler
        .conversion(
            constant("IRByteMemoryResultV1"),
            typed,
            old.evaluated.left().clone(),
        )
        .unwrap();
    let evaluated = assembler.compose(bridge, old.evaluated).unwrap();
    let evaluated = site
        .typed_gep_evaluation(assembler, model, before, nat(index), selected, evaluated)
        .unwrap();
    let checks = site.memory_checks(model, before, &old.result).unwrap();
    site.memory_value(
        assembler,
        model,
        before,
        old.result,
        MemoryPremises {
            evaluated,
            result: truth(checks.result),
            allocations: old.allocations,
            before: truth(before.valid(model)),
        },
    )
    .unwrap()
}

fn whole(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    catalog: &mut Catalog<'_, '_>,
    f: &Fixture,
    first: &MemoryTransfer,
) -> ExactRun {
    let current = first.current();
    let frame = RootReturnFrame {
        returning: current.frame.clone(),
        legacy_memory: current.legacy_memory.clone(),
        legacy_cursor: current.legacy_cursor.clone(),
        memory: current_memory(current),
        host: nat(37),
        owner: nat(8),
        next: nat(9),
    };
    let target = catalog.call_target(f.function).unwrap();
    let returning = catalog.fetch(f.coordinate(1)).unwrap();
    let values = list("IRScalar", std::slice::from_ref(&first.result().value));
    let resolution = conversion(
        app("IRList", [constant("IRScalar")]),
        app(
            "ir_resolve",
            [
                frame.current(model).machine(),
                list("Nat", &[nat(u64::from(f.result.index()))]),
            ],
        ),
        values.clone(),
    );
    let admitted = truth(
        returning
            .root_return_admission(model, &target, &frame, values)
            .unwrap(),
    );
    let valid = assembler
        .convert_endpoints(
            first.valid().clone(),
            frame.current(model).valid(model),
            constant("Bool.true"),
        )
        .unwrap();
    let returned = returning
        .return_from_root(
            assembler, model, &target, &frame, resolution, admitted, valid,
        )
        .unwrap();
    let boundary = assembler
        .conversion(
            model.config_type(),
            first.run().reached().clone(),
            returned.run().initial().clone(),
        )
        .unwrap();
    let prefix = assembler
        .transport_reached(first.run().clone(), boundary)
        .unwrap();
    assembler
        .concatenate(prefix, returned.run().clone())
        .unwrap()
}

fn final_goal(model: &MachineModel, before: &Current, index: u64, host: u64) -> Expr {
    final_goal_memory(model, before, index, host, memory())
}

fn final_goal_memory(
    model: &MachineModel,
    before: &Current,
    index: u64,
    host: u64,
    memory: Expr,
) -> Expr {
    eq(
        &model.config_type(),
        model.run(&NatTerm::literal(2), before.running(model)),
        app(
            "IRByteConfigV1.halted",
            [
                constant("Nat"),
                app(
                    "IROutcome.ret",
                    [list("IRScalar", &[pointer(nat(80 + index))])],
                ),
                app(
                    "IRByteWorldV1.mk",
                    [constant("Nat"), memory, nat(host), list("Nat", &[]), nat(9)],
                ),
            ],
        ),
    )
}

#[test]
fn typed_integer_gep_fetched_nominal_matrix_replays_original_two_step_world_and_dag() {
    for (ty, index) in [
        (Ty::I8, 3),
        (Ty::U8, 200),
        (Ty::I16, 3),
        (Ty::U16, 50_000),
        (Ty::I32, 3),
        (Ty::U32, (1_u64 << 31) + 1),
        (Ty::I64, 3),
        (Ty::U64, 3),
    ] {
        let f = fixture(ty);
        let original = f.module.clone();
        let reflected = reflect_core_module_v1_with_memory_profile(
            &f.module,
            &[(f.function, 4096)],
            CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
        )
        .unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let before = f.current(index);
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let site = catalog.fetch(f.coordinate(0)).unwrap();
        assert_eq!(site.site.get_app_fn(), &constant("IRByteSiteV1.mki"));
        replay(&Scope::new(), &decoder(&site, &before, index), true);
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let first = transfer(&mut assembler, &model, &f, &site, &before, index);
        let execution = whole(&mut assembler, &model, &mut catalog, &f, &first);
        let goal = final_goal(&model, &before, index, 37);
        let expected = goal.get_app_args();
        let proof = assembler
            .convert_endpoints(
                execution.equality().clone(),
                expected[1].clone(),
                expected[2].clone(),
            )
            .unwrap();
        replay(assembler.local_scope(), &proof, true);
        let wrong = final_goal(&model, &before, index, 38).get_app_args()[2].clone();
        replay(
            assembler.local_scope(),
            &PendingEquality::candidate(
                model.config_type(),
                proof.left().clone(),
                wrong,
                proof.term().clone(),
            ),
            false,
        );
        assert_eq!(f.module, original);
    }
}

#[test]
fn typed_integer_gep_decoder_rejects_negative_noncanonical_and_high64_words_semantically() {
    for (ty, word) in [
        (Ty::I8, 128),
        (Ty::U8, 256),
        (Ty::I16, 32_768),
        (Ty::U16, 65_536),
        (Ty::I32, 1_u64 << 31),
        (Ty::U32, 1_u64 << 32),
        (Ty::I64, 1_u64 << 63),
        (Ty::U64, 1_u64 << 63),
    ] {
        let f = fixture(ty);
        let reflected = reflect_core_module_v1_with_memory_profile(
            &f.module,
            &[(f.function, 4096)],
            CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
        )
        .unwrap();
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let site = catalog.fetch(f.coordinate(0)).unwrap();
        let before = f.current(word);
        let false_some = decoder(&site, &before, word);
        replay(&Scope::new(), &false_some, false);
        replay(
            &Scope::new(),
            &conversion(
                option_nat(),
                false_some.left().clone(),
                app("IROption.none", [constant("Nat")]),
            ),
            true,
        );
    }
}

#[test]
fn typed_integer_gep_changed_catalog_ids_types_and_ordered_ids_never_gain_fetched_authority() {
    let f = fixture(Ty::I32);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
    )
    .unwrap();
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let genuine = catalog.fetch(f.coordinate(0)).unwrap();
    let before = f.current(3);
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    for mutation in 0..4 {
        let mut site = genuine.clone();
        if mutation < 3 {
            let mut fields: Vec<Expr> = site.site.get_app_args().into_iter().cloned().collect();
            let row = app(
                "IRByteOperandV1.mk",
                [
                    nat(if mutation == 0 {
                        999
                    } else {
                        u64::from(f.index.index())
                    }),
                    if mutation == 1 {
                        constant("IRTy.bool_")
                    } else {
                        app("IRTy.int_", [nat(32)])
                    },
                ],
            );
            let rows = if mutation == 2 {
                vec![row.clone(), row]
            } else {
                vec![row]
            };
            fields[6] = list("IRByteOperandV1", &rows);
            site.site = app("IRByteSiteV1.mki", fields);
            replay(&Scope::new(), &decoder(&site, &before, 3), false);
        } else {
            let mut fields: Vec<Expr> = site
                .instruction
                .get_app_args()
                .into_iter()
                .cloned()
                .collect();
            fields[2] = list("Nat", &[nat(999)]);
            site.instruction = app("IRInst.gep", fields);
            replay(&Scope::new(), &decoder(&site, &before, 3), false);
        }
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let first = transfer(&mut assembler, &model, &f, &site, &before, 3);
        replay(assembler.local_scope(), first.step(), false);
    }
    // A changed sign catalog can produce the same address but still is NOT
    // the actual fetched site. Its false lookup evidence must be rejected.
    let mut unsigned = genuine.clone();
    let mut fields: Vec<Expr> = unsigned.site.get_app_args().into_iter().cloned().collect();
    fields[6] = list(
        "IRByteOperandV1",
        &[app(
            "IRByteOperandV1.mk",
            [
                nat(u64::from(f.index.index())),
                app("IRTy.uint_", [nat(32)]),
            ],
        )],
    );
    unsigned.site = app("IRByteSiteV1.mki", fields);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let first = transfer(&mut assembler, &model, &f, &unsigned, &before, 3);
    replay(assembler.local_scope(), first.step(), false);
}

#[test]
fn typed_integer_gep_bridge_charges_and_refuses_wrong_context_site_machine_and_operand_shapes() {
    let f = fixture(Ty::I32);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
    )
    .unwrap();
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let genuine = catalog.fetch(f.coordinate(0)).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let before = f.current(3);
    for mutation in 0..5 {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let mut site = genuine.clone();
        let mut decoded = decoder(&site, &before, 3);
        match mutation {
            0 => site.context = constant("wrong_actual_context"),
            1 => {
                let mut fields: Vec<Expr> = site.site.get_app_args().into_iter().cloned().collect();
                fields[2] = nat(1);
                site.site = app("IRByteSiteV1.mki", fields);
            }
            2 => {
                let fields: Vec<Expr> = site.site.get_app_args().into_iter().cloned().collect();
                site.site = app("IRByteSiteV1.mkt", fields);
            }
            3 => decoded = decoder(&site, &f.current(4), 3),
            _ => site.instruction = app("IRInst.ret", [list("Nat", &[])]),
        }
        let old = old_singleton(&mut assembler, &model, &f, &before, 3);
        let operations = assembler.operations();
        assert!(
            site.typed_gep_evaluation(
                &mut assembler,
                &model,
                &before,
                nat(3),
                decoded,
                old.evaluated
            )
            .is_err()
        );
        assert_eq!(assembler.operations(), operations + 1);
    }
}

#[test]
fn typed_integer_gep_preserves_changed_incoming_memory_not_a_cached_or_assumed_world() {
    let f = fixture(Ty::I32);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog.fetch(f.coordinate(0)).unwrap();
    let mut before = f.current(3);
    let changed_memory = memory_with_byte(174);
    before.world = app(
        "IRByteWorldV1.mk",
        [
            constant("Nat"),
            changed_memory.clone(),
            nat(37),
            list("Nat", &[nat(8)]),
            nat(9),
        ],
    );
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let first = transfer(&mut assembler, &model, &f, &site, &before, 3);
    let execution = whole(&mut assembler, &model, &mut catalog, &f, &first);
    let expected = final_goal_memory(&model, &before, 3, 37, changed_memory);
    let fields = expected.get_app_args();
    let proof = assembler
        .convert_endpoints(
            execution.equality().clone(),
            fields[1].clone(),
            fields[2].clone(),
        )
        .unwrap();
    replay(assembler.local_scope(), &proof, true);
    let lost_memory = final_goal(&model, &before, 3, 37).get_app_args()[2].clone();
    replay(
        assembler.local_scope(),
        &PendingEquality::candidate(
            model.config_type(),
            proof.left().clone(),
            lost_memory,
            proof.term().clone(),
        ),
        false,
    );
}

fn typed_equation(
    site: &FetchedSite,
    model: &MachineModel,
    before: &Current,
    index: u64,
) -> PendingEquality {
    let fields = site.instruction.get_app_args();
    let left = app(
        "ir_byte_gep_typed_v1",
        [
            model.context().clone(),
            fields[0].clone(),
            app("ir_getd", [before.machine(), fields[1].clone()]),
            some_nat(nat(index)),
            fields[3].clone(),
            current_memory(before),
        ],
    );
    conversion(
        constant("IRByteMemoryResultV1"),
        left,
        MemoryResult {
            value: pointer(nat(80 + index)),
            memory: current_memory(before),
        }
        .result(),
    )
}

#[test]
fn typed_integer_gep_preflight_and_compose_charge_preserve_partial_spent_and_overflowed_budgets() {
    let f = fixture(Ty::I32);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog.fetch(f.coordinate(0)).unwrap();
    let before = f.current(3);
    let decoded = decoder(&site, &before, 3);
    let evaluated = typed_equation(&site, &model, &before, 3);
    let mut scope = Scope::new();
    // Real independently replayed prerequisites isolate the construction gate
    // from a malformed/false candidate and retain the ordinary strict limits.
    replay(&scope, &decoded, true);
    replay(&scope, &evaluated, true);
    let mut policy = limits();
    policy.max_operations = 1;
    let mut partial = Assembler::new(&mut scope, policy).unwrap();
    for _ in 0..2 {
        let error = site
            .typed_gep_evaluation(
                &mut partial,
                &model,
                &before,
                nat(3),
                decoded.clone(),
                evaluated.clone(),
            )
            .err()
            .unwrap();
        assert_eq!(error, "execution construction operation budget exceeded");
        assert_eq!(
            partial.operations(),
            1,
            "the preflight charge is not refunded"
        );
    }
    drop(partial);
    let mut success = Assembler::new(&mut scope, limits()).unwrap();
    let proof = site
        .typed_gep_evaluation(
            &mut success,
            &model,
            &before,
            nat(3),
            decoded.clone(),
            evaluated.clone(),
        )
        .unwrap();
    assert_eq!(
        success.operations(),
        2,
        "one preflight plus one existing compose charge"
    );
    replay(success.local_scope(), &proof, true);
    drop(success);
    let mut overflowing = Assembler::new(&mut scope, limits()).unwrap();
    overflowing.operations = usize::MAX;
    let error = site
        .typed_gep_evaluation(
            &mut overflowing,
            &model,
            &before,
            nat(3),
            decoded,
            evaluated,
        )
        .err()
        .unwrap();
    assert_eq!(error, "operation counter overflow");
    assert_eq!(overflowing.operations(), usize::MAX);
}

#[test]
fn typed_integer_gep_site_endpoint_is_additive_and_legacy_profiles_stay_exact() {
    // The nominal bridge consumes these public checked roots, never an axiom
    // or a trust marker installed by this consumer's environment.
    for name in [
        "ir_byte_gep_index_limit_v1",
        "ir_byte_gep_typed_index_v1",
        "ir_byte_gep_typed_indices_v1",
        "ir_byte_gep_typed_v1",
        "ir_byte_gep_site_v1",
        "ir_byte_gep_site_mki_selected_v1",
    ] {
        let root = Name::from_string(name);
        assert!(environment().axiom_deps(&root).unwrap().is_empty());
        assert!(
            environment()
                .foundational_axiom_deps(&root)
                .unwrap()
                .is_empty()
        );
        assert!(environment().trust_marker_deps(&root).unwrap().is_empty());
    }
    let f = fixture(Ty::I64);
    let before = f.current(3);
    for profile in [
        CoreMemoryIndexProfileV1::StrictI64,
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
    ] {
        let reflected =
            reflect_core_module_v1_with_memory_profile(&f.module, &[(f.function, 4096)], profile)
                .unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let site = catalog.fetch(f.coordinate(0)).unwrap();
        let fields = site.instruction.get_app_args();
        let evaluation = site
            .memory_checks(
                &model,
                &before,
                &MemoryResult {
                    value: pointer(nat(83)),
                    memory: current_memory(&before),
                },
            )
            .unwrap()
            .evaluation;
        if profile == CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1 {
            assert_eq!(
                evaluation,
                app(
                    "ir_byte_gep_site_v1",
                    [
                        model.context().clone(),
                        site.site.clone(),
                        fields[0].clone(),
                        before.machine(),
                        fields[1].clone(),
                        fields[2].clone(),
                        fields[3].clone(),
                        current_memory(&before)
                    ]
                )
            );
        } else {
            assert_eq!(
                evaluation,
                app(
                    "ir_byte_gep_v1",
                    [
                        model.context().clone(),
                        fields[0].clone(),
                        app("ir_getd", [before.machine(), fields[1].clone()]),
                        app("ir_resolve", [before.machine(), fields[2].clone()]),
                        fields[3].clone(),
                        current_memory(&before)
                    ]
                )
            );
        }
    }
}
