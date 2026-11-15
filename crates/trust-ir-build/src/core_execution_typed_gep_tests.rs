// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordinary original Core singleton GEPs, exact reflection/catalog fetches and
//! independently checked ByteV1 candidates. These are shared-model tests, not
//! a TY source denotation, caller-access proof or native compilation receipt.
//! The bounded unsigned profile preserves the actual U64 operand: no body,
//! nominal type or index is rewritten to obtain a successful replay.

use super::*;
use crate::ModuleBuilder;
use crate::core_reflection::{
    CoreMemoryIndexProfileV1, reflect_core_module_v1, reflect_core_module_v1_with_memory_profile,
};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{CallingConv, Endianness, Inst, Module, StructPassingPolicy, TargetInfo, Ty};

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
    replay_parameters(scope, &[], proof, accepted);
}

fn closed(scope: &Scope, parameters: &[Local], proof: &PendingEquality) -> (Expr, Expr) {
    let term = parameters
        .iter()
        .rev()
        .fold(proof.term().clone(), |body, local| local.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(proof.proposition(), |body, local| local.pi(body));
    (scope.close(&term).unwrap(), scope.close(&claim).unwrap())
}

fn replay_parameters(scope: &Scope, parameters: &[Local], proof: &PendingEquality, accepted: bool) {
    let (term, claim) = closed(scope, parameters, proof);
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let checker = checker();
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .expect("the exact original claim must be a proposition");
    if accepted {
        checker.check_type(&term, &claim).unwrap();
        let audit = environment().audit_certification(&claim, &term);
        assert!(audit.is_certified(), "{audit:#?}");
    } else {
        let error = checker.check_type(&term, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "a real mismatch, not an exhausted checker budget: {error:?}"
        );
    }
}

fn replay_dag(scope: &Scope, parameters: &[Local], proof: &PendingEquality) {
    replay_parameters(scope, parameters, proof, true);
    let (term, claim) = closed(scope, parameters, proof);
    let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
    assert_eq!(decoded, term, "the entire lossless proof term is retained");
    checker().check_type(&decoded, &claim).unwrap();
    assert!(
        environment()
            .audit_certification(&claim, &decoded)
            .is_certified()
    );
}

fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(&ty, right))
}

fn truth(left: Expr) -> PendingEquality {
    conversion(constant("Bool"), left, constant("Bool.true"))
}

fn literal_bound(claim: Expr, value: Expr, literal: u128, upper_literal: u128) -> PendingProof {
    // On a negative control the zero remainder deliberately does NOT prove
    // the requested bound. Construction is untrusted; the real kernel must
    // reject that false same-endpoint candidate.
    let remainder = upper_literal
        .checked_sub(literal + 1)
        .and_then(|n| u64::try_from(n).ok())
        .unwrap_or(0);
    PendingProof::candidate(
        claim,
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [value]), nat(remainder)],
        ),
    )
}

fn positive(value: u64) -> PendingProof {
    PendingProof::candidate(
        app("Nat.lt", [nat(0), nat(value)]),
        app("Nat.zero_lt_succ", [nat(value.saturating_sub(1))]),
    )
}

fn providers() -> Expr {
    // A total, unused provider: neither original instruction is an import.
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

fn byte_map() -> Expr {
    Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(173)))
}

fn memory(live: bool, duplicate: bool, bytes: Expr) -> Expr {
    let allocation = || {
        app(
            "IRByteAllocationV1.mk",
            [
                nat(80),
                nat(16),
                nat(0),
                constant(if live { "Bool.true" } else { "Bool.false" }),
            ],
        )
    };
    let rows = if duplicate {
        vec![allocation(), allocation()]
    } else {
        vec![allocation()]
    };
    app(
        "IRByteMemoryV1.mk",
        [list("IRByteAllocationV1", &rows), bytes, nat(1)],
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
    index: ValueId,
    result: ValueId,
}

fn fixture(pointee: Ty, index_ty: Ty, inbounds: bool) -> Fixture {
    let mut builder = ModuleBuilder::new_with_target_info(
        "typed_singleton_gep",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::Ptr, index_ty.clone()], vec![Ty::Ptr]);
    let function = builder.declare_function("original_gep", signature);
    let mut body = builder.define_function(function).unwrap();
    body.set_calling_conv(CallingConv::C);
    let block = body.create_block();
    let pointer = body.add_block_param(block, Ty::Ptr);
    let index = body.add_block_param(block, index_ty);
    body.switch_to_block(block);
    let result = if inbounds {
        body.gep_inbounds(pointee, pointer, vec![index])
    } else {
        body.gep(pointee, pointer, vec![index])
    };
    body.ret(vec![result]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    Fixture {
        module,
        function,
        block,
        pointer,
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

    fn current(&self, base: u64, index: u64, memory: Expr) -> Current {
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
                            binding(self.pointer, app("IRScalar.ptr_", [nat(base)])),
                            binding(self.index, scalar(nat(index))),
                        ],
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
}

fn pointee(ty: &Ty) -> Expr {
    match ty {
        Ty::U8 => app("IRTy.uint_", [nat(8)]),
        Ty::U32 => app("IRTy.uint_", [nat(32)]),
        Ty::I64 => app("IRTy.int_", [nat(64)]),
        Ty::Ptr => constant("IRTy.ptr_"),
        _ => panic!("test nominal type must be explicit"),
    }
}

fn input(
    _model: &MachineModel,
    f: &Fixture,
    before: &Current,
    ty: &Ty,
    base: u64,
    index: u64,
    stride: u64,
) -> ByteGepSingleton {
    let pointee = pointee(ty);
    ByteGepSingleton {
        layout: layout(pointee.clone(), stride),
        pointee,
        stride: nat(stride),
        pointer: app(
            "ir_getd",
            [before.machine(), nat(u64::from(f.pointer.index()))],
        ),
        indices: app(
            "ir_resolve",
            [
                before.machine(),
                list("Nat", &[nat(u64::from(f.index.index()))]),
            ],
        ),
        base: nat(base),
        index: nat(index),
        memory: current_memory(before),
    }
}

fn premises(
    model: &MachineModel,
    input: &ByteGepSingleton,
    base: u64,
    index: u64,
    stride: u64,
) -> ByteGepSingletonPremises {
    let checks = input.checks(model.context());
    let equality = |(ty, left, right): (Expr, Expr, Expr)| conversion(ty, left, right);
    let delta = u128::from(stride) * u128::from(index);
    let address = u128::from(base) + delta;
    ByteGepSingletonPremises {
        layout: equality(checks.layout),
        layout_size: equality(checks.layout_size),
        pointer: equality(checks.pointer),
        indices: equality(checks.indices),
        base_positive: PendingProof::candidate(checks.base_positive, positive(base).term().clone()),
        index_bound: literal_bound(
            checks.index_bound,
            input.index.clone(),
            u128::from(index),
            1_u128 << 63,
        ),
        stride_positive: PendingProof::candidate(
            checks.stride_positive,
            positive(stride).term().clone(),
        ),
        stride_bound: literal_bound(
            checks.stride_bound,
            input.stride.clone(),
            u128::from(stride),
            1_u128 << 64,
        ),
        delta_bound: literal_bound(checks.delta_bound, input.delta(), delta, 1_u128 << 64),
        result_bound: literal_bound(checks.result_bound, input.address(), address, 1_u128 << 64),
    }
}

fn candidate(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    input: ByteGepSingleton,
    premises: ByteGepSingletonPremises,
    membership: Option<PendingEquality>,
) -> Result<ByteGepSingletonResult> {
    match membership {
        Some(membership) => assembler.byte_gep_singleton_inbounds(
            model.context().clone(),
            input,
            premises,
            membership,
        ),
        None => assembler.byte_gep_singleton_noninbounds(model.context().clone(), input, premises),
    }
}

fn transfer(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    site: &FetchedSite,
    before: &Current,
    result: ByteGepSingletonResult,
) -> MemoryTransfer {
    let checks = site.memory_checks(model, before, &result.result).unwrap();
    let bridge = assembler
        .conversion(
            constant("IRByteMemoryResultV1"),
            checks.evaluation,
            result.evaluated.left.clone(),
        )
        .unwrap();
    let evaluated = assembler.compose(bridge, result.evaluated).unwrap();
    site.memory_value(
        assembler,
        model,
        before,
        result.result,
        MemoryPremises {
            evaluated,
            allocations: result.allocations,
            result: truth(checks.result),
            before: truth(before.valid(model)),
        },
    )
    .unwrap()
}

fn whole_run(
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
    let site = catalog.fetch(f.coordinate(1)).unwrap();
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
        site.root_return_admission(model, &target, &frame, values)
            .unwrap(),
    );
    let before = assembler
        .conversion(
            constant("Bool"),
            frame.current(model).valid(model),
            first.valid().left.clone(),
        )
        .unwrap();
    let before = assembler.compose(before, first.valid().clone()).unwrap();
    let returned = site
        .return_from_root(
            assembler, model, &target, &frame, resolution, admitted, before,
        )
        .unwrap();
    // Transport the complete running configuration to the root-return view.
    // This candidate (including the current byte world) is replayed as part
    // of the entire fetched two-step run, not accepted from endpoint shape.
    let boundary = assembler
        .conversion(
            model.config_type(),
            first.run().reached().clone(),
            returned.run().initial().clone(),
        )
        .unwrap();
    let first = assembler
        .transport_reached(first.run().clone(), boundary)
        .unwrap();
    assembler
        .concatenate(first, returned.run().clone())
        .unwrap()
}

#[test]
fn typed_singleton_gep_fetched_strides_one_four_eight_and_root_return_replay_dag_v2() {
    for (ty, stride) in [(Ty::U8, 1), (Ty::U32, 4), (Ty::I64, 8), (Ty::Ptr, 8)] {
        let f = fixture(ty.clone(), Ty::U64, false);
        let original = f.module.clone(); // Test identity oracle only.
        let reflected = reflect_core_module_v1_with_memory_profile(
            &f.module,
            &[(f.function, 4096)],
            CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
        )
        .unwrap();
        assert!(std::ptr::eq(reflected.module(), &f.module));
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let site = catalog.fetch(f.coordinate(0)).unwrap();
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        // Universally quantified prior bytes: GEP grants no initialized/readable
        // region, and the fetched Return retains this exact current memory.
        let bytes = assembler
            .local(Expr::pi(
                BinderInfo::Default,
                constant("Nat"),
                option("Nat"),
            ))
            .unwrap();
        let before = f.current(80, 2, memory(true, false, bytes.term().clone()));
        let input = input(&model, &f, &before, &ty, 80, 2, stride);
        let premises = premises(&model, &input, 80, 2, stride);
        let result = candidate(&mut assembler, &model, input, premises, None).unwrap();
        let independent_value = app("IRScalar.ptr_", [nat(80 + 2 * stride)]);
        let pointer_equation = assembler
            .conversion(
                constant("IRScalar"),
                result.result.value.clone(),
                independent_value,
            )
            .unwrap();
        let fit = result.result_fits.clone();
        let first = transfer(&mut assembler, &model, &site, &before, result);
        let run = whole_run(&mut assembler, &model, &mut catalog, &f, &first);
        let fuel = assembler
            .conversion(constant("Nat"), run.fuel().term().clone(), nat(2))
            .unwrap();
        assert_eq!(run.initial(), &before.running(&model));
        drop(assembler);
        let parameters = std::slice::from_ref(&bytes);
        replay_parameters(&scope, parameters, &fuel, true);
        replay_parameters(&scope, parameters, &pointer_equation, true);
        replay_parameters(&scope, parameters, &fit, true);
        replay_dag(&scope, parameters, run.equality());
        assert_eq!(
            f.module, original,
            "neither source Core nor metadata was projected or rewritten"
        );
    }
}

#[test]
fn typed_singleton_gep_signed_profile_parity_and_unsigned_refusal_are_preserved() {
    let unsigned = fixture(Ty::U8, Ty::U64, false);
    assert_eq!(
        reflect_core_module_v1(&unsigned.module, &[(unsigned.function, 4096)])
            .unwrap_err()
            .to_string(),
        "byte profile requires typed I64 GEP indices"
    );
    let f = fixture(Ty::U8, Ty::I64, false);
    for profile in [
        CoreMemoryIndexProfileV1::StrictI64,
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    ] {
        let reflected =
            reflect_core_module_v1_with_memory_profile(&f.module, &[(f.function, 4096)], profile)
                .unwrap();
        assert_eq!(reflected.memory_index_profile(), profile);
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let site = Catalog::new(environment(), &reflected, limits())
            .unwrap()
            .fetch(f.coordinate(0))
            .unwrap();
        let before = f.current(80, 8, memory(true, false, byte_map()));
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let input = input(&model, &f, &before, &Ty::U8, 80, 8, 1);
        let premises = premises(&model, &input, 80, 8, 1);
        let result = candidate(&mut a, &model, input, premises, None).unwrap();
        let first = transfer(&mut a, &model, &site, &before, result);
        drop(a);
        replay(&scope, first.step(), true);
    }
}

#[test]
fn typed_singleton_gep_inbounds_uses_exact_current_live_unique_allocation_and_one_past() {
    let f = fixture(Ty::U32, Ty::U64, true);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(0))
        .unwrap();
    for (live, duplicate, index, accepted) in [
        (true, false, 0, true),
        (true, false, 2, true),
        (true, false, 4, true),
        (true, false, 5, false),
        (false, false, 2, false),
        (true, true, 2, false),
    ] {
        let before = f.current(80, index, memory(live, duplicate, byte_map()));
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let input = input(&model, &f, &before, &Ty::U32, 80, index, 4);
        let premises = premises(&model, &input, 80, index, 4);
        let (ty, left, right) = input.checks(model.context()).inbounds_membership;
        let membership = conversion(ty, left, right);
        let result = candidate(&mut a, &model, input, premises, Some(membership)).unwrap();
        let first = transfer(&mut a, &model, &site, &before, result);
        drop(a);
        replay(&scope, first.step(), accepted);
    }
}

#[test]
fn typed_singleton_gep_stale_memory_membership_is_never_current_memory_evidence() {
    let f = fixture(Ty::I64, Ty::U64, true);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(0))
        .unwrap();
    let before = f.current(80, 1, memory(false, false, byte_map()));
    for forged_same_endpoint in [false, true] {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let input = input(&model, &f, &before, &Ty::I64, 80, 1, 8);
        let premises = premises(&model, &input, 80, 1, 8);
        let stale = truth(app(
            "ir_byte_same_allocation_v1",
            [
                allocs(memory(true, false, byte_map())),
                nat(80),
                input.address(),
            ],
        ));
        let result = if forged_same_endpoint {
            candidate(
                &mut a,
                &model,
                input.clone(),
                premises,
                Some(PendingEquality::candidate(
                    constant("Bool"),
                    input.checks(model.context()).inbounds_membership.1,
                    constant("Bool.true"),
                    stale.term.clone(),
                )),
            )
            .unwrap()
        } else {
            assert!(
                candidate(&mut a, &model, input, premises, Some(stale)).is_err(),
                "foreign memory endpoints must refuse before proof composition"
            );
            continue;
        };
        let first = transfer(&mut a, &model, &site, &before, result);
        drop(a);
        replay(&scope, first.step(), false);
    }
}

#[test]
fn typed_singleton_gep_high_half_product_and_address_wrap_are_kernel_refutations() {
    for (ty, stride, base, index, accepted) in [
        (Ty::U8, 1, 80, 0, true),
        (Ty::U8, 1, 1, (1_u64 << 63) - 1, true),
        (Ty::U8, 1, 1, 1_u64 << 63, false),
        (Ty::U8, 1, 1, u64::MAX, false),
        (Ty::I64, 8, 1, 1_u64 << 61, false),
        (Ty::U8, 1, u64::MAX, 1, false),
    ] {
        let f = fixture(ty.clone(), Ty::U64, false);
        let reflected = reflect_core_module_v1_with_memory_profile(
            &f.module,
            &[(f.function, 4096)],
            CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
        )
        .unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let site = Catalog::new(environment(), &reflected, limits())
            .unwrap()
            .fetch(f.coordinate(0))
            .unwrap();
        let before = f.current(base, index, memory(true, false, byte_map()));
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let input = input(&model, &f, &before, &ty, base, index, stride);
        let premises = premises(&model, &input, base, index, stride);
        let result = candidate(&mut a, &model, input, premises, None).unwrap();
        let first = transfer(&mut a, &model, &site, &before, result);
        drop(a);
        replay(&scope, first.step(), accepted);
    }
}

#[test]
fn typed_singleton_gep_nominal_layout_stride_index_and_same_endpoint_proof_mutants_refuse() {
    let f = fixture(Ty::U8, Ty::U64, false);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(0))
        .unwrap();
    let before = f.current(80, 2, memory(true, false, byte_map()));
    for mutation in 0..=6 {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let mut input = input(&model, &f, &before, &Ty::U8, 80, 2, 1);
        let (mut base, mut index, mut stride) = (80, 2, 1);
        match mutation {
            0 => {
                stride = 4;
                input.stride = nat(stride); // actual U8 layout still has size1
            }
            1 => {
                stride = 4;
                input.stride = nat(stride);
                input.layout = layout(pointee(&Ty::U32), stride);
            }
            2 => {
                stride = 8;
                input.stride = nat(stride);
                input.pointee = pointee(&Ty::I64); // not the fetched U8 GEP
                input.layout = layout(input.pointee.clone(), stride);
            }
            3 => {
                index = 3;
                input.index = nat(index); // actual original operand resolves2
            }
            4 => {
                base = 88;
                input.base = nat(base); // actual original pointer addresses80
            }
            5 | 6 => {}
            _ => unreachable!(),
        }
        let premises = premises(&model, &input, base, index, stride);
        let mut result = candidate(&mut a, &model, input, premises, None).unwrap();
        if mutation == 5 {
            result.evaluated.term = refl(&constant("Bool"), constant("Bool.true"));
        }
        let first = transfer(&mut a, &model, &site, &before, result);
        drop(a);
        // 6 is the mandatory unmutated positive: construction refusal cannot
        // masquerade as any of the six residual-proof negative controls.
        replay(&scope, first.step(), mutation == 6);
    }
}

#[test]
fn typed_singleton_gep_original_index_list_and_profile_types_are_not_reconstructed() {
    let bad_width = fixture(Ty::U8, Ty::U32, false);
    assert!(
        reflect_core_module_v1_with_memory_profile(
            &bad_width.module,
            &[(bad_width.function, 4096)],
            CoreMemoryIndexProfileV1::TypedI64U64BoundedV1
        )
        .is_err()
    );
    for arity in [0, 1, 2] {
        let mut f = fixture(Ty::U32, Ty::U64, false);
        let Inst::GEP { indices, .. } = &mut f.module.functions[0].blocks[0].body[0].inst else {
            panic!("original GEP")
        };
        *indices = vec![f.index; arity];
        assert!(crate::validate_module(&f.module).is_empty());
        let reflected = reflect_core_module_v1_with_memory_profile(
            &f.module,
            &[(f.function, 4096)],
            CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
        )
        .unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let site = Catalog::new(environment(), &reflected, limits())
            .unwrap()
            .fetch(f.coordinate(0))
            .unwrap();
        let before = f.current(80, 2, memory(true, false, byte_map()));
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        // This candidate claims a singleton. The fetched source remains its
        // real empty/singleton/repeated ordered list; only arity1 can replay.
        let input = input(&model, &f, &before, &Ty::U32, 80, 2, 4);
        let premises = premises(&model, &input, 80, 2, 4);
        let result = candidate(&mut a, &model, input, premises, None).unwrap();
        let first = transfer(&mut a, &model, &site, &before, result);
        drop(a);
        replay(&scope, first.step(), arity == 1);
    }
}

#[test]
fn typed_singleton_gep_closed_helper_reuses_actual_context_stride_and_memory() {
    let first = fixture(Ty::U8, Ty::U64, false);
    let second = fixture(Ty::U32, Ty::U64, false);
    let first_reflected = reflect_core_module_v1_with_memory_profile(
        &first.module,
        &[(first.function, 4096)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap();
    let second_reflected = reflect_core_module_v1_with_memory_profile(
        &second.module,
        &[(second.function, 8192)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap();
    let first_model = MachineModel::new(constant("Nat"), &first_reflected, providers());
    let second_model = MachineModel::new(constant("Nat"), &second_reflected, providers());
    assert_ne!(first_model.context(), second_model.context());
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let mut kept = Vec::new();
    let mut helper = None;
    let mut helper_locals = 0;
    for (f, model, ty, stride, base, index, mem) in [
        (
            &first,
            &first_model,
            Ty::U8,
            1,
            80,
            2,
            memory(true, false, byte_map()),
        ),
        (
            &second,
            &second_model,
            Ty::U32,
            4,
            200,
            3,
            memory(
                false,
                false,
                Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(29))),
            ),
        ),
    ] {
        let before = f.current(base, index, mem);
        let input = input(model, f, &before, &ty, base, index, stride);
        let premises = premises(model, &input, base, index, stride);
        let result = candidate(&mut a, model, input, premises, None).unwrap();
        let cached = a.byte_gep_singleton_candidates[0].as_ref().unwrap();
        assert!(!cached.has_fvar_quick());
        if let Some(helper) = &helper {
            assert_eq!(cached, helper);
            assert_eq!(
                a.locals, helper_locals,
                "a new source context must not recapture template locals"
            );
        } else {
            helper = Some(cached.clone());
            helper_locals = a.locals;
            assert_eq!(
                helper_locals, 27,
                "the singleton helper shares its three eliminator binders; no duplicate recursor functions"
            );
        }
        assert!(a.byte_gep_singleton_candidates[1].is_none());
        assert_eq!(result.evaluated.term().get_app_fn(), cached);
        kept.push(result.evaluated);
    }
    drop(a);
    for proof in kept {
        replay(&scope, &proof, true);
    }
}

#[test]
fn typed_singleton_gep_endpoint_and_construction_budgets_remain_fail_closed() {
    let f = fixture(Ty::U8, Ty::U64, false);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let before = f.current(80, 2, memory(true, false, byte_map()));
    for bad_premise in 0..4 {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let input = input(&model, &f, &before, &Ty::U8, 80, 2, 1);
        let mut premises = premises(&model, &input, 80, 2, 1);
        match bad_premise {
            0 => {
                premises.layout.left = app(
                    "ir_byte_layout_v1",
                    [model.context().clone(), pointee(&Ty::I64)],
                )
            }
            1 => premises.layout_size.right = nat(4),
            2 => premises.pointer.right = some("Nat", nat(88)),
            3 => premises.index_bound = positive(2),
            _ => unreachable!(),
        }
        assert!(candidate(&mut a, &model, input, premises, None).is_err());
    }
    for (operations, locals, expected) in [
        (1, 100, "execution construction operation budget exceeded"),
        (1_000, 1, "execution construction local budget exceeded"),
    ] {
        let mut scope = Scope::new();
        let mut bounded_limits = limits();
        bounded_limits.max_operations = operations;
        bounded_limits.max_locals = locals;
        let mut a = Assembler::new(&mut scope, bounded_limits).unwrap();
        let input = input(&model, &f, &before, &Ty::U8, 80, 2, 1);
        let premises = premises(&model, &input, 80, 2, 1);
        let error = candidate(&mut a, &model, input, premises, None)
            .err()
            .expect("resource refusal, not a proof result");
        assert_eq!(error, expected);
        assert!(a.byte_gep_singleton_candidates.iter().all(Option::is_none));
    }
}
