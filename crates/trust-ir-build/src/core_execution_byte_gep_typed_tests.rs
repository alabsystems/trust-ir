// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Authored ordinary Core and strict original/DAG replay, not frontend
//! extraction, provider authentication or native execution. The nominal
//! decoder is independently replayed over the original catalog and SSA IDs.

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

fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        // Catalog discovery is a separate existing policy, not replay fuel.
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}

fn replay(scope: &Scope, parameters: &[Local], term: &Expr, claim: &Expr, accepted: bool) {
    let term = parameters
        .iter()
        .rev()
        .fold(term.clone(), |body, local| local.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(claim.clone(), |body, local| local.pi(body));
    let term = scope.close(&term).unwrap();
    let claim = scope.close(&claim).unwrap();
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    assert!(!term.has_loose_bvars() && !claim.has_loose_bvars());
    let decoded_term = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap(),
    )
    .unwrap();
    let decoded_claim = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(&claim).unwrap(),
    )
    .unwrap();
    assert_eq!(decoded_term, term);
    assert_eq!(decoded_claim, claim);
    for (term, claim) in [(term, claim), (decoded_term, decoded_claim)] {
        let mut checker = TypeChecker::new(environment());
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        assert_eq!(checker.heartbeat_limit(), 2_000_000);
        checker
            .check_type(&claim, &Expr::sort(Level::zero()))
            .unwrap();
        let checked = checker.check_type(&term, &claim);
        assert!(
            !checker.heartbeat_spent(),
            "resource stop is not a verdict: {checked:?}"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        if accepted {
            checked.unwrap();
            assert!(
                environment()
                    .audit_certification(&claim, &term)
                    .is_certified()
            );
        } else {
            assert!(matches!(
                checked.unwrap_err(),
                KernelTypeError::TypeMismatch { .. }
            ));
        }
    }
}

fn replay_equality(scope: &Scope, proof: &PendingEquality, accepted: bool) {
    replay(scope, &[], proof.term(), &proof.proposition(), accepted);
}

fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(&ty, right))
}
fn truth(left: Expr) -> PendingEquality {
    conversion(constant("Bool"), left, constant("Bool.true"))
}
fn literal_bound(claim: Expr, value: Expr, literal: u128) -> PendingProof {
    // Deliberately false same-endpoint candidates on overflow/zero controls
    // must be rejected semantically, not accepted from this host calculation.
    let remainder = (1_u128 << 64)
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
fn positive(claim: Expr, value: u64) -> PendingProof {
    PendingProof::candidate(
        claim,
        app("Nat.zero_lt_succ", [nat(value.saturating_sub(1))]),
    )
}
fn scalar(value: u64) -> Expr {
    app("IRScalar.int_", [nat(value)])
}
fn pointer(value: u64) -> Expr {
    app("IRScalar.ptr_", [nat(value)])
}
fn layout(pointee: Expr, stride: u64) -> Expr {
    app(
        "IRByteLayoutV1.mk",
        [
            pointee,
            nat(stride),
            nat(stride),
            list("IRTy", &[]),
            list("Nat", &[]),
        ],
    )
}
fn current_memory(current: &Current) -> Expr {
    app(
        "ir_byte_world_memory_v1",
        [constant("Nat"), current.world.clone()],
    )
}
fn memory(base: u64, length: u64, byte: u64) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[app(
                    "IRByteAllocationV1.mk",
                    [nat(base), nat(length), nat(0), constant("Bool.true")],
                )],
            ),
            Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(byte))),
            nat(1),
        ],
    )
}
fn providers() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        constant("Nat"),
        Expr::lam(
            BinderInfo::Default,
            list_type("IRScalar"),
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
fn list_type(name: &str) -> Expr {
    app("IRList", [constant(name)])
}

struct Fixture {
    module: Module,
    function: FuncId,
    block: BlockId,
    base: ValueId,
    indices: Vec<ValueId>,
    result: ValueId,
    pointee: Ty,
    inbounds: bool,
}
fn fixture(pointee: Ty, index_types: &[Ty], inbounds: bool, repeated: bool) -> Fixture {
    let mut builder = ModuleBuilder::new_with_target_info(
        "original_selected_gep",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let parameters = std::iter::once(Ty::Ptr)
        .chain(index_types.iter().cloned())
        .collect();
    let signature = builder.add_func_type(parameters, vec![Ty::Ptr]);
    let function = builder.declare_function("original", signature);
    let mut body = builder.define_function(function).unwrap();
    body.set_calling_conv(CallingConv::C);
    let block = body.create_block();
    let base = body.add_block_param(block, Ty::Ptr);
    let indices: Vec<ValueId> = index_types
        .iter()
        .cloned()
        .map(|ty| body.add_block_param(block, ty))
        .collect();
    body.switch_to_block(block);
    let ids = if repeated {
        vec![indices[0], indices[0]]
    } else {
        indices.clone()
    };
    let result = if inbounds {
        body.gep_inbounds(pointee.clone(), base, ids)
    } else {
        body.gep(pointee.clone(), base, ids)
    };
    body.ret(vec![result]);
    body.build();
    let module = builder.build().unwrap();
    assert!(crate::validate_module(&module).is_empty());
    Fixture {
        module,
        function,
        block,
        base,
        indices,
        result,
        pointee,
        inbounds,
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
    fn current(&self, base: u64, indices: &[u64], memory: Expr) -> Current {
        assert_eq!(indices.len(), self.indices.len());
        let binding = |id: ValueId, value| app("IRBinding.mk", [nat(u64::from(id.index())), value]);
        let bindings: Vec<Expr> = std::iter::once(binding(self.base, pointer(base)))
            .chain(
                self.indices
                    .iter()
                    .zip(indices)
                    .map(|(id, value)| binding(*id, scalar(*value))),
            )
            .collect();
        Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(u64::from(self.function.index())),
                    nat(u64::from(self.block.index())),
                    nat(0),
                    list("IRBinding", &bindings),
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
                    memory,
                    nat(37),
                    list("Nat", &[nat(8)]),
                    nat(9),
                ],
            ),
        }
    }
}
fn nominal(ty: &Ty) -> Expr {
    match ty {
        Ty::U8 => app("IRTy.uint_", [nat(8)]),
        Ty::U32 => app("IRTy.uint_", [nat(32)]),
        Ty::I64 => app("IRTy.int_", [nat(64)]),
        _ => panic!("explicit test pointee"),
    }
}
fn input(f: &Fixture, before: &Current, base: u64, index: u64, stride: u64) -> ByteGepTyped {
    let pointee = nominal(&f.pointee);
    ByteGepTyped {
        layout: layout(pointee.clone(), stride),
        pointee,
        stride: nat(stride),
        pointer: app(
            "ir_getd",
            [before.machine(), nat(u64::from(f.base.index()))],
        ),
        base: nat(base),
        index: nat(index),
        memory: current_memory(before),
    }
}
fn premises(
    context: &Expr,
    input: &ByteGepTyped,
    base: u64,
    index: u64,
    stride: u64,
) -> ByteGepTypedPremises {
    let checks = input.checks(context);
    let equality = |(ty, left, right)| conversion(ty, left, right);
    let delta = u128::from(stride) * u128::from(index);
    ByteGepTypedPremises {
        layout: equality(checks.layout),
        layout_size: equality(checks.layout_size),
        pointer: equality(checks.pointer),
        base_positive: positive(checks.base_positive, base),
        stride_positive: positive(checks.stride_positive, stride),
        stride_bound: literal_bound(checks.stride_bound, nat(stride), u128::from(stride)),
        delta_bound: literal_bound(checks.delta_bound, input.resolved().delta(), delta),
        result_bound: literal_bound(
            checks.result_bound,
            input.resolved().address(),
            u128::from(base) + delta,
        ),
    }
}
fn candidate(
    a: &mut Assembler<'_>,
    context: &Expr,
    input: ByteGepTyped,
    premises: ByteGepTypedPremises,
    inbounds: bool,
) -> ByteGepTypedResult {
    if inbounds {
        let checks = input.checks(context);
        a.byte_gep_typed_inbounds(
            context.clone(),
            input,
            premises,
            truth(checks.inbounds_membership.1),
        )
        .unwrap()
    } else {
        a.byte_gep_typed_noninbounds(context.clone(), input, premises)
            .unwrap()
    }
}
fn decoder(site: &FetchedSite, before: &Current, index: u64) -> PendingEquality {
    conversion(
        option("Nat"),
        app(
            "ir_byte_gep_typed_indices_v1",
            [
                site.site.get_app_args()[6].clone(),
                before.machine(),
                site.instruction.get_app_args()[2].clone(),
            ],
        ),
        some("Nat", nat(index)),
    )
}
fn transfer(
    a: &mut Assembler<'_>,
    model: &MachineModel,
    site: &FetchedSite,
    before: &Current,
    selected: PendingEquality,
    result: ByteGepTypedResult,
    index: u64,
) -> MemoryTransfer {
    let evaluated = site
        .typed_gep_evaluation(a, model, before, nat(index), selected, result.evaluated)
        .unwrap();
    let checks = site.memory_checks(model, before, &result.result).unwrap();
    site.memory_value(
        a,
        model,
        before,
        result.result,
        MemoryPremises {
            evaluated,
            result: truth(checks.result),
            allocations: result.allocations,
            before: truth(before.valid(model)),
        },
    )
    .unwrap()
}
fn whole(
    a: &mut Assembler<'_>,
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
        list_type("IRScalar"),
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
    let valid = a
        .convert_endpoints(
            first.valid().clone(),
            frame.current(model).valid(model),
            constant("Bool.true"),
        )
        .unwrap();
    let returned = returning
        .return_from_root(a, model, &target, &frame, resolution, admitted, valid)
        .unwrap();
    let boundary = a
        .conversion(
            model.config_type(),
            first.run().reached().clone(),
            returned.run().initial().clone(),
        )
        .unwrap();
    let prefix = a.transport_reached(first.run().clone(), boundary).unwrap();
    a.concatenate(prefix, returned.run().clone()).unwrap()
}
fn final_goal(
    model: &MachineModel,
    before: &Current,
    address: u64,
    memory: Expr,
    host: u64,
) -> Expr {
    eq(
        &model.config_type(),
        model.run(&NatTerm::literal(2), before.running(model)),
        app(
            "IRByteConfigV1.halted",
            [
                constant("Nat"),
                app("IROutcome.ret", [list("IRScalar", &[pointer(address)])]),
                app(
                    "IRByteWorldV1.mk",
                    [constant("Nat"), memory, nat(host), list("Nat", &[]), nat(9)],
                ),
            ],
        ),
    )
}

#[test]
fn byte_gep_typed_symbolic_selected_layout_pointer_and_arithmetic_replay_strict_dag() {
    for name in [
        "ir_byte_gep_typed_v1",
        "ir_byte_gep_typed_indices_v1",
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
    for inbounds in [false, true] {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let context = a.local(constant("IRByteContextV1")).unwrap();
        let pointee = a.local(constant("IRTy")).unwrap();
        let shape = a.local(constant("IRByteLayoutV1")).unwrap();
        let stride = a.local(constant("Nat")).unwrap();
        let pointer = a.local(constant("IRScalar")).unwrap();
        let base = a.local(constant("Nat")).unwrap();
        let index = a.local(constant("Nat")).unwrap();
        let memory = a.local(constant("IRByteMemoryV1")).unwrap();
        let input = ByteGepTyped {
            pointee: pointee.term().clone(),
            layout: shape.term().clone(),
            stride: stride.term().clone(),
            pointer: pointer.term().clone(),
            base: base.term().clone(),
            index: index.term().clone(),
            memory: memory.term().clone(),
        };
        let mut parameters = vec![
            context.clone(),
            pointee,
            shape,
            stride,
            pointer,
            base,
            index,
            memory,
        ];
        let mut equalities = Vec::new();
        for (ty, left, right) in input.equalities(context.term()) {
            let local = a.local(eq(&ty, left.clone(), right.clone())).unwrap();
            equalities.push(PendingEquality::candidate(
                ty,
                left,
                right,
                local.term().clone(),
            ));
            parameters.push(local);
        }
        let mut bounds = Vec::new();
        for proposition in input.propositions() {
            let local = a.local(proposition.clone()).unwrap();
            bounds.push(PendingProof::candidate(proposition, local.term().clone()));
            parameters.push(local);
        }
        let premises = ByteGepTypedPremises {
            layout: equalities[0].clone(),
            layout_size: equalities[1].clone(),
            pointer: equalities[2].clone(),
            base_positive: bounds[0].clone(),
            stride_positive: bounds[1].clone(),
            stride_bound: bounds[2].clone(),
            delta_bound: bounds[3].clone(),
            result_bound: bounds[4].clone(),
        };
        let membership = if inbounds {
            let claim = input.checks(context.term()).inbounds_membership;
            let local = a
                .local(eq(&claim.0, claim.1.clone(), claim.2.clone()))
                .unwrap();
            let proof = PendingEquality::candidate(claim.0, claim.1, claim.2, local.term().clone());
            parameters.push(local);
            Some(proof)
        } else {
            None
        };
        let flag = constant(if inbounds { "Bool.true" } else { "Bool.false" });
        let expected_value = app(
            "IRScalar.ptr_",
            [app(
                "Nat.add",
                [
                    input.base.clone(),
                    app("Nat.mul", [input.stride.clone(), input.index.clone()]),
                ],
            )],
        );
        let evaluated_claim = eq(
            &constant("IRByteMemoryResultV1"),
            app(
                "ir_byte_gep_typed_v1",
                [
                    context.term().clone(),
                    input.pointee.clone(),
                    input.pointer.clone(),
                    some("Nat", input.index.clone()),
                    flag,
                    input.memory.clone(),
                ],
            ),
            MemoryResult {
                value: expected_value.clone(),
                memory: input.memory.clone(),
            }
            .result(),
        );
        let fit_claim = eq(
            &constant("Bool"),
            app(
                "ir_byte_value_matches_v1",
                [
                    context.term().clone(),
                    constant("IRTy.ptr_"),
                    expected_value,
                ],
            ),
            constant("Bool.true"),
        );
        let allocation_claim = eq(
            &list_type("IRByteAllocationV1"),
            allocs(input.memory.clone()),
            allocs(input.memory.clone()),
        );
        let result = match membership {
            Some(membership) => a
                .byte_gep_typed_inbounds(context.term().clone(), input, premises, membership)
                .unwrap(),
            None => a
                .byte_gep_typed_noninbounds(context.term().clone(), input, premises)
                .unwrap(),
        };
        for (proof, independent_claim) in [
            (&result.evaluated, evaluated_claim),
            (&result.result_fits, fit_claim),
            (&result.allocations, allocation_claim),
        ] {
            replay(
                a.local_scope(),
                &parameters,
                proof.term(),
                &independent_claim,
                true,
            );
        }
    }
}

#[test]
fn byte_gep_typed_original_two_ids_sum_to_high64_and_return_complete_world() {
    for (inbounds, repeated) in [(false, false), (true, false), (false, true)] {
        let f = fixture(Ty::U8, &[Ty::U64, Ty::U64], inbounds, repeated);
        let original = f.module.clone(); // Test-only source identity oracle.
        let reflected = reflect_core_module_v1_with_memory_profile(
            &f.module,
            &[(f.function, 4096)],
            CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
        )
        .unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mem = memory(1, 1_u64 << 63, 173);
        let before = f.current(1, &[1_u64 << 62, 1_u64 << 62], mem.clone());
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let site = catalog.fetch(f.coordinate(0)).unwrap();
        assert_eq!(site.site.get_app_fn(), &constant("IRByteSiteV1.mki"));
        let selected = decoder(&site, &before, 1_u64 << 63);
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        replay_equality(a.local_scope(), &selected, true);
        let input = input(&f, &before, 1, 1_u64 << 63, 1);
        let premises = premises(model.context(), &input, 1, 1_u64 << 63, 1);
        let result = candidate(&mut a, model.context(), input, premises, f.inbounds);
        replay_equality(a.local_scope(), &result.evaluated, true);
        let first = transfer(
            &mut a,
            &model,
            &site,
            &before,
            selected,
            result,
            1_u64 << 63,
        );
        replay_equality(a.local_scope(), first.step(), true);
        let run = whole(&mut a, &model, &mut catalog, &f, &first);
        assert_eq!(run.fuel().term(), &app("Nat.add", [nat(1), nat(1)]));
        replay(
            a.local_scope(),
            &[],
            run.equality().term(),
            &final_goal(&model, &before, (1_u64 << 63) + 1, mem.clone(), 37),
            true,
        );
        for (address, memory, host) in [
            ((1_u64 << 63) + 2, mem.clone(), 37),
            ((1_u64 << 63) + 1, memory(1, 1_u64 << 63, 174), 37),
            ((1_u64 << 63) + 1, mem, 38),
        ] {
            replay(
                a.local_scope(),
                &[],
                run.equality().term(),
                &final_goal(&model, &before, address, memory, host),
                false,
            );
        }
        assert_eq!(f.module, original, "no original source/profile rewrite");
    }
}

#[test]
fn byte_gep_typed_nominal_matrix_scaled_strides_retains_original_decoder() {
    for (pointee, stride, ty, index) in [
        (Ty::U8, 1, Ty::I8, 127),
        (Ty::U8, 1, Ty::U8, 255),
        (Ty::U32, 4, Ty::I16, 32767),
        (Ty::U32, 4, Ty::U16, 65535),
        (Ty::I64, 8, Ty::I32, 2147483647),
        (Ty::I64, 8, Ty::U32, 2147483648),
        (Ty::U8, 1, Ty::I64, 3),
        (Ty::U8, 1, Ty::U64, 3),
        (Ty::U8, 1, Ty::U64, 0),
    ] {
        let f = fixture(pointee, &[ty], false, false);
        let reflected = reflect_core_module_v1_with_memory_profile(
            &f.module,
            &[(f.function, 4096)],
            CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
        )
        .unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mem = memory(80, 16, 173);
        let before = f.current(80, &[index], mem.clone());
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let site = catalog.fetch(f.coordinate(0)).unwrap();
        let selected = decoder(&site, &before, index);
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        replay_equality(a.local_scope(), &selected, true);
        let input = input(&f, &before, 80, index, stride);
        let premises = premises(model.context(), &input, 80, index, stride);
        let result = candidate(&mut a, model.context(), input, premises, false);
        let first = transfer(&mut a, &model, &site, &before, selected, result, index);
        let run = whole(&mut a, &model, &mut catalog, &f, &first);
        replay(
            a.local_scope(),
            &[],
            run.equality().term(),
            &final_goal(&model, &before, 80 + stride * index, mem, 37),
            true,
        );
    }
}

#[test]
fn byte_gep_typed_false_layout_pointer_unbounded_arithmetic_and_membership_are_refuted() {
    let f = fixture(Ty::U32, &[Ty::U64], false, false);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    for mutation in 0..7 {
        let before = f.current(
            if mutation == 1 { 0 } else { 80 },
            &[2],
            memory(80, 16, 173),
        );
        let mut input = input(
            &f,
            &before,
            if mutation == 1 { 0 } else { 80 },
            2,
            if mutation == 2 { 0 } else { 4 },
        );
        match mutation {
            0 => input.layout = layout(input.pointee.clone(), 8),
            3 => input.index = nat(1_u64 << 62),
            4 => {
                input.base = nat(u64::MAX);
                input.pointer = pointer(u64::MAX);
            }
            _ => {}
        }
        let base = if mutation == 1 {
            0
        } else if mutation == 4 {
            u64::MAX
        } else {
            80
        };
        let index = if mutation == 3 { 1_u64 << 62 } else { 2 };
        let stride = if mutation == 2 { 0 } else { 4 };
        let mut proofs = premises(model.context(), &input, base, index, stride);
        if mutation == 5 {
            proofs.delta_bound.term = app("Nat.zero_lt_succ", [nat(0)]);
        }
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let result = if mutation == 6 {
            // Correct endpoints, false same-allocation proof: result exceeds
            // the current live extent, not a permission granted by the API.
            input.index = nat(5);
            let premises = premises(model.context(), &input, 80, 5, 4);
            candidate(&mut a, model.context(), input, premises, true)
        } else {
            candidate(&mut a, model.context(), input, proofs, false)
        };
        replay_equality(a.local_scope(), &result.evaluated, false);
    }
}

#[test]
fn byte_gep_typed_actual_catalog_signed_carrier_and_ordered_ids_cannot_be_forged() {
    for (ty, values, repeated, claimed_index) in [
        (Ty::I8, vec![255, 1], false, 256),
        (Ty::U8, vec![256, 1], false, 257),
        (Ty::U64, vec![1_u64 << 63, 1], false, (1_u64 << 63) + 1),
        (Ty::U64, vec![2, 3], true, 5),
    ] {
        let f = fixture(Ty::U8, &[ty.clone(), ty], false, repeated);
        let reflected = reflect_core_module_v1_with_memory_profile(
            &f.module,
            &[(f.function, 4096)],
            CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
        )
        .unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let before = f.current(80, &values, memory(80, 16, 173));
        let site = Catalog::new(environment(), &reflected, limits())
            .unwrap()
            .fetch(f.coordinate(0))
            .unwrap();
        let selected = decoder(&site, &before, claimed_index);
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        replay_equality(a.local_scope(), &selected, false);
        let input = input(&f, &before, 80, claimed_index, 1);
        let premises = premises(model.context(), &input, 80, claimed_index, 1);
        let result = candidate(&mut a, model.context(), input, premises, false);
        // The arithmetic candidate can be true while the actual source
        // decoder is false. The fetched step must still reject it.
        replay_equality(a.local_scope(), &result.evaluated, true);
        let first = transfer(
            &mut a,
            &model,
            &site,
            &before,
            selected,
            result,
            claimed_index,
        );
        replay_equality(a.local_scope(), first.step(), false);
    }
}

#[test]
fn byte_gep_typed_fetched_endpoint_checks_retain_original_context_machine_and_memory() {
    let f = fixture(Ty::U8, &[Ty::U64], false, false);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let genuine = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(0))
        .unwrap();
    let before = f.current(80, &[2], memory(80, 16, 173));
    for mutation in 0..5 {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let mut site = genuine.clone();
        let mut selected = decoder(&site, &before, 2);
        let mut input = input(&f, &before, 80, 2, 1);
        match mutation {
            0 => site.context = constant("different_actual_context"),
            1 => {
                let mut fields: Vec<Expr> = site.site.get_app_args().into_iter().cloned().collect();
                fields[2] = nat(1);
                site.site = app("IRByteSiteV1.mki", fields);
            }
            2 => {
                let fields: Vec<Expr> = site.site.get_app_args().into_iter().cloned().collect();
                site.site = app("IRByteSiteV1.mkt", fields);
            }
            3 => selected = decoder(&site, &f.current(80, &[3], memory(80, 16, 173)), 2),
            _ => input.memory = memory(80, 16, 174),
        }
        let premises = premises(model.context(), &input, 80, 2, 1);
        let result = candidate(&mut a, model.context(), input, premises, false);
        let operations = a.operations();
        assert!(
            site.typed_gep_evaluation(&mut a, &model, &before, nat(2), selected, result.evaluated)
                .is_err()
        );
        assert_eq!(
            a.operations(),
            operations + 1,
            "failed original endpoint preflight remains spent"
        );
    }
}

#[test]
fn byte_gep_typed_completed_helpers_reuse_no_captured_inputs_and_keep_legacy_cache_separate() {
    let f = fixture(Ty::U8, &[Ty::U64], false, false);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let second_reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 8192)],
        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
    )
    .unwrap();
    let second_model = MachineModel::new(constant("Nat"), &second_reflected, providers());
    assert_ne!(model.context(), second_model.context());
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let mut cached = None;
    let mut locals = 0;
    for (base, index, byte, current_model) in [(80, 2, 173, &model), (200, 3, 174, &second_model)] {
        let before = f.current(base, &[index], memory(base, 16, byte));
        let input = input(&f, &before, base, index, 1);
        let premises = premises(current_model.context(), &input, base, index, 1);
        let operations = a.operations();
        let result = candidate(&mut a, current_model.context(), input, premises, false);
        let helper = a.byte_gep_typed_candidates[0].as_ref().unwrap();
        assert!(!helper.has_fvar_quick() && !helper.has_loose_bvars());
        if let Some(previous) = &cached {
            assert_eq!(helper, previous);
            assert_eq!(a.locals, locals);
            assert_eq!(
                a.operations(),
                operations + 1,
                "a warm candidate charges the public door only"
            );
        } else {
            cached = Some(helper.clone());
            locals = a.locals;
        }
        assert!(a.byte_gep_typed_candidates[1].is_none());
        assert!(a.byte_gep_singleton_candidates.iter().all(Option::is_none));
        replay_equality(a.local_scope(), &result.evaluated, true);
    }
    let before = f.current(80, &[2], memory(80, 16, 173));
    let selected = input(&f, &before, 80, 2, 1);
    let checks = selected.checks(model.context());
    let old = ByteGepSingleton {
        pointee: selected.pointee,
        layout: selected.layout,
        stride: selected.stride,
        pointer: selected.pointer,
        indices: app(
            "ir_resolve",
            [
                before.machine(),
                list("Nat", &[nat(u64::from(f.indices[0].index()))]),
            ],
        ),
        base: selected.base,
        index: selected.index,
        memory: selected.memory,
    };
    let p = premises(model.context(), &input(&f, &before, 80, 2, 1), 80, 2, 1);
    let index_bound = PendingProof::candidate(
        app("Nat.lt", [nat(2), nat(1_u64 << 63)]),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(2)]), nat((1_u64 << 63) - 3)],
        ),
    );
    let old_premises = ByteGepSingletonPremises {
        layout: p.layout,
        layout_size: p.layout_size,
        pointer: p.pointer,
        indices: conversion(
            old.equalities(model.context())[3].0.clone(),
            old.equalities(model.context())[3].1.clone(),
            old.equalities(model.context())[3].2.clone(),
        ),
        base_positive: p.base_positive,
        index_bound,
        stride_positive: p.stride_positive,
        stride_bound: p.stride_bound,
        delta_bound: p.delta_bound,
        result_bound: p.result_bound,
    };
    let before_locals = a.locals;
    let legacy = a
        .byte_gep_singleton_noninbounds(model.context().clone(), old, old_premises)
        .unwrap();
    assert_eq!(
        a.locals - before_locals,
        27,
        "old singleton helper telescope and eliminator binders are unchanged"
    );
    assert_eq!(
        legacy.evaluated.left().get_app_fn(),
        &constant("ir_byte_gep_v1")
    );
    assert_eq!(a.byte_gep_typed_candidates[0].as_ref(), cached.as_ref());
    assert!(a.byte_gep_singleton_candidates[0].is_some());
    assert!(a.byte_gep_singleton_candidates[1].is_none());
    assert_eq!(checks.inbounds_membership.2, constant("Bool.true"));
    replay_equality(a.local_scope(), &legacy.evaluated, true);

    // Sharing the suffix does not remove the old erased decoder's <2^63
    // premise. An exactly shaped but false boundary proof is still refuted.
    let before = f.current(80, &[1_u64 << 63], memory(80, 16, 173));
    let selected = input(&f, &before, 80, 1_u64 << 63, 1);
    let p = premises(model.context(), &selected, 80, 1_u64 << 63, 1);
    let old = ByteGepSingleton {
        pointee: selected.pointee,
        layout: selected.layout,
        stride: selected.stride,
        pointer: selected.pointer,
        indices: app(
            "ir_resolve",
            [
                before.machine(),
                list("Nat", &[nat(u64::from(f.indices[0].index()))]),
            ],
        ),
        base: selected.base,
        index: selected.index,
        memory: selected.memory,
    };
    let (ty, left, right) = old.equalities(model.context())[3].clone();
    let false_bound = PendingProof::candidate(
        app("Nat.lt", [nat(1_u64 << 63), nat(1_u64 << 63)]),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(1_u64 << 63)]), nat(0)],
        ),
    );
    let p = ByteGepSingletonPremises {
        layout: p.layout,
        layout_size: p.layout_size,
        pointer: p.pointer,
        indices: conversion(ty, left, right),
        base_positive: p.base_positive,
        index_bound: false_bound,
        stride_positive: p.stride_positive,
        stride_bound: p.stride_bound,
        delta_bound: p.delta_bound,
        result_bound: p.result_bound,
    };
    let legacy = a
        .byte_gep_singleton_noninbounds(model.context().clone(), old, p)
        .unwrap();
    replay_equality(a.local_scope(), &legacy.evaluated, false);
}

#[test]
fn byte_gep_typed_wrong_premise_shapes_and_partial_or_overflowed_budgets_fail_closed() {
    let f = fixture(Ty::U8, &[Ty::U64], false, false);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let before = f.current(80, &[2], memory(80, 16, 173));
    for mutation in 0..4 {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let input = input(&f, &before, 80, 2, 1);
        let mut premises = premises(model.context(), &input, 80, 2, 1);
        match mutation {
            0 => {
                premises.layout.left = app(
                    "ir_byte_layout_v1",
                    [model.context().clone(), constant("IRTy.ptr_")],
                )
            }
            1 => premises.layout_size.right = nat(4),
            2 => premises.pointer.right = some("Nat", nat(81)),
            _ => premises.delta_bound.proposition = app("Nat.lt", [nat(2), nat(1_u64 << 63)]),
        }
        assert!(
            a.byte_gep_typed_noninbounds(model.context().clone(), input, premises)
                .is_err()
        );
        assert_eq!(a.operations(), 1);
        assert_eq!(a.locals, 0);
        assert!(a.byte_gep_typed_candidates.iter().all(Option::is_none));
    }
    {
        let mut scope = Scope::new();
        let mut bounded = limits();
        bounded.max_operations = 1;
        bounded.max_locals = 100;
        let mut a = Assembler::new(&mut scope, bounded).unwrap();
        let input = input(&f, &before, 80, 2, 1);
        let premises = premises(model.context(), &input, 80, 2, 1);
        let error = a
            .byte_gep_typed_noninbounds(model.context().clone(), input, premises)
            .err()
            .unwrap();
        assert_eq!(error, "execution construction operation budget exceeded");
        assert!(a.operations() > 0);
        assert!(a.byte_gep_typed_candidates.iter().all(Option::is_none));
    }
    // The selected fixed helper now needs no caller locals. A caller whose
    // real allocation allowance is exhausted can still build its candidate;
    // a subsequent explicit allocation continues to refuse without refund.
    let mut scope = Scope::new();
    let mut bounded = limits();
    bounded.max_locals = 1;
    let mut a = Assembler::new(&mut scope, bounded).unwrap();
    let _held = a.local(constant("Nat")).unwrap();
    let selected_input = input(&f, &before, 80, 2, 1);
    let selected_premises = premises(model.context(), &selected_input, 80, 2, 1);
    let result = a
        .byte_gep_typed_noninbounds(model.context().clone(), selected_input, selected_premises)
        .unwrap();
    assert_eq!(a.locals, 1);
    replay_equality(a.local_scope(), &result.evaluated, true);
    let spent = a.operations();
    assert_eq!(
        a.local(constant("Nat")).err().unwrap(),
        "execution construction local budget exceeded"
    );
    assert_eq!(a.operations(), spent + 1);
    assert_eq!(a.locals, 1);
    assert!(a.byte_gep_typed_candidates[0].is_some());

    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    a.operations = usize::MAX;
    let input = input(&f, &before, 80, 2, 1);
    let premises = premises(model.context(), &input, 80, 2, 1);
    assert_eq!(
        a.byte_gep_typed_noninbounds(model.context().clone(), input, premises)
            .err()
            .unwrap(),
        "operation counter overflow"
    );
    assert_eq!(a.operations(), usize::MAX);
    assert_eq!(a.locals, 0);
    assert!(a.byte_gep_typed_candidates.iter().all(Option::is_none));
}

#[path = "core_execution_byte_gep_typed_closed_tests.rs"]
mod closed_templates;
