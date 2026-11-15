// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual reflected/fetched singleton Return replay, not native or whole-wrapper
//! execution evidence. The C2Ptr fixture's five stores identify a realistic
//! terminal site; their preceding execution is deliberately not assumed proved.

use super::*;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
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

fn replay(scope: &Scope, proof: &Expr, claim: &Expr, accepted: bool) {
    let proof = scope.close(proof).unwrap();
    let claim = scope.close(claim).unwrap();
    assert!(!proof.has_fvar_quick() && !claim.has_fvar_quick());
    assert!(!proof.has_loose_bvars() && !claim.has_loose_bvars());
    let checker = checker();
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .unwrap();
    if accepted {
        checker.check_type(&proof, &claim).unwrap();
        let audit = environment().audit_certification(&claim, &proof);
        assert!(audit.is_certified(), "{audit:#?}");
    } else {
        let error = checker.check_type(&proof, &claim).unwrap_err();
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

fn providers() -> Expr {
    // Total, unused provider, not a hypothesis of provider fidelity.
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

fn builder() -> ModuleBuilder {
    ModuleBuilder::new_with_target_info(
        "root_return_replay",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    )
}

fn int(word: u64) -> Expr {
    app("IRScalar.int_", [nat(word)])
}
fn pointer(word: u64) -> Expr {
    app("IRScalar.ptr_", [nat(word)])
}
fn binding(id: ValueId, value: Expr) -> Expr {
    app("IRBinding.mk", [nat(u64::from(id.index())), value])
}

fn output_bytes(changed: bool) -> Expr {
    let mut bytes = Expr::lam(
        BinderInfo::Default,
        constant("Nat"),
        app("IROption.none", [constant("Nat")]),
    );
    // Ptr/U64/I64/U64/U64 words at exactly output+0/8/16/24/32.
    for (index, word) in [16, 1_u64 << 63, u64::MAX, 3, if changed { 6 } else { 5 }]
        .into_iter()
        .enumerate()
    {
        bytes = app(
            "ir_byte_write_word_v1",
            [bytes, nat(80 + 8 * index as u64), nat(8), nat(word)],
        );
    }
    bytes
}

fn memory(root_live: bool, output_live: bool, changed: bool) -> Expr {
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
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[
                    allocation(16, 16, 8, root_live),
                    allocation(80, 40, 0, output_live),
                    allocation(128, 8, 7, false),
                ],
            ),
            output_bytes(changed),
            nat(192),
        ],
    )
}

fn terminal(values: Expr, memory: Expr, host: u64, owners: &[Expr], next: u64) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            constant("Nat"),
            app("IROutcome.ret", [values]),
            app(
                "IRByteWorldV1.mk",
                [
                    constant("Nat"),
                    memory,
                    nat(host),
                    list("Nat", owners),
                    nat(next),
                ],
            ),
        ],
    )
}

struct Fixture {
    module: Module,
    function: FuncId,
    block: BlockId,
    pc: usize,
    bindings: Vec<Expr>,
    arguments: Vec<ValueId>,
    values: Vec<Expr>,
}

impl Fixture {
    fn coordinate(&self) -> Coordinate {
        Coordinate {
            function: self.function,
            block: self.block,
            instruction: self.pc,
        }
    }

    fn frame(&self) -> RootReturnFrame {
        RootReturnFrame {
            returning: app(
                "IRFrame.mk",
                [
                    nat(u64::from(self.function.index())),
                    nat(u64::from(self.block.index())),
                    nat(self.pc as u64),
                    list("IRBinding", &self.bindings),
                    list("Nat", &[]),
                ],
            ),
            legacy_memory: list("IRMemSlot", &[]),
            legacy_cursor: nat(0),
            memory: memory(true, true, false),
            host: nat(37),
            owner: nat(8),
            next: nat(9),
        }
    }

    fn resolved(
        &self,
        model: &MachineModel,
        frame: &RootReturnFrame,
        values: Expr,
    ) -> PendingEquality {
        conversion(
            app("IRList", [constant("IRScalar")]),
            app(
                "ir_resolve",
                [
                    frame.current(model).machine(),
                    list(
                        "Nat",
                        &self
                            .arguments
                            .iter()
                            .map(|id| nat(u64::from(id.index())))
                            .collect::<Vec<_>>(),
                    ),
                ],
            ),
            values,
        )
    }
}

fn wrapper_suffix() -> Fixture {
    let mut builder = builder();
    let signature = builder.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![]);
    let function = builder.declare_function("wrapper", signature);
    let mut body = builder.define_function(function).unwrap();
    body.set_calling_conv(CallingConv::C);
    let block = body.create_block();
    let context = body.add_block_param(block, Ty::Ptr);
    let output = body.add_block_param(block, Ty::Ptr);
    body.switch_to_block(block);
    let lanes = [
        context,
        body.uconst(Ty::U64, 1_u128 << 63),
        body.iconst(Ty::I64, -1),
        body.uconst(Ty::U64, 3),
        body.uconst(Ty::U64, 5),
    ];
    let mut bindings = vec![binding(context, pointer(16)), binding(output, pointer(80))];
    for ((index, ty), (value, scalar)) in [Ty::Ptr, Ty::U64, Ty::I64, Ty::U64, Ty::U64]
        .into_iter()
        .enumerate()
        .zip(
            lanes
                .into_iter()
                .zip([pointer(16), int(1_u64 << 63), int(u64::MAX), int(3), int(5)]),
        )
    {
        let address = body.gep_byte_offset(output, 8 * index as u64);
        body.store(ty, address, value);
        if index != 0 {
            bindings.push(binding(value, scalar));
        }
        bindings.push(binding(address, pointer(80 + 8 * index as u64)));
    }
    body.ret(vec![]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    let nodes = &module.functions[function.index() as usize].blocks[block.index() as usize].body;
    let pc = nodes.len() - 1;
    assert!(matches!(&nodes[pc].inst, Inst::Return { values } if values.is_empty()));
    let stores = nodes
        .iter()
        .filter_map(|node| match &node.inst {
            Inst::Store { ty, .. } => Some(ty.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(stores, vec![Ty::Ptr, Ty::U64, Ty::I64, Ty::U64, Ty::U64]);
    Fixture {
        module,
        function,
        block,
        pc,
        bindings,
        arguments: vec![],
        values: vec![],
    }
}

fn returning(arity: usize) -> Fixture {
    let mut builder = builder();
    let types = (0..arity)
        .map(|index| match index % 3 {
            0 => Ty::U64,
            1 => Ty::Ptr,
            _ => Ty::I64,
        })
        .collect::<Vec<_>>();
    let returns = types.iter().rev().cloned().collect();
    let signature = builder.add_func_type(types.clone(), returns);
    let function = builder.declare_function("return_arguments", signature);
    let mut body = builder.define_function(function).unwrap();
    body.set_calling_conv(CallingConv::Fast);
    let block = body.create_block();
    let arguments = types
        .into_iter()
        .map(|ty| body.add_block_param(block, ty))
        .collect::<Vec<_>>();
    body.switch_to_block(block);
    let values = (0..arity)
        .map(|index| match index % 3 {
            0 => int(1_u64 << 63),
            1 => pointer(80),
            _ => int(u64::MAX),
        })
        .collect::<Vec<_>>();
    let bindings = arguments
        .iter()
        .zip(&values)
        .map(|(id, value)| binding(*id, value.clone()))
        .collect();
    let arguments = arguments.into_iter().rev().collect::<Vec<_>>();
    let values = values.into_iter().rev().collect();
    body.ret(arguments.clone());
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    Fixture {
        module,
        function,
        block,
        pc: 0,
        bindings,
        arguments,
        values,
    }
}

fn candidate(
    assembler: &mut Assembler<'_>,
    f: &Fixture,
    site: &FetchedSite,
    target: &CallTarget,
    model: &MachineModel,
    frame: &RootReturnFrame,
    values: Expr,
) -> Result<RootReturnTransfer> {
    site.return_from_root(
        assembler,
        model,
        target,
        frame,
        f.resolved(model, frame, values.clone()),
        truth(site.root_return_admission(model, target, frame, values)?),
        truth(frame.current(model).valid(model)),
    )
}

#[test]
fn fetched_void_c2ptr_wrapper_suffix_retires_only_root_owner_and_preserves_output_words() {
    let f = wrapper_suffix();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let target = catalog.call_target(f.function).unwrap();
    let site = catalog.fetch(f.coordinate()).unwrap();
    let frame = f.frame();
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let transfer = candidate(
        &mut assembler,
        &f,
        &site,
        &target,
        &model,
        &frame,
        list("IRScalar", &[]),
    )
    .unwrap();
    drop(assembler);
    let expected = terminal(
        list("IRScalar", &[]),
        memory(false, true, false),
        37,
        &[],
        9,
    );
    replay(
        &scope,
        transfer.run().equality().term(),
        &eq(
            &model.config_type(),
            model.run(&NatTerm::literal(1), frame.current(&model).running(&model)),
            expected,
        ),
        true,
    );
    assert_eq!(transfer.run().fuel().term(), &nat(1));
    assert_eq!(transfer.run().reached(), transfer.halted());
    assert_eq!(transfer.values(), &list("IRScalar", &[]));
    assert_eq!(
        transfer.memory(),
        &app("ir_byte_retire_v1", [nat(8), frame.memory.clone()])
    );
    assert_eq!(transfer.world(), &frame.retired_world(&model));
}

#[test]
fn fetched_root_return_resolves_scalar_and_nonzero_arity_without_caller_destinations() {
    for arity in [1, 3, 7] {
        let f = returning(arity);
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let target = catalog.call_target(f.function).unwrap();
        let site = catalog.fetch(f.coordinate()).unwrap();
        let entry = catalog.entry(f.function).unwrap();
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let values = list("IRScalar", &f.values);
        // Here the fetched Ret IS the entry body. Compose actual ir_byte_init,
        // not an independently supplied interior current-state precondition.
        let input_memory = memory(false, true, false);
        let arguments = list(
            "IRScalar",
            &f.values.iter().rev().cloned().collect::<Vec<_>>(),
        );
        let initialized = entry
            .initialize(
                &mut assembler,
                &model,
                arguments.clone(),
                input_memory.clone(),
                nat(37),
                truth(EntryTarget::memory_admission(input_memory.clone())),
                truth(entry.admission(&model, arguments).unwrap()),
            )
            .unwrap();
        let owner = app("ir_byte_fresh_owner_v1", [input_memory.clone()]);
        let frame = RootReturnFrame {
            returning: initialized.current().frame.clone(),
            legacy_memory: initialized.current().legacy_memory.clone(),
            legacy_cursor: initialized.current().legacy_cursor.clone(),
            memory: input_memory,
            host: nat(37),
            owner: owner.clone(),
            next: app("Nat.succ", [owner]),
        };
        assert_eq!(
            frame.current(&model).running(&model),
            initialized.current().running(&model)
        );
        let transfer = site
            .return_from_root(
                &mut assembler,
                &model,
                &target,
                &frame,
                f.resolved(&model, &frame, values.clone()),
                truth(
                    site.root_return_admission(&model, &target, &frame, values.clone())
                        .unwrap(),
                ),
                initialized.valid().clone(),
            )
            .unwrap();
        let initial = initialized.equality().left().clone();
        let mapped = assembler
            .congruence(
                initialized.equality().clone(),
                model.config_type(),
                |state| model.run(&NatTerm::literal(1), state),
            )
            .unwrap();
        let start = assembler
            .conversion(
                model.config_type(),
                model.run(&NatTerm::literal(1), initial.clone()),
                mapped.left().clone(),
            )
            .unwrap();
        let end = assembler
            .conversion(
                model.config_type(),
                mapped.right().clone(),
                transfer.run().equality().left().clone(),
            )
            .unwrap();
        let full = assembler.compose(start, mapped).unwrap();
        let full = assembler.compose(full, end).unwrap();
        let full = assembler
            .compose(full, transfer.run().equality().clone())
            .unwrap();
        drop(assembler);
        // Initial allocation history already owns retired generations 7 and 8;
        // actual initialization therefore chooses 9 and keeps next=10 at halt.
        let expected = terminal(values, memory(false, true, false), 37, &[], 10);
        replay(
            &scope,
            full.term(),
            &eq(
                &model.config_type(),
                model.run(&NatTerm::literal(1), initial),
                expected,
            ),
            true,
        );
    }
}

#[test]
fn fetched_root_return_rejects_changed_return_values_final_memory_host_owners_and_next() {
    let f = returning(3);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let target = catalog.call_target(f.function).unwrap();
    let site = catalog.fetch(f.coordinate()).unwrap();
    let frame = f.frame();
    let values = list("IRScalar", &f.values);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let transfer = candidate(
        &mut assembler,
        &f,
        &site,
        &target,
        &model,
        &frame,
        values.clone(),
    )
    .unwrap();
    drop(assembler);
    replay(
        &scope,
        transfer.run().equality().term(),
        &transfer.run().equality().proposition(),
        true,
    );
    let mut wrong_values = f.values.clone();
    wrong_values[0] = int(2);
    let wrong = [
        terminal(
            list("IRScalar", &wrong_values),
            memory(false, true, false),
            37,
            &[],
            9,
        ),
        terminal(values.clone(), memory(true, true, false), 37, &[], 9),
        terminal(values.clone(), memory(false, false, false), 37, &[], 9),
        terminal(values.clone(), memory(false, true, true), 37, &[], 9),
        terminal(values.clone(), memory(false, true, false), 38, &[], 9),
        terminal(values.clone(), memory(false, true, false), 37, &[nat(8)], 9),
        terminal(values, memory(false, true, false), 37, &[], 10),
    ];
    for expected in wrong {
        replay(
            &scope,
            transfer.run().equality().term(),
            &eq(
                &model.config_type(),
                transfer.run().equality().left().clone(),
                expected,
            ),
            false,
        );
    }
}

#[test]
fn fetched_root_return_does_not_certify_forged_resolution_owner_destinations_or_site() {
    let f = returning(1);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let target = catalog.call_target(f.function).unwrap();
    let site = catalog.fetch(f.coordinate()).unwrap();
    for mutation in 0..4 {
        let mut frame = f.frame();
        let mut values = list("IRScalar", &f.values);
        match mutation {
            0 => values = list("IRScalar", &[int(7)]),
            1 => frame.owner = nat(7),
            2 | 3 => {
                // get_app_args retains borrowed fields until its SmallVec drops.
                // Finish the owned replacement before assigning the source.
                let returning = {
                    let fields = frame.returning.get_app_args();
                    app(
                        "IRFrame.mk",
                        [
                            fields[0].clone(),
                            fields[1].clone(),
                            if mutation == 3 {
                                nat(1)
                            } else {
                                fields[2].clone()
                            },
                            fields[3].clone(),
                            if mutation == 2 {
                                list("Nat", &[nat(99)])
                            } else {
                                fields[4].clone()
                            },
                        ],
                    )
                };
                frame.returning = returning;
            }
            _ => unreachable!(),
        }
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let transfer =
            candidate(&mut assembler, &f, &site, &target, &model, &frame, values).unwrap();
        drop(assembler);
        replay(
            &scope,
            transfer.run().equality().term(),
            &transfer.run().equality().proposition(),
            false,
        );
    }
}

#[test]
fn root_return_source_admission_refuses_wrong_opcode_target_and_premise_endpoints() {
    // Source admission is distinct from the kernel refusals above. No forged
    // evidence is credited merely because its proposition has the right shape.
    let f = wrapper_suffix();
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let target = catalog.call_target(f.function).unwrap();
    let site = catalog.fetch(f.coordinate()).unwrap();
    let non_return = catalog
        .fetch(Coordinate {
            instruction: 0,
            ..f.coordinate()
        })
        .unwrap();
    let frame = f.frame();
    let values = list("IRScalar", &[]);
    assert!(
        non_return
            .root_return_admission(&model, &target, &frame, values.clone())
            .is_err()
    );
    let mut wrong_target = target.clone();
    wrong_target.function_id = nat(u64::from(f.function.index()) + 1);
    assert!(
        site.root_return_admission(&model, &wrong_target, &frame, values.clone())
            .is_err()
    );
    for mutation in 0..4 {
        let mut resolved = f.resolved(&model, &frame, values.clone());
        let mut admitted = truth(
            site.root_return_admission(&model, &target, &frame, values.clone())
                .unwrap(),
        );
        let mut before = truth(frame.current(&model).valid(&model));
        match mutation {
            0 => resolved.left = list("IRScalar", &[]),
            1 => resolved.ty = constant("Nat"),
            2 => admitted.left = constant("Bool.true"),
            3 => before.left = constant("Bool.true"),
            _ => unreachable!(),
        }
        let mut scope = Scope::new();
        assert!(
            site.return_from_root(
                &mut Assembler::new(&mut scope, limits()).unwrap(),
                &model,
                &target,
                &frame,
                resolved,
                admitted,
                before
            )
            .is_err()
        );
    }
}

#[path = "core_execution_root_return_closed_tests.rs"]
mod closed_functions;
