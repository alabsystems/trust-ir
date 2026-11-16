// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Actual reflected callees and closed canonical ByteV1 candidates. No native
//! publication/provider grade follows from these logical proof controls.
use super::*;
use crate::core_reflection::reflect_core_module_v1;
use clean_kernel::BinderInfo;
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{
    Block, Endianness, FuncTy, FuncTyId, Function, InstrNode, StructPassingPolicy, TargetInfo,
};
fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}
fn limits() -> Limits {
    Limits {
        max_operations: 100_000,
        max_locals: 10_000,
        max_list_items: 1_000,
        max_lookup_candidates: 1_000,
        lookup_heartbeats: 2_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn addresses() -> [(FuncId, u64); 2] {
    [(FuncId::new(0), 4096), (FuncId::new(1), 8192)]
}
fn fixture() -> Module {
    let mut m = Module::new("readonly_indexed");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    m.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::U64],
        abi: None,
        is_vararg: false,
    });
    let mut callee = Function::new(
        FuncId::new(0),
        "read_word",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    callee.linkage = Linkage::Internal;
    callee.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: Ty::U64,
                ptr: ValueId::new(0),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    let mut caller = Function::new(FuncId::new(1), "caller", FuncTyId::new(0), BlockId::new(0));
    caller.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(10), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(10)],
            })
            .with_result(ValueId::new(11)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(11)],
            }),
        ],
    }];
    m.functions = vec![callee, caller];
    m
}
fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(&ty, right))
}
fn truth(left: Expr) -> PendingEquality {
    conversion(constant("Bool"), left, constant("Bool.true"))
}
fn bound(word: u64) -> PendingProof {
    PendingProof::candidate(
        app("Nat.lt", [nat(word), constant("ir_byte_limit_v1")]),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(word)]), nat(u64::MAX - word)],
        ),
    )
}
fn extent(base: u64, count: usize) -> PendingProof {
    let end = base + 8 * count as u64;
    PendingProof::candidate(
        app(
            "Nat.le",
            [
                app(
                    "Nat.add",
                    [nat(base), app("Nat.mul", [nat(8), nat(count as u64)])],
                ),
                constant("ir_byte_limit_v1"),
            ],
        ),
        app(
            "Nat.le_add_right",
            [nat(end), app("Nat.succ", [nat(u64::MAX - end)])],
        ),
    )
}
fn initial_memory_with_owner(live: bool, owner: u64) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[app(
                    "IRByteAllocationV1.mk",
                    [
                        nat(80),
                        nat(24),
                        nat(owner),
                        constant(if live { "Bool.true" } else { "Bool.false" }),
                    ],
                )],
            ),
            Expr::lam(
                BinderInfo::Default,
                constant("Nat"),
                app("IROption.none", [constant("Nat")]),
            ),
            nat(104),
        ],
    )
}
fn write(memory: Expr, address: Expr, word: Expr) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            app("ir_byte_mem_allocs_v1", [memory.clone()]),
            app(
                "ir_byte_write_word_v1",
                [
                    app("ir_byte_mem_bytes_v1", [memory.clone()]),
                    address,
                    nat(8),
                    word,
                ],
            ),
            app("ir_byte_mem_next_v1", [memory]),
        ],
    )
}
fn publication(a: &mut Assembler<'_>) -> InitializedEightRead {
    publication_with_live(a, true)
}
fn publication_with_live(a: &mut Assembler<'_>, live: bool) -> InitializedEightRead {
    publication_with_owner(a, live, 8)
}
fn publication_with_owner(a: &mut Assembler<'_>, live: bool, owner: u64) -> InitializedEightRead {
    let mut prefix = a
        .byte_initialized_eight_empty(initial_memory_with_owner(live, owner), nat(80))
        .unwrap();
    for (i, word) in [42u64, 43, 44].into_iter().enumerate() {
        let at = nat(80 + 8 * i as u64);
        let before = prefix.memory().clone();
        let after = write(before.clone(), at.clone(), nat(word));
        let adjacent = conversion(
            constant("Nat"),
            at.clone(),
            app(
                "Nat.add",
                [nat(80), app("Nat.mul", [nat(8), nat(i as u64)])],
            ),
        );
        let written = conversion(
            constant("IRByteMemoryV1"),
            after.clone(),
            write(before, at.clone(), nat(word)),
        );
        prefix = a
            .byte_initialized_eight_append(
                prefix,
                at,
                nat(word),
                after,
                InitializedEightAppendPremises {
                    adjacent,
                    written,
                    bounded_word: bound(word),
                    extent: extent(80, i + 1),
                },
            )
            .unwrap();
    }
    a.byte_initialized_eight_finish(prefix).unwrap()
}
fn replay(scope: &Scope, p: &PendingProof, accepted: bool) {
    let proposition = scope.close(p.proposition()).unwrap();
    let term = scope.close(p.term()).unwrap();
    let mut tc = TypeChecker::new(environment());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.set_heartbeat_limit(10_000_000);
    tc.set_max_cache_entries(200_000);
    if accepted {
        tc.check_type(&term, &proposition).unwrap();
        assert!(
            environment()
                .audit_certification(&proposition, &term)
                .is_certified()
        );
    } else {
        let error = tc
            .check_type(&term, &proposition)
            .expect_err("forged readonly candidate must fail actual typing");
        assert!(
            matches!(error, clean_kernel::KernelTypeError::TypeMismatch { .. }),
            "non-semantic refusal: {error:?}"
        );
    }
}
#[test]
fn readonly_callee_requires_exact_body_abi_and_module() {
    let m = fixture();
    let reflected = reflect_core_module_v1(&m, &addresses()).unwrap();
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let owner = catalog.readonly_eight_callee(FuncId::new(0)).unwrap();
    assert_eq!(owner.function_in(&m).unwrap(), FuncId::new(0));
    assert!(owner.function_in(&m.clone()).is_err());
    for mutation in 0..7 {
        let mut changed = fixture();
        let f = &mut changed.functions[0];
        match mutation {
            0 => f.linkage = Linkage::External,
            1 => f.calling_conv = CallingConv::Fast,
            2 => {
                if let Inst::Load { volatile, .. } = &mut f.blocks[0].body[0].inst {
                    *volatile = true;
                }
            }
            3 => {
                if let Inst::Load { align, .. } = &mut f.blocks[0].body[0].inst {
                    *align = Some(4);
                }
            }
            4 => {
                f.blocks[0].body.insert(
                    1,
                    InstrNode::new(Inst::Store {
                        ty: Ty::U64,
                        ptr: ValueId::new(0),
                        value: ValueId::new(1),
                        volatile: false,
                        align: Some(8),
                    }),
                );
            }
            5 => {
                f.blocks[0].body.insert(
                    1,
                    InstrNode::new(Inst::Call {
                        callee: FuncId::new(1),
                        args: vec![ValueId::new(0)],
                    })
                    .with_result(ValueId::new(2)),
                );
            }
            _ => {
                changed.func_types[0].is_vararg = true;
            }
        }
        if let Ok(reflected) = reflect_core_module_v1(&changed, &addresses()) {
            let mut c = Catalog::new(environment(), &reflected, limits()).unwrap();
            assert!(
                c.readonly_eight_callee(FuncId::new(0)).is_err(),
                "mutation {mutation}"
            );
        }
    }
}
#[test]
fn publication_slot_index_word_readback_is_independently_replayed() {
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let publication = publication(&mut a);
    for (i, word) in [42u64, 43, 44].into_iter().enumerate() {
        let selected = a.readonly_eight_selected(&publication, i).unwrap();
        let proof = conversion(
            app("IROption", [constant("Nat")]),
            selected,
            app("IROption.some", [constant("Nat"), nat(word)]),
        );
        let slot = a
            .readonly_eight_slot(&publication, i, nat(word), proof)
            .unwrap();
        assert_eq!(slot.index(), i);
    }
    assert!(a.readonly_eight_selected(&publication, 3).is_err());
    assert!(
        a.readonly_eight_slot(
            &publication,
            usize::MAX,
            nat(42),
            truth(constant("Bool.true"))
        )
        .is_err()
    );
    let good = a.readonly_eight_selected(&publication, 1).unwrap();
    let good = conversion(
        app("IROption", [constant("Nat")]),
        good,
        app("IROption.some", [constant("Nat"), nat(43)]),
    );
    let wrong = PendingProof::candidate(
        eq(
            &app("IROption", [constant("Nat")]),
            good.left().clone(),
            app("IROption.some", [constant("Nat"), nat(44)]),
        ),
        good.term().clone(),
    );
    let ready = publication.bounded_readback().unwrap();
    let _ = a;
    replay(&scope, &ready, true);
    replay(
        &scope,
        &PendingProof::candidate(good.proposition(), good.term().clone()),
        true,
    );
    replay(&scope, &wrong, false);
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
#[test]
fn readonly_indexed_defined_call_preserves_memory_host_and_caller_owner() {
    run_call("positive");
}
#[cfg(feature = "source-value-operational")]
#[test]
fn readonly_forward_entry_checks_actual_initialization_through_root_halt() {
    run_call("entry");
}
#[cfg(feature = "source-value-operational")]
#[test]
fn readonly_forward_entry_replays_independent_source_memory_read() {
    run_call("source-entry");
}
#[cfg(feature = "source-value-operational")]
#[test]
fn readonly_forward_entry_requires_the_original_complete_forwarding_caller() {
    for mutation in 0..7 {
        let mut module = fixture();
        match mutation {
            0 => module.functions[1].calling_conv = CallingConv::Fast,
            1 => {
                if let Inst::Call { args, .. } = &mut module.functions[1].blocks[0].body[0].inst {
                    args[0] = ValueId::new(99);
                }
            }
            2 => {
                if let Inst::Return { values } = &mut module.functions[1].blocks[0].body[1].inst {
                    values[0] = ValueId::new(10);
                }
            }
            3 => {
                let extra = module.functions[1].blocks[0].body[0].clone();
                module.functions[1].blocks[0].body.insert(1, extra);
            }
            4 => module.functions[1].blocks[0].params[0].1 = Ty::U64,
            5 => module.func_types[0].returns[0] = Ty::I64,
            _ => {
                if let Inst::Load { align, .. } = &mut module.functions[0].blocks[0].body[0].inst {
                    *align = Some(4);
                }
            }
        }
        if let Ok(reflected) = reflect_core_module_v1(&module, &addresses()) {
            let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
            assert!(
                catalog
                    .readonly_eight_forward_call(FuncId::new(1), FuncId::new(0))
                    .is_err(),
                "caller/leaf mutation {mutation}"
            );
        }
    }
}
#[test]
fn readonly_indexed_call_rejects_wrong_base_initialized_but_inaccessible_and_forged_word() {
    for mode in [
        "wrong-base",
        "inaccessible",
        "wrong-word",
        "wrong-caller-owner",
    ] {
        run_call(mode);
    }
}
#[cfg(feature = "source-value-operational")]
#[path = "../core_execution_readonly_licensed_tests.rs"]
mod licensed;
#[cfg(feature = "source-value-operational")]
#[test]
fn readonly_licensed_source_family_joins_complete_original_entry_and_effect() {
    run_call("licensed-entry");
}
fn run_call(mode: &str) {
    let entry_mode = matches!(mode, "entry" | "source-entry" | "licensed-entry");
    let mut module = fixture();
    #[cfg(feature = "source-value-operational")]
    if mode == "licensed-entry" {
        licensed::license(&mut module);
    }
    #[cfg(feature = "source-value-operational")]
    let report = if mode == "licensed-entry" {
        Some(crate::validate_module_with_config(
            &module,
            &crate::ValidationConfig::pinned()
                .with_bound_certificates(true)
                .with_source_bound_certificates(true)
                .with_gate_evidence(true),
        ))
    } else {
        None
    };
    #[cfg(feature = "source-value-operational")]
    let family = report
        .as_ref()
        .map(|r| crate::source_readonly_calls::check_readonly_source_family(r).unwrap());
    #[cfg(feature = "source-value-operational")]
    let reflected = if let Some(f) = &family {
        crate::source_readonly_calls::reflect_readonly_source_core_module_v1(f, &addresses())
            .unwrap()
    } else {
        reflect_core_module_v1(&module, &addresses()).unwrap()
    };
    #[cfg(not(feature = "source-value-operational"))]
    let reflected = reflect_core_module_v1(&module, &addresses()).unwrap();
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let callee = catalog.readonly_eight_callee(FuncId::new(0)).unwrap();
    let site = catalog
        .fetch(Coordinate {
            function: FuncId::new(1),
            block: BlockId::new(0),
            instruction: 0,
        })
        .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let publication = if entry_mode {
        // Entry begins with no live activations. Preserve the old suffix
        // fixture's owner8 separately; only a global allocation (owner0)
        // may already be live in this new complete-entry positive.
        publication_with_owner(&mut a, true, 0)
    } else {
        publication_with_live(&mut a, mode != "inaccessible")
    };
    let expected_word = if mode == "wrong-word" { 44 } else { 43 };
    let selected = a.readonly_eight_selected(&publication, 1).unwrap();
    let selected = conversion(
        app("IROption", [constant("Nat")]),
        selected,
        app("IROption.some", [constant("Nat"), nat(expected_word)]),
    );
    let slot = a
        .readonly_eight_slot(&publication, 1, nat(expected_word), selected)
        .unwrap();
    let pointer = app(
        "IRScalar.ptr_",
        [nat(if mode == "wrong-base" { 96 } else { 88 })],
    );
    let arguments = list("IRScalar", std::slice::from_ref(&pointer));
    let initialization = if entry_mode {
        let entry = catalog.entry(FuncId::new(1)).unwrap();
        let memory = publication.memory().clone();
        Some(
            entry
                .initialize(
                    &mut a,
                    &model,
                    arguments.clone(),
                    memory.clone(),
                    nat(37),
                    truth(EntryTarget::memory_admission(memory)),
                    truth(entry.admission(&model, arguments).unwrap()),
                )
                .unwrap(),
        )
    } else {
        None
    };
    let caller = initialization
        .as_ref()
        .map(|i| i.current().clone())
        .unwrap_or_else(|| Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(1),
                    nat(0),
                    nat(0),
                    list(
                        "IRBinding",
                        &[app("IRBinding.mk", [nat(10), pointer.clone()])],
                    ),
                    list("Nat", &[]),
                ],
            ),
            tail: list("IRFrame", &[]),
            legacy_memory: list("IRMemSlot", &[]),
            legacy_cursor: nat(1),
            world: app(
                "IRByteWorldV1.mk",
                [
                    constant("Nat"),
                    publication.memory().clone(),
                    nat(37),
                    list("Nat", &[nat(8)]),
                    nat(9),
                ],
            ),
        });
    let values = list("IRScalar", &[pointer]);
    let checks = callee
        .call_target()
        .checks(&model, &site, values.clone())
        .unwrap();
    let dispatch = callee
        .call_target()
        .call_target()
        .direct(&mut a, &model, &caller, &site)
        .unwrap();
    let resolved = conversion(
        app("IRList", [constant("IRScalar")]),
        app("ir_resolve", [caller.machine(), list("Nat", &[nat(10)])]),
        values,
    );
    let entered = callee
        .enter(
            &mut a,
            &model,
            &site,
            &caller,
            InternalCallPremises {
                dispatch,
                resolved,
                local_binding: conversion(
                    constant("Bool"),
                    checks.local_binding,
                    constant("Bool.false"),
                ),
                arity: truth(checks.arity),
                admitted: truth(checks.admitted),
                before: initialization
                    .as_ref()
                    .map(|i| i.valid().clone())
                    .unwrap_or_else(|| truth(caller.valid(&model))),
            },
        )
        .unwrap();
    let ty = app("IRTy.uint_", [nat(64)]);
    let layout = app(
        "IRByteLayoutV1.mk",
        [
            ty.clone(),
            nat(8),
            nat(8),
            list("IRTy", &[]),
            list("Nat", &[]),
        ],
    );
    let found = conversion(
        app("IROption", [constant("IRByteLayoutV1")]),
        app("ir_byte_layout_v1", [model.context().clone(), ty]),
        app("IROption.some", [constant("IRByteLayoutV1"), layout]),
    );
    let codec = a
        .byte_u64_codec(
            model.context().clone(),
            nat(expected_word),
            found,
            bound(expected_word),
        )
        .unwrap();
    let ptr = app("ir_getd", [entered.current().machine(), nat(0)]);
    let address = slot.address().clone();
    let align = app(
        "ir_byte_effective_align_v1",
        [
            nat(8),
            app("ir_byte_layout_align_v1", [codec.layout.clone()]),
        ],
    );
    let premises = ByteLoadEightPremises {
        pointer: conversion(
            app("IROption", [constant("Nat")]),
            app("ir_byte_pointer_address_v1", [ptr]),
            app("IROption.some", [constant("Nat"), address.clone()]),
        ),
        accessible: truth(app(
            "ir_byte_accessible_v1",
            [
                app("ir_byte_mem_allocs_v1", [publication.memory().clone()]),
                address.clone(),
                nat(8),
                align,
            ],
        )),
        initialized: conversion(
            app("IROption", [constant("Nat")]),
            app(
                "ir_byte_read_word_v1",
                [
                    app("ir_byte_mem_bytes_v1", [publication.memory().clone()]),
                    nat(8),
                    address,
                ],
            ),
            app("IROption.some", [constant("Nat"), nat(expected_word)]),
        ),
    };
    let loaded = entered.load(&mut a, &model, slot, codec, premises).unwrap();
    let (admission, retirement) = loaded.return_obligations(&model).unwrap();
    let retirement_arguments = retirement.get_app_args();
    let [_, retired, memory] = retirement_arguments.as_slice() else {
        panic!("retirement equality");
    };
    let retirement = conversion(
        constant("IRByteMemoryV1"),
        (*retired).clone(),
        (*memory).clone(),
    );
    if mode == "wrong-caller-owner" {
        let wrong = conversion(
            constant("IRByteMemoryV1"),
            app("ir_byte_retire_v1", [nat(8), publication.memory().clone()]),
            publication.memory().clone(),
        );
        assert!(
            loaded
                .finish(&mut a, &model, truth(admission), wrong)
                .is_err()
        );
        return;
    }
    let candidate = loaded
        .finish(&mut a, &model, truth(admission), retirement)
        .unwrap();
    assert_eq!(candidate.run.initial(), &caller.running(&model));
    #[cfg(feature = "source-value-operational")]
    if let Some(initialization) = initialization {
        let memory = publication.memory().clone();
        let owner = app("ir_byte_fresh_owner_v1", [memory.clone()]);
        let root = RootReturnFrame {
            returning: candidate.resumed.frame.clone(),
            legacy_memory: candidate.resumed.legacy_memory.clone(),
            legacy_cursor: candidate.resumed.legacy_cursor.clone(),
            memory: memory.clone(),
            host: nat(37),
            owner: owner.clone(),
            next: app("Nat.succ", [app("Nat.succ", [owner])]),
        };
        let returning = catalog
            .fetch(Coordinate {
                function: FuncId::new(1),
                block: BlockId::new(0),
                instruction: 1,
            })
            .unwrap();
        let target = catalog.call_target(FuncId::new(1)).unwrap();
        let values = list("IRScalar", &[app("IRScalar.int_", [nat(43)])]);
        let halted = returning
            .return_from_root(
                &mut a,
                &model,
                &target,
                &root,
                conversion(
                    app("IRList", [constant("IRScalar")]),
                    app(
                        "ir_resolve",
                        [root.current(&model).machine(), list("Nat", &[nat(11)])],
                    ),
                    values.clone(),
                ),
                truth(
                    returning
                        .root_return_admission(&model, &target, &root, values.clone())
                        .unwrap(),
                ),
                truth(root.current(&model).valid(&model)),
            )
            .unwrap();
        // The readonly suffix preserves memory by an explicit equality. Its
        // world and the literal root frame have equal normal forms, but are
        // not syntactically identical assembler endpoints. Keep that actual
        // transport in the proof before concatenating the fetched return.
        let returning = ExactRun::candidate(
            model.clone(),
            candidate.run.reached().clone(),
            halted.run().reached().clone(),
            halted.run().fuel().clone(),
            a.convert_endpoints(
                halted.run().equality().clone(),
                model.run(halted.run().fuel(), candidate.run.reached().clone()),
                halted.run().reached().clone(),
            )
            .unwrap(),
        )
        .unwrap();
        let run = a.concatenate(candidate.run, returning).unwrap();
        let terminal = app(
            "IRByteConfigV1.halted",
            [
                constant("Nat"),
                app("IROutcome.ret", [values]),
                app(
                    "IRByteWorldV1.mk",
                    [
                        constant("Nat"),
                        memory.clone(),
                        nat(37),
                        list("Nat", &[]),
                        root.next.clone(),
                    ],
                ),
            ],
        );
        let normalized = a
            .conversion(model.config_type(), run.reached().clone(), terminal)
            .unwrap();
        let equality = a.compose(run.equality().clone(), normalized).unwrap();
        let lifted = a
            .congruence_function(
                initialization.equality().clone(),
                model.config_type(),
                model.run_function(run.fuel()),
            )
            .unwrap();
        let lifted = a
            .convert_endpoints(
                lifted,
                model.run(run.fuel(), initialization.equality().left().clone()),
                equality.left().clone(),
            )
            .unwrap();
        let equality = a.compose(lifted, equality).unwrap();
        let owner = catalog
            .readonly_eight_forward_call(FuncId::new(1), FuncId::new(0))
            .unwrap();
        let _ = a;
        let proof = scope.close(equality.term()).unwrap();
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&proof).unwrap();
        let checked = owner
            .check_entry_proof(
                constant("Nat"),
                providers(),
                memory.clone(),
                nat(37),
                88,
                43,
                &bytes,
            )
            .unwrap();
        assert_eq!(
            checked.functions_in(&module).unwrap(),
            (FuncId::new(1), FuncId::new(0))
        );
        assert!(checked.functions_in(&module.clone()).is_err());
        assert_eq!(checked.logical_address(), 88);
        assert_eq!(checked.word(), 43);
        if mode == "licensed-entry" {
            let expected = app(
                "IRByteMemoryResultV1.value",
                [app("IRScalar.int_", [nat(43)]), memory.clone()],
            );
            let effect = trust_ir::proof::encode_clean_expr_dag_v2(&refl(
                &constant("IRByteMemoryResultV1"),
                expected,
            ))
            .unwrap();
            let joined = checked
                .check_source_family(family.as_ref().unwrap(), &effect)
                .unwrap();
            assert!(std::ptr::eq(joined.core_entry(), &checked));
            assert!(
                joined
                    .source_family()
                    .functions_in(&module.clone())
                    .is_err()
            );
            let wrong = app(
                "IRByteMemoryResultV1.value",
                [app("IRScalar.int_", [nat(44)]), memory.clone()],
            );
            let wrong = trust_ir::proof::encode_clean_expr_dag_v2(&refl(
                &constant("IRByteMemoryResultV1"),
                wrong,
            ))
            .unwrap();
            assert_eq!(
                checked
                    .check_source_family(family.as_ref().unwrap(), &wrong)
                    .err()
                    .unwrap(),
                "operational proof failed strict kernel checking"
            );
            let wrong_memory = app(
                "IRByteMemoryResultV1.value",
                [
                    app("IRScalar.int_", [nat(43)]),
                    write(memory.clone(), nat(88), nat(99)),
                ],
            );
            let wrong_memory = trust_ir::proof::encode_clean_expr_dag_v2(&refl(
                &constant("IRByteMemoryResultV1"),
                wrong_memory,
            ))
            .unwrap();
            assert_eq!(
                checked
                    .check_source_family(family.as_ref().unwrap(), &wrong_memory)
                    .err()
                    .unwrap(),
                "operational proof failed strict kernel checking"
            );
            let foreign_module = module.clone();
            let foreign_report = crate::validate_module_with_config(
                &foreign_module,
                &crate::ValidationConfig::pinned()
                    .with_bound_certificates(true)
                    .with_source_bound_certificates(true)
                    .with_gate_evidence(true),
            );
            let foreign_family =
                crate::source_readonly_calls::check_readonly_source_family(&foreign_report)
                    .unwrap();
            assert_eq!(
                checked
                    .check_source_family(&foreign_family, &effect)
                    .err()
                    .unwrap(),
                "readonly source family belongs to another original module"
            );
            if let Some(directory) = std::env::var_os("TRUST_IR_LICENSED_READONLY_PROOF_DIR") {
                let directory = std::path::PathBuf::from(directory);
                for (name, data) in [
                    ("entry.proof.dag", bytes.clone()),
                    (
                        "entry.goal.dag",
                        trust_ir::proof::encode_clean_expr_dag_v2(checked.judgment()).unwrap(),
                    ),
                    ("effect.proof.dag", effect.clone()),
                    (
                        "effect.goal.dag",
                        trust_ir::proof::encode_clean_expr_dag_v2(joined.effect_judgment())
                            .unwrap(),
                    ),
                    (
                        "source.island",
                        family
                            .as_ref()
                            .unwrap()
                            .source_island()
                            .declarations
                            .clone(),
                    ),
                    (
                        "original-module.bin",
                        trust_ir::binary::serialize_module(&module).unwrap(),
                    ),
                ] {
                    std::fs::write(directory.join(name), data).unwrap();
                }
            }
            assert!(
                checked
                    .check_source_family(family.as_ref().unwrap(), &[])
                    .is_err()
            );
            return;
        }
        if mode == "source-entry" {
            check_independent_source_read(&checked, &module);
            return;
        }
        if let Some(directory) = std::env::var_os("TRUST_IR_READONLY_PROOF_DIR") {
            let directory = std::path::PathBuf::from(directory);
            std::fs::write(directory.join("readonly-entry.proof.dag"), &bytes).unwrap();
            std::fs::write(
                directory.join("readonly-entry.goal.dag"),
                trust_ir::proof::encode_clean_expr_dag_v2(checked.judgment()).unwrap(),
            )
            .unwrap();
        }
        let orphaned = truth(EntryTarget::memory_admission(initial_memory_with_owner(
            true, 8,
        )));
        replay(
            &scope,
            &PendingProof::candidate(orphaned.proposition(), orphaned.term().clone()),
            false,
        );
        for (address, word, host, changed_memory) in [
            (96, 43, 37, memory.clone()),
            (88, 44, 37, memory.clone()),
            (88, 43, 38, memory.clone()),
            (88, 43, 37, write(memory.clone(), nat(88), nat(99))),
        ] {
            assert!(
                owner
                    .check_entry_proof(
                        constant("Nat"),
                        providers(),
                        changed_memory,
                        nat(host),
                        address,
                        word,
                        &bytes
                    )
                    .is_err()
            );
        }
        return;
    }
    let _ = a;
    replay(&scope, &candidate.publication_and_run, mode == "positive");
}

#[cfg(feature = "source-value-operational")]
fn check_independent_source_read(checked: &CheckedReadonlyEightCallEntry<'_>, module: &Module) {
    use clean_kernel::{ConstantKind, Declaration};
    use trust_ir::proof::{IslandEnvironment, SourceDefinitionRef, encode_island_declarations_v1};
    let source_type = Expr::pi(
        BinderInfo::Default,
        constant("IRByteMemoryV1"),
        Expr::pi(BinderInfo::Default, constant("Nat"), constant("Nat")),
    );
    // Independently authored byte read, with an explicit zero on uninitialized
    // source input. The complete Core proof separately establishes accessible,
    // initialized storage for this exact point. No Core body is reified here.
    let body = Expr::apps(
        Expr::const_(
            Name::from_string("IROption.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            constant("Nat"),
            Expr::lam(
                BinderInfo::Default,
                app("IROption", [constant("Nat")]),
                constant("Nat"),
            ),
            nat(0),
            Expr::lam(BinderInfo::Default, constant("Nat"), Expr::bvar(0)),
            app(
                "ir_byte_read_word_v1",
                [
                    app("ir_byte_mem_bytes_v1", [Expr::bvar(1)]),
                    nat(8),
                    Expr::bvar(0),
                ],
            ),
        ],
    );
    let value = Expr::lam(
        BinderInfo::Default,
        constant("IRByteMemoryV1"),
        Expr::lam(BinderInfo::Default, constant("Nat"), body),
    );
    let declaration = |value| Declaration::Definition {
        name: Name::from_string("Source.readWord"),
        level_params: vec![],
        type_: source_type.clone(),
        value,
        is_reducible: true,
    };
    let island = |declarations: &[Declaration]| {
        IslandEnvironment::new(encode_island_declarations_v1(declarations).unwrap())
    };
    let selected = |island: &IslandEnvironment| SourceDefinitionRef {
        decl: "Source.readWord".into(),
        closure_digest: island.digest,
    };
    let original = island(&[declaration(value)]);
    let selection = selected(&original);
    let source = checked
        .check_source_definition(&original, &selection)
        .unwrap();
    assert!(std::ptr::eq(source.core_entry(), checked));
    assert_eq!(
        source.core_entry().functions_in(module).unwrap(),
        (FuncId::new(1), FuncId::new(0))
    );
    assert!(source.core_entry().functions_in(&module.clone()).is_err());
    assert_eq!(source.source(), &selection);
    assert_eq!(
        source
            .environment()
            .get_const(&Name::from_string("Source.readWord"))
            .unwrap()
            .kind,
        ConstantKind::Definition
    );
    crate::source_value_operational::strict_replay(
        source.environment(),
        source.judgment(),
        source.proof(),
    )
    .unwrap();
    let wrong = island(&[declaration(Expr::lam(
        BinderInfo::Default,
        constant("IRByteMemoryV1"),
        Expr::lam(BinderInfo::Default, constant("Nat"), nat(44)),
    ))]);
    assert!(
        checked
            .check_source_definition(&wrong, &selected(&wrong))
            .is_err()
    );
    assert!(checked.check_source_definition(&wrong, &selection).is_err());
    let mut absent = selection.clone();
    absent.decl = "Source.absent".into();
    assert!(checked.check_source_definition(&original, &absent).is_err());
    let axiom = island(&[Declaration::Axiom {
        name: Name::from_string("Source.readWord"),
        level_params: vec![],
        type_: source_type.clone(),
    }]);
    assert!(
        checked
            .check_source_definition(&axiom, &selected(&axiom))
            .is_err()
    );
    let shadow = island(&[Declaration::Definition {
        name: Name::from_string("ir_byte_read_word_v1"),
        level_params: vec![],
        type_: constant("Nat"),
        value: nat(43),
        is_reducible: true,
    }]);
    let mut shadow_selection = selected(&shadow);
    shadow_selection.decl = "ir_byte_read_word_v1".into();
    assert!(
        checked
            .check_source_definition(&shadow, &shadow_selection)
            .is_err()
    );
    let wrong_type = island(&[Declaration::Definition {
        name: Name::from_string("Source.readWord"),
        level_params: vec![],
        type_: constant("Nat"),
        value: nat(43),
        is_reducible: true,
    }]);
    assert!(
        checked
            .check_source_definition(&wrong_type, &selected(&wrong_type))
            .is_err()
    );
    if let Some(directory) = std::env::var_os("TRUST_IR_READONLY_PROOF_DIR") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::write(
            directory.join("readonly-source-entry.proof.dag"),
            trust_ir::proof::encode_clean_expr_dag_v2(source.proof()).unwrap(),
        )
        .unwrap();
        std::fs::write(
            directory.join("readonly-source-entry.goal.dag"),
            trust_ir::proof::encode_clean_expr_dag_v2(source.judgment()).unwrap(),
        )
        .unwrap();
        std::fs::write(
            directory.join("readonly-source-entry.island"),
            &original.declarations,
        )
        .unwrap();
    }
}
