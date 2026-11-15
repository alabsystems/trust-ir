// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
use super::*;
use crate::core_reflection::reflect_core_module_v1;
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{
    Block, Endianness, FuncTy, FuncTyId, Function, InstrNode, StructPassingPolicy, TargetInfo,
};

pub(super) fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}
pub(super) fn limits() -> Limits {
    Limits {
        max_operations: 100_000,
        max_locals: 10_000,
        max_list_items: 1_000,
        max_lookup_candidates: 1_000,
        lookup_heartbeats: 2_000_000,
        lookup_cache_entries: 100_000,
    }
}
pub(super) fn addresses() -> [(FuncId, u64); 2] {
    [(FuncId::new(0), 4096), (FuncId::new(1), 8192)]
}
pub(super) fn fixture(ty: Ty, word: u64) -> Module {
    let mut m = Module::new("original_defined_constant_call");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("darwinpcs".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    m.func_types.push(FuncTy {
        params: vec![],
        returns: vec![ty.clone()],
        abi: None,
        is_vararg: false,
    });
    let mut leaf = Function::new(
        FuncId::new(0),
        "constant_leaf",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    leaf.linkage = Linkage::Internal;
    leaf.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty,
                value: Constant::Int(i128::from(word)),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    let mut caller = Function::new(
        FuncId::new(1),
        "real_caller",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    caller.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![],
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(7)],
            }),
        ],
    }];
    m.functions = vec![leaf, caller];
    m
}
pub(super) fn memory(owned: bool) -> Expr {
    let allocs = if owned {
        vec![app(
            "IRByteAllocationV1.mk",
            [nat(80), nat(8), nat(8), constant("Bool.true")],
        )]
    } else {
        vec![]
    };
    app(
        "IRByteMemoryV1.mk",
        [
            list("IRByteAllocationV1", &allocs),
            Expr::lam(
                BinderInfo::Default,
                constant("Nat"),
                app("IROption.none", [constant("Nat")]),
            ),
            nat(if owned { 88 } else { 1 }),
        ],
    )
}
pub(super) fn providers() -> Expr {
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
pub(super) fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(&ty, right))
}
pub(super) fn truth(left: Expr) -> PendingEquality {
    conversion(constant("Bool"), left, constant("Bool.true"))
}
fn replay(scope: &Scope, proof: &Expr, claim: &Expr, accepted: bool) {
    let proof = scope.close(proof).unwrap();
    let claim = scope.close(claim).unwrap();
    assert!(!proof.has_fvar_quick() && !claim.has_fvar_quick());
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(20_000_000);
    checker.set_max_cache_entries(200_000);
    if accepted {
        checker.check_type(&proof, &claim).unwrap();
        let audit = environment().audit_certification(&claim, &proof);
        assert!(audit.is_certified(), "{audit:#?}");
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&proof).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
        assert_eq!(decoded, proof);
        checker.check_type(&decoded, &claim).unwrap();
        assert!(
            environment()
                .audit_certification(&claim, &decoded)
                .is_certified()
        );
    } else {
        let error = checker
            .check_type(&proof, &claim)
            .expect_err("forged complete caller proof must refuse");
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "nonsemantic refusal: {error:?}"
        );
    }
}

#[test]
fn original_two_function_call_and_return_reaches_exact_word_and_world() {
    for (ty, word) in [(Ty::U64, 41), (Ty::I64, 43)] {
        run(ty, word, false, false);
    }
}

#[test]
fn actual_initializer_and_complete_caller_preserve_live_foreign_bytes_and_host() {
    for (ty, word) in [(Ty::U64, 41), (Ty::I64, 43)] {
        initialized_entry_case(ty, word);
    }
}

fn initialized_entry_case(ty: Ty, word: u64) {
    let module = fixture(ty.clone(), word);
    let reflected = reflect_core_module_v1(&module, &addresses()).unwrap();
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let owner = catalog
        .defined_constant_call(FuncId::new(1), FuncId::new(0))
        .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    // A real live global allocation and its initialized bytes survive both
    // activation retirements. They grant no native allocation permission.
    let empty_bytes = Expr::lam(
        BinderInfo::Default,
        constant("Nat"),
        app("IROption.none", [constant("Nat")]),
    );
    let mem = app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[app(
                    "IRByteAllocationV1.mk",
                    [nat(80), nat(8), nat(0), constant("Bool.true")],
                )],
            ),
            app(
                "ir_byte_write_word_v1",
                [empty_bytes, nat(80), nat(8), nat(99)],
            ),
            nat(88),
        ],
    );
    let root = owner.entry_root(mem.clone(), nat(37));
    let retire = |who: Expr| {
        conversion(
            constant("IRByteMemoryV1"),
            app("ir_byte_retire_v1", [who, mem.clone()]),
            mem.clone(),
        )
    };
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let candidate = owner
        .execute_entry(
            &mut a,
            &model,
            mem.clone(),
            nat(37),
            truth(EntryTarget::memory_admission(mem.clone())),
            truth(owner.entry_admission(&model).unwrap()),
            retire(root.next.clone()),
            retire(root.owner.clone()),
        )
        .unwrap();
    let initial = app(
        "ir_byte_init_v1",
        [
            constant("Nat"),
            reflected.context_term().clone(),
            nat(1),
            list("IRScalar", &[]),
            mem.clone(),
            nat(37),
        ],
    );
    let expected_world = app(
        "IRByteWorldV1.mk",
        [
            constant("Nat"),
            mem.clone(),
            nat(37),
            list("Nat", &[]),
            nat(3),
        ],
    );
    let expected = app(
        "IRByteConfigV1.halted",
        [
            constant("Nat"),
            app(
                "IROutcome.ret",
                [list("IRScalar", &[app("IRScalar.int_", [nat(word)])])],
            ),
            expected_world,
        ],
    );
    let claim = eq(
        &model.config_type(),
        model.run(&NatTerm::literal(4), initial),
        expected,
    );
    replay(&scope, candidate.run.equality().term(), &claim, true);
    #[cfg(feature = "source-value-operational")]
    {
        let proof = scope.close(candidate.run.equality().term()).unwrap();
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&proof).unwrap();
        let checked = owner
            .check_entry_proof(constant("Nat"), providers(), mem.clone(), nat(37), &bytes)
            .unwrap();
        assert_eq!(checked.word(), word);
        assert_eq!(
            checked.functions_in(&module).unwrap(),
            (FuncId::new(1), FuncId::new(0))
        );
        assert!(checked.functions_in(&module.clone()).is_err());
        // Independent assertion: the admitted proposition is the original
        // initializer/run-four/halt claim, not candidate.run's stored endpoints.
        let mut checker = TypeChecker::new(environment());
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker
            .check_type(checked.proof(), &scope.close(&claim).unwrap())
            .unwrap();
        assert!(
            environment()
                .audit_certification(checked.judgment(), checked.proof())
                .is_certified()
        );
        let semantic_refusal = |error: String| {
            assert_eq!(
                error, "operational proof failed strict kernel checking",
                "resource limits, malformed terms and claim typing are not semantic negatives"
            );
        };
        semantic_refusal(
            owner
                .check_entry_proof(constant("Nat"), providers(), mem.clone(), nat(38), &bytes)
                .err()
                .expect("the original closed proof cannot change HOST"),
        );
        semantic_refusal(
            owner
                .check_entry_proof(constant("Nat"), providers(), memory(false), nat(37), &bytes)
                .err()
                .expect("the original closed proof cannot replace live initialized memory"),
        );
        let malformed = owner
            .check_entry_proof(
                constant("Nat"),
                providers(),
                mem.clone(),
                nat(37),
                &[0, 1, 2],
            )
            .err()
            .expect("malformed codec must refuse");
        assert!(
            malformed.starts_with("defined call proof codec:"),
            "{malformed}"
        );
        let open = trust_ir::proof::encode_clean_expr_dag_v2(&Expr::bvar(0)).unwrap();
        let loose = owner
            .check_entry_proof(constant("Nat"), providers(), mem.clone(), nat(37), &open)
            .err()
            .expect("loose proof binders cannot become an admitted owner");
        assert_eq!(loose, "open or metavariable operational source-value claim");
        let changed = fixture(ty, word + 1);
        let other_reflected = reflect_core_module_v1(&changed, &addresses()).unwrap();
        let mut other_catalog = Catalog::new(environment(), &other_reflected, limits()).unwrap();
        let other = other_catalog
            .defined_constant_call(FuncId::new(1), FuncId::new(0))
            .unwrap();
        semantic_refusal(
            other
                .check_entry_proof(constant("Nat"), providers(), mem, nat(37), &bytes)
                .err()
                .expect("an old source/body/result proof cannot certify the changed literal"),
        );
    }
}
#[test]
fn complete_caller_refuses_forged_return_value_and_root_owner_retirement() {
    run(Ty::U64, 41, true, false);
    run(Ty::U64, 41, false, true);
}
fn run(ty: Ty, word: u64, wrong_result: bool, owned_allocation: bool) {
    let module = fixture(ty, word);
    assert!(crate::validate_module(&module).is_empty());
    let reflected = reflect_core_module_v1(&module, &addresses()).unwrap();
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let owner = catalog
        .defined_constant_call(FuncId::new(1), FuncId::new(0))
        .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mem = memory(owned_allocation);
    let root = owner.root(mem.clone(), nat(37), nat(8), nat(9));
    let retire = |who| {
        conversion(
            constant("IRByteMemoryV1"),
            app("ir_byte_retire_v1", [nat(who), mem.clone()]),
            mem.clone(),
        )
    };
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let candidate = owner
        .execute_root(
            &mut a,
            &model,
            &root,
            truth(root.current(&model).valid(&model)),
            retire(9),
            retire(8),
        )
        .unwrap();
    // Independently reconstruct the complete claim from the ORIGINAL caller
    // coordinates and specified result/world, not the candidate's endpoints.
    let frame = app(
        "IRFrame.mk",
        [
            nat(1),
            nat(0),
            nat(0),
            list("IRBinding", &[]),
            list("Nat", &[]),
        ],
    );
    let initial = Current {
        frame,
        tail: list("IRFrame", &[]),
        legacy_memory: list("IRMemSlot", &[]),
        legacy_cursor: nat(0),
        world: app(
            "IRByteWorldV1.mk",
            [
                constant("Nat"),
                mem.clone(),
                nat(37),
                list("Nat", &[nat(8)]),
                nat(9),
            ],
        ),
    };
    let result = app("IRScalar.int_", [nat(word + u64::from(wrong_result))]);
    let world = app(
        "IRByteWorldV1.mk",
        [constant("Nat"), mem, nat(37), list("Nat", &[]), nat(10)],
    );
    let final_config = app(
        "IRByteConfigV1.halted",
        [
            constant("Nat"),
            app("IROutcome.ret", [list("IRScalar", &[result])]),
            world,
        ],
    );
    let claim = eq(
        &model.config_type(),
        model.run(&NatTerm::literal(4), initial.running(&model)),
        final_config,
    );
    replay(
        &scope,
        candidate.run.equality().term(),
        &claim,
        !wrong_result && !owned_allocation,
    );
}

#[test]
fn defined_constant_call_refuses_foreign_original_body_abi_and_coordinates() {
    let module = fixture(Ty::U64, 41);
    let reflected = reflect_core_module_v1(&module, &addresses()).unwrap();
    let mut c = Catalog::new(environment(), &reflected, limits()).unwrap();
    let owner = c
        .defined_constant_call(FuncId::new(1), FuncId::new(0))
        .unwrap();
    assert_eq!(
        owner.functions_in(&module).unwrap(),
        (FuncId::new(1), FuncId::new(0))
    );
    assert!(owner.functions_in(&module.clone()).is_err());
    assert!(
        c.defined_constant_call(FuncId::new(0), FuncId::new(1))
            .is_err()
    );
    for mutation in 0..8 {
        let mut m = fixture(Ty::U64, 41);
        match mutation {
            0 => m.functions[0].calling_conv = CallingConv::Fast,
            1 => m.functions[0].linkage = Linkage::External,
            2 => m.func_types[0].is_vararg = true,
            3 => {
                m.functions[1].blocks[0].body[0].inst = Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![],
                }
            }
            4 => {
                m.functions[1].blocks[0].body[1].inst = Inst::Return {
                    values: vec![ValueId::new(3)],
                }
            }
            5 => m.functions[0].blocks[0].body[1].inst = Inst::Return { values: vec![] },
            6 => m.functions[1].blocks[0].body.insert(
                0,
                InstrNode::new(Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(41),
                })
                .with_result(ValueId::new(19)),
            ),
            _ => {
                m.functions[0].blocks[0].body[0].inst = Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(true),
                }
            }
        }
        if let Ok(r) = reflect_core_module_v1(&m, &addresses()) {
            let mut c = Catalog::new(environment(), &r, limits()).unwrap();
            assert!(
                c.defined_constant_call(FuncId::new(1), FuncId::new(0))
                    .is_err(),
                "mutation{mutation}"
            );
        }
    }
}

#[test]
fn complete_caller_keeps_exact_memory_owner_and_module_premise_endpoints() {
    let module = fixture(Ty::U64, 41);
    let r = reflect_core_module_v1(&module, &addresses()).unwrap();
    let foreign_module = module.clone();
    let foreign = reflect_core_module_v1(&foreign_module, &addresses()).unwrap();
    let mut c = Catalog::new(environment(), &r, limits()).unwrap();
    let owner = c
        .defined_constant_call(FuncId::new(1), FuncId::new(0))
        .unwrap();
    let root = owner.root(memory(false), nat(37), nat(8), nat(9));
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let model = MachineModel::new(constant("Nat"), &r, providers());
    let retire = |who| {
        conversion(
            constant("IRByteMemoryV1"),
            app("ir_byte_retire_v1", [nat(who), memory(false)]),
            memory(false),
        )
    };
    assert!(
        owner
            .execute_root(
                &mut a,
                &model,
                &root,
                truth(root.current(&model).valid(&model)),
                retire(9),
                retire(7)
            )
            .is_err()
    );
    // A foreign model with the same reflected data has equal logical context;
    // immutable module borrowing is checked by functions_in, not a hash claim.
    assert!(owner.functions_in(foreign.module()).is_err());
    let mut wrong = root.clone();
    wrong.returning = app(
        "IRFrame.mk",
        [
            nat(0),
            nat(0),
            nat(0),
            list("IRBinding", &[]),
            list("Nat", &[]),
        ],
    );
    assert!(
        owner
            .execute_root(
                &mut a,
                &model,
                &wrong,
                truth(wrong.current(&model).valid(&model)),
                retire(9),
                retire(8)
            )
            .is_err()
    );
}

#[cfg(feature = "source-value-operational")]
fn source_call_fixture(
    source_leaf: Expr,
) -> Result<(
    Module,
    trust_ir::proof::IslandEnvironment,
    trust_ir::proof::SourceDefinitionRef,
    trust_ir::proof::SourceDefinitionRef,
)> {
    source_call_fixture_named(source_leaf, "DefinedCalls.leaf", "DefinedCalls.entry")
}

#[cfg(feature = "source-value-operational")]
fn source_call_fixture_named(
    source_leaf: Expr,
    leaf_name: &str,
    caller_name: &str,
) -> Result<(
    Module,
    trust_ir::proof::IslandEnvironment,
    trust_ir::proof::SourceDefinitionRef,
    trust_ir::proof::SourceDefinitionRef,
)> {
    use clean_kernel::Declaration;
    use trust_ir::proof::*;
    let mut module = fixture(Ty::U64, 42);
    module.name = "independent_defined_call_family".into();
    module.functions[0].name = "leaf".into();
    module.functions[1].name = "entry".into();
    // Source declarations are independently authored; no IR denotation or
    // returned result supplies either definition. The caller references leaf.
    let definition = |name: &str, value| Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: constant("Nat"),
        value,
        is_reducible: true,
    };
    let island = IslandEnvironment::new(encode_island_declarations_v1(&[
        definition(leaf_name, source_leaf),
        definition(caller_name, constant(leaf_name)),
    ])?);
    let source = |name: &str| SourceDefinitionRef {
        decl: name.into(),
        closure_digest: island.digest,
    };
    let caller = source(caller_name);
    let callee = source(leaf_name);
    let family = crate::certify_source_bound_call_family(
        &module,
        ProofLineageId::new(0),
        trust_ir::value::ProofId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "source-defined-calls",
            "operational-consumer",
            "1",
        ),
        &island,
        &[
            (FuncId::new(1), caller.clone()),
            (FuncId::new(0), callee.clone()),
        ],
    )?;
    let gates = module
        .functions
        .iter()
        .map(|function| {
            let obligation = family
                .obligations
                .iter()
                .find(|row| row.function == Some(function.id))
                .unwrap();
            (
                function.id,
                trust_ir::GateEvidence {
                    obligation: obligation.id,
                    body_digest: module.function_body_digest(function.id).unwrap(),
                },
            )
        })
        .collect::<Vec<_>>();
    for (function, evidence) in gates {
        module
            .functions
            .iter_mut()
            .find(|f| f.id == function)
            .unwrap()
            .body_gate = Some(trust_ir::BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: Some(evidence),
        });
    }
    module.proof_obligations.extend(family.obligations);
    module.proof_certificates.extend(family.certificates);
    Ok((module, island, caller, callee))
}

#[cfg(feature = "source-value-operational")]
#[test]
fn source_call_whole_entry_joins_actual_island_and_original_core_module() {
    use crate::source_call_operational::check_source_bound_defined_constant_call_entry as join_source;
    let configuration = crate::ValidationConfig::pinned()
        .with_bound_certificates(true)
        .with_source_bound_certificates(true)
        .with_gate_evidence(true);
    // The computed independent source control cannot pass by extracting or
    // comparing a literal 42 in Rust. Both exact original source bodies replay.
    for (case, source_leaf) in [nat(42), app("Nat.add", [nat(20), nat(22)])]
        .into_iter()
        .enumerate()
    {
        let (module, island, caller_source, callee_source) =
            source_call_fixture(source_leaf).unwrap();
        let report = crate::validate_module_with_config(&module, &configuration);
        assert!(report.is_ok(), "{:?}", report.errors());
        assert!(
            reflect_core_module_v1(&module, &addresses()).is_err(),
            "raw proof-table refusal must remain"
        );
        let reflected = crate::source_call_operational::reflect_source_call_core_module_v1(
            &report,
            &addresses(),
        )
        .unwrap();
        assert!(std::ptr::eq(reflected.module(), &module));
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let owner = catalog
            .defined_constant_call(FuncId::new(1), FuncId::new(0))
            .unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mem = memory(false);
        let root = owner.entry_root(mem.clone(), nat(37));
        let retire = |who: Expr| {
            conversion(
                constant("IRByteMemoryV1"),
                app("ir_byte_retire_v1", [who, mem.clone()]),
                mem.clone(),
            )
        };
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let candidate = owner
            .execute_entry(
                &mut a,
                &model,
                mem.clone(),
                nat(37),
                truth(EntryTarget::memory_admission(mem.clone())),
                truth(owner.entry_admission(&model).unwrap()),
                retire(root.next.clone()),
                retire(root.owner.clone()),
            )
            .unwrap();
        let proposed = scope.close(candidate.run.equality().term()).unwrap();
        let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&proposed).unwrap();
        let core = owner
            .check_entry_proof(constant("Nat"), providers(), mem.clone(), nat(37), &encoded)
            .unwrap();
        let joined = join_source(&report, &core, &island, &caller_source, &callee_source).unwrap();
        if case == 0 {
            // The original TV anchor permits this independent source name;
            // canonical ByteV1 already gives it a different declaration.
            // Mint a NEW Core receipt for this actual module: proposed bytes
            // are rechecked, never cast into a foreign receipt's custody.
            let (shadow, shadow_island, shadow_caller, shadow_callee) =
                source_call_fixture_named(nat(42), "DefinedCalls.leaf", "ir_byte_run_v1").unwrap();
            let shadow_report = crate::validate_module_with_config(&shadow, &configuration);
            assert!(shadow_report.is_ok(), "{:?}", shadow_report.errors());
            let shadow_reflected =
                crate::source_call_operational::reflect_source_call_core_module_v1(
                    &shadow_report,
                    &addresses(),
                )
                .unwrap();
            let mut shadow_catalog =
                Catalog::new(environment(), &shadow_reflected, limits()).unwrap();
            let shadow_owner = shadow_catalog
                .defined_constant_call(FuncId::new(1), FuncId::new(0))
                .unwrap();
            let shadow_core = shadow_owner
                .check_entry_proof(constant("Nat"), providers(), mem.clone(), nat(37), &encoded)
                .unwrap();
            let shadow_error = join_source(
                &shadow_report,
                &shadow_core,
                &shadow_island,
                &shadow_caller,
                &shadow_callee,
            )
            .err()
            .unwrap();
            assert_eq!(
                shadow_error.0,
                "original source/environment collision: ir_byte_run_v1"
            );
        }

        assert_eq!(
            joined.functions_in(&module).unwrap(),
            (FuncId::new(1), FuncId::new(0))
        );
        assert_eq!(joined.source(), &caller_source);
        assert!(joined.functions_in(&module.clone()).is_err());
        let mut reads = std::collections::HashSet::new();
        joined.judgment().collect_kernel_reads_into(&mut reads);
        assert!(
            reads.contains(&Name::from_string("DefinedCalls.entry")),
            "source constant must remain in the theorem"
        );
        let semantic = |goal: Expr| {
            let error = crate::source_value_operational::strict_replay(
                joined.environment(),
                &goal,
                joined.proof(),
            )
            .unwrap_err();
            assert_eq!(
                error, "operational proof failed strict kernel checking",
                "nonsemantic negative: {error}"
            );
        };
        // False source result and false HOST are checked as complete queries;
        // codec, scope or budget failures cannot satisfy these controls.
        semantic(
            core.entry_claim_with_word(app("Nat.add", [constant("DefinedCalls.entry"), nat(1)])),
        );
        let wrong_initial = app(
            "ir_byte_init_v1",
            [
                constant("Nat"),
                reflected.context_term().clone(),
                nat(1),
                list("IRScalar", &[]),
                mem.clone(),
                nat(38),
            ],
        );
        let original_world = app(
            "IRByteWorldV1.mk",
            [
                constant("Nat"),
                mem.clone(),
                nat(37),
                list("Nat", &[]),
                nat(3),
            ],
        );
        let source_halt = app(
            "IRByteConfigV1.halted",
            [
                constant("Nat"),
                app(
                    "IROutcome.ret",
                    [list(
                        "IRScalar",
                        &[app("IRScalar.int_", [constant("DefinedCalls.entry")])],
                    )],
                ),
                original_world,
            ],
        );
        semantic(eq(
            &model.config_type(),
            model.run(&NatTerm::literal(4), wrong_initial),
            source_halt,
        ));
        let clone = module.clone();
        let cloned_report = crate::validate_module_with_config(&clone, &configuration);
        let foreign = join_source(
            &cloned_report,
            &core,
            &island,
            &caller_source,
            &callee_source,
        )
        .err()
        .unwrap();
        assert_eq!(
            foreign.0,
            "checked defined call belongs to another immutable module"
        );
        let wrong_selector = join_source(&report, &core, &island, &callee_source, &caller_source)
            .err()
            .unwrap();
        assert_eq!(
            wrong_selector.0,
            "source-call selection differs from the replayed original binding"
        );
        let (_, foreign_island, _, _) = source_call_fixture(nat(42)).unwrap();
        if foreign_island != island {
            let wrong = join_source(
                &report,
                &core,
                &foreign_island,
                &caller_source,
                &callee_source,
            )
            .err()
            .unwrap();
            assert_eq!(
                wrong.0,
                "source-call island differs from the replayed original binding"
            );
        }
        for change_callee in [false, true] {
            let mut changed = module.clone();
            if change_callee {
                changed.functions[1].blocks[0].body[0].inst = Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![],
                };
            } else {
                changed.functions[0].blocks[0].body[0].inst = Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(43),
                };
            }
            let rejected = crate::validate_module_with_config(&changed, &configuration);
            assert!(
                !rejected.is_ok(),
                "changed body/callee must lose original source authority"
            );
            assert!(rejected.replayed_certificate_refs().is_none());
            let error = join_source(&rejected, &core, &island, &caller_source, &callee_source)
                .err()
                .unwrap();
            assert_eq!(
                error.0,
                "source-call operational join requires a successful original-module report"
            );
        }
    }
}

#[cfg(feature = "source-value-operational")]
#[test]
fn source_call_independent_wrong_source_refuses_actual_equation_kernel() {
    let error = source_call_fixture(nat(43)).err().unwrap();
    assert!(
        error.contains("TypeMismatch"),
        "not a semantic kernel mismatch: {error}"
    );
    assert!(
        error.contains("source equation kernel refusal"),
        "not a semantic equation refusal: {error}"
    );
}
