// Copyright 2026 Andrew Yates | Apache-2.0
use super::tests::{addresses, conversion, environment, fixture, limits, memory, providers, truth};
use super::*;
use crate::core_reflection::reflect_core_module_v1;
use clean_kernel::{BinderInfo, Declaration, KernelTypeError, Name};
use trust_ir::proof::*;

fn original() -> Module {
    let mut m = fixture(Ty::U64, 0);
    m.func_types[0].params = vec![Ty::U64];
    m.functions[0].blocks[0].body.remove(0);
    m.functions[0].blocks[0].params = vec![(ValueId::new(3), Ty::U64)];
    m.functions[1].blocks[0].params = vec![(ValueId::new(5), Ty::U64)];
    let Inst::Call { args, .. } = &mut m.functions[1].blocks[0].body[0].inst else {
        panic!()
    };
    *args = vec![ValueId::new(5)];
    m
}
fn encoded(owner: &DefinedWordForwardCall<'_>, reflected: &ReflectedCoreModuleV1<'_>) -> Vec<u8> {
    let model = MachineModel::new(constant("Nat"), reflected, providers());
    let mem = memory(false);
    let root = owner.entry_root(mem.clone(), nat(37));
    let retire = |who| {
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
    let fuel = candidate.run.fuel().term().clone();
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker
        .check_type(
            &refl(&constant("Nat"), fuel.clone()),
            &eq(&constant("Nat"), fuel, nat(3)),
        )
        .expect("actual fetched CALL/RETURN/RETURN fuel must definitionally equal three");
    trust_ir::proof::encode_clean_expr_dag_v2(
        &scope.close(candidate.run.equality().term()).unwrap(),
    )
    .unwrap()
}
#[test]
fn actual_word_argument_initializer_call_return_and_retirement_replay() {
    for argument in [0, 43, u64::MAX] {
        let m = original();
        let reflected = reflect_core_module_v1(&m, &addresses()).unwrap();
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let owner = catalog
            .defined_word_forward_call(FuncId::new(1), FuncId::new(0), argument)
            .unwrap();
        let bytes = encoded(&owner, &reflected);
        let checked = owner
            .check_entry_proof(constant("Nat"), providers(), memory(false), nat(37), &bytes)
            .unwrap();
        assert_eq!(checked.argument(), argument);
        assert_eq!(
            checked.functions_in(&m).unwrap(),
            (FuncId::new(1), FuncId::new(0))
        );
        assert!(checked.functions_in(&m.clone()).is_err());
        let mut checker = TypeChecker::new(environment());
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        let error = checker
            .check_type(checked.proof(), &constant("False"))
            .unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "{error:?}"
        );
        let other = catalog
            .defined_word_forward_call(FuncId::new(1), FuncId::new(0), argument.wrapping_add(1))
            .unwrap();
        assert_eq!(
            other
                .check_entry_proof(constant("Nat"), providers(), memory(false), nat(37), &bytes)
                .err()
                .unwrap(),
            "operational proof failed strict kernel checking"
        );
        assert_eq!(
            owner
                .check_entry_proof(constant("Nat"), providers(), memory(false), nat(38), &bytes)
                .err()
                .unwrap(),
            "operational proof failed strict kernel checking"
        );
    }
}
#[test]
fn actual_parameter_width_target_and_body_refusals_remain_structural() {
    let mut variants = vec![];
    let mut m = original();
    m.func_types[0].params = vec![Ty::U32];
    variants.push(m);
    let mut m = original();
    m.functions[0].blocks[0].params[0].1 = Ty::I64;
    variants.push(m);
    let mut m = original();
    let Inst::Call { args, .. } = &mut m.functions[1].blocks[0].body[0].inst else {
        panic!()
    };
    *args = vec![ValueId::new(99)];
    variants.push(m);
    let mut m = original();
    let Inst::Call { callee, .. } = &mut m.functions[1].blocks[0].body[0].inst else {
        panic!()
    };
    *callee = FuncId::new(1);
    variants.push(m);
    let mut m = original();
    m.functions[0].blocks[0].body.insert(
        0,
        trust_ir::InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(90)),
    );
    variants.push(m);
    for m in variants {
        if let Ok(reflected) = reflect_core_module_v1(&m, &addresses()) {
            let mut c = Catalog::new(environment(), &reflected, limits()).unwrap();
            assert!(
                c.defined_word_forward_call(FuncId::new(1), FuncId::new(0), 43)
                    .is_err()
            );
        }
    }
}
#[test]
fn independently_authored_source_lambdas_join_the_exact_pointwise_entry() {
    let mut m = original();
    let source = |name: &str| Expr::const_str(name);
    let definition = |name: &str, value| Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, constant("Nat"), constant("Nat")),
        value,
        is_reducible: true,
    };
    let island = IslandEnvironment::new(
        encode_island_declarations_v1(&[
            definition(
                "Forward.leaf",
                Expr::lam(BinderInfo::Default, constant("Nat"), Expr::bvar(0)),
            ),
            definition(
                "Forward.entry",
                Expr::lam(
                    BinderInfo::Default,
                    constant("Nat"),
                    Expr::app(source("Forward.leaf"), Expr::bvar(0)),
                ),
            ),
        ])
        .unwrap(),
    );
    let sr = |name: &str| SourceDefinitionRef {
        decl: name.into(),
        closure_digest: island.digest,
    };
    let caller = sr("Forward.entry");
    let callee = sr("Forward.leaf");
    let family = crate::certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        trust_ir::value::ProofId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "word-forward-call",
            "actual-source",
            "1",
        ),
        &island,
        &[
            (FuncId::new(1), caller.clone()),
            (FuncId::new(0), callee.clone()),
        ],
    )
    .unwrap();
    let gates = m
        .functions
        .iter()
        .map(|f| {
            let o = family
                .obligations
                .iter()
                .find(|o| o.function == Some(f.id))
                .unwrap();
            (
                f.id,
                trust_ir::GateEvidence {
                    obligation: o.id,
                    body_digest: m.function_body_digest(f.id).unwrap(),
                },
            )
        })
        .collect::<Vec<_>>();
    for (id, evidence) in gates {
        m.functions
            .iter_mut()
            .find(|f| f.id == id)
            .unwrap()
            .body_gate = Some(trust_ir::BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: Some(evidence),
        });
    }
    m.proof_obligations.extend(family.obligations);
    m.proof_certificates.extend(family.certificates);
    let config = crate::ValidationConfig::pinned()
        .with_bound_certificates(true)
        .with_source_bound_certificates(true)
        .with_gate_evidence(true);
    let report = crate::validate_module_with_config(&m, &config);
    assert!(report.is_ok(), "{:?}", report.errors());
    let reflected =
        crate::source_call_operational::reflect_source_call_core_module_v1(&report, &addresses())
            .unwrap();
    let mut c = Catalog::new(environment(), &reflected, limits()).unwrap();
    let owner = c
        .defined_word_forward_call(FuncId::new(1), FuncId::new(0), 43)
        .unwrap();
    let bytes = encoded(&owner, &reflected);
    let checked = owner
        .check_entry_proof(constant("Nat"), providers(), memory(false), nat(37), &bytes)
        .unwrap();
    let joined =
        crate::source_call_operational::check_source_bound_defined_word_forward_call_entry(
            &report, &checked, &island, &caller, &callee,
        )
        .unwrap();
    assert_eq!(
        joined.functions_in(&m).unwrap(),
        (FuncId::new(1), FuncId::new(0))
    );
    assert!(
        crate::source_call_operational::check_source_bound_defined_word_forward_call_entry(
            &report, &checked, &island, &callee, &caller
        )
        .is_err()
    );
}

#[test]
fn universal_original_parameter_add_source_entry_replays() {
    let mut m = original();
    m.functions[0].blocks[0].body = vec![
        trust_ir::InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(90)),
        trust_ir::InstrNode::new(Inst::BinOp {
            op: trust_ir::BinOp::Add,
            ty: Ty::U64,
            lhs: ValueId::new(3),
            rhs: ValueId::new(90),
        })
        .with_result(ValueId::new(91)),
        trust_ir::InstrNode::new(Inst::Return {
            values: vec![ValueId::new(91)],
        }),
    ];
    let source = |name: &str| Expr::const_str(name);
    let definition = |name: &str, value| Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, constant("Nat"), constant("Nat")),
        value,
        is_reducible: true,
    };
    let island = IslandEnvironment::new(
        encode_island_declarations_v1(&[
            definition(
                "Forward.leaf",
                Expr::lam(
                    BinderInfo::Default,
                    constant("Nat"),
                    app(
                        "Nat.mod",
                        [
                            app("Nat.add", [Expr::bvar(0), nat(7)]),
                            Expr::nat_lit_u128(1u128 << 64),
                        ],
                    ),
                ),
            ),
            definition(
                "Forward.entry",
                Expr::lam(
                    BinderInfo::Default,
                    constant("Nat"),
                    Expr::app(source("Forward.leaf"), Expr::bvar(0)),
                ),
            ),
        ])
        .unwrap(),
    );
    let sr = |name: &str| SourceDefinitionRef {
        decl: name.into(),
        closure_digest: island.digest,
    };
    let caller = sr("Forward.entry");
    let callee = sr("Forward.leaf");
    let family = crate::certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        trust_ir::value::ProofId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "word-forward-call",
            "actual-source",
            "1",
        ),
        &island,
        &[
            (FuncId::new(1), caller.clone()),
            (FuncId::new(0), callee.clone()),
        ],
    )
    .unwrap();
    let gates = m
        .functions
        .iter()
        .map(|f| {
            let o = family
                .obligations
                .iter()
                .find(|o| o.function == Some(f.id))
                .unwrap();
            (
                f.id,
                trust_ir::GateEvidence {
                    obligation: o.id,
                    body_digest: m.function_body_digest(f.id).unwrap(),
                },
            )
        })
        .collect::<Vec<_>>();
    for (id, evidence) in gates {
        m.functions
            .iter_mut()
            .find(|f| f.id == id)
            .unwrap()
            .body_gate = Some(trust_ir::BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: Some(evidence),
        });
    }
    m.proof_obligations.extend(family.obligations);
    m.proof_certificates.extend(family.certificates);
    let config = crate::ValidationConfig::pinned()
        .with_bound_certificates(true)
        .with_source_bound_certificates(true)
        .with_gate_evidence(true);
    let report = crate::validate_module_with_config(&m, &config);
    assert!(report.is_ok(), "{:?}", report.errors());
    let checked = crate::core_execution::derive_defined_word_add_call_entry(
        &report,
        FuncId::new(1),
        FuncId::new(0),
    )
    .unwrap();
    let joined = crate::source_call_operational::check_source_bound_defined_word_add_call_entry(
        &report, &checked, &island, &caller, &callee,
    )
    .unwrap();
    let mut checker = TypeChecker::new(joined.environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    assert!(
        checker
            .check_type(joined.proof(), &constant("False"))
            .is_err()
    );
    assert!(joined.functions_in(&m.clone()).is_err());
    assert_eq!(
        joined.functions_in(&m).unwrap(),
        (FuncId::new(1), FuncId::new(0))
    );
    assert!(
        crate::source_call_operational::check_source_bound_defined_word_add_call_entry(
            &report, &checked, &island, &callee, &caller
        )
        .is_err()
    );
}

#[test]
fn universal_add_profile_refuses_wrong_width_operand_target_and_extra_effect() {
    let mut original_add = original();
    original_add.functions[0].blocks[0].body = vec![
        trust_ir::InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(90)),
        trust_ir::InstrNode::new(Inst::BinOp {
            op: trust_ir::BinOp::Add,
            ty: Ty::U64,
            lhs: ValueId::new(3),
            rhs: ValueId::new(90),
        })
        .with_result(ValueId::new(91)),
        trust_ir::InstrNode::new(Inst::Return {
            values: vec![ValueId::new(91)],
        }),
    ];

    for change in 0..4 {
        let mut m = original_add.clone();
        match change {
            0 => m.func_types[0].params = vec![Ty::U32],
            1 => {
                let Inst::BinOp { lhs, .. } = &mut m.functions[0].blocks[0].body[1].inst else {
                    panic!()
                };
                *lhs = ValueId::new(90);
            }
            2 => {
                let Inst::Call { callee, .. } = &mut m.functions[1].blocks[0].body[0].inst else {
                    panic!()
                };
                *callee = FuncId::new(1);
            }
            _ => {
                let extra = m.functions[0].blocks[0].body[0].clone();
                m.functions[0].blocks[0].body.insert(0, extra);
            }
        }
        if let Ok(reflected) = reflect_core_module_v1(&m, &addresses()) {
            let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
            assert!(
                catalog
                    .defined_word_add_call(FuncId::new(1), FuncId::new(0))
                    .is_err()
            );
        }
    }
}
