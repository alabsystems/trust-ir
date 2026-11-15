// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "source-value-operational")]
//! Complete retained production subject, not a cleared/pruned selected surrogate.
//! Requires the checked canonical Release33 syntax and explicitly unmodelled step.
use trust_ir::{
    FuncId, Module, ObligationKind, ProofFormula, ProofId, ProofObligation, ProofStatus,
};
use trust_ir_build::clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker, TypeError,
};
use trust_ir_build::core_execution::Limits;
use trust_ir_build::core_reflection::{
    reflect_core_module_v1, reflect_core_module_with_runtime_signature_descriptors_v1,
};
use trust_ir_build::{
    ValidationConfig, check_u32_straight_line_source_value,
    check_u32_straight_line_source_value_with_runtime_signature_descriptors,
    check_u32_straight_line_source_value_with_validated_runtime_context,
    check_u64_straight_line_source_value, check_uint_source_value_equation,
    validate_module_with_config,
};
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}
fn limits() -> Limits {
    Limits {
        max_operations: 20000,
        max_locals: 4096,
        max_list_items: 4096,
        max_lookup_candidates: 1024,
        lookup_heartbeats: 1000000,
        lookup_cache_entries: 100000,
    }
}
fn fixture() -> (Module, Environment, Name, Declaration) {
    macro_rules! data {
        ($file:literal) => {
            include_bytes!(concat!(
                "fixtures/source_value_equations/boundActualEquation/",
                $file
            ))
        };
    }
    fn expression(raw: &[u8]) -> Expr {
        trust_ir::proof::decode_clean_expr_v1(raw).unwrap()
    }
    fn name(raw: &[u8]) -> Name {
        let e = expression(raw);
        let trust_ir_build::clean_kernel::ExprKind::Const(n, l) = e.kind() else {
            panic!("name carrier")
        };
        assert!(l.is_empty());
        n.clone()
    }
    let module = trust_ir::binary::deserialize_module(data!("module.bin")).unwrap();
    assert_eq!(module.functions.len(), 72);
    assert_eq!(module.func_types.len(), 73);
    assert_eq!(module.proof_obligations.len(), 1);
    assert_eq!(module.proof_certificates.len(), 1);
    let selected = module.function_by_id(FuncId::new(70)).unwrap();
    assert_eq!(selected.name, "boundActualEquation");
    assert_eq!(selected.blocks.len(), 1);
    assert_eq!(selected.blocks[0].id.index(), 0);
    assert_eq!(
        selected.blocks[0]
            .params
            .iter()
            .map(|(id, _)| id.index())
            .collect::<Vec<_>>(),
        [0, 1]
    );
    assert_eq!(selected.blocks[0].body.len(), 4);
    // Literal reference states below are independent; pin the actual sparse/nominal coordinates.
    assert_eq!(
        selected.blocks[0]
            .body
            .iter()
            .flat_map(|n| n.results.iter().map(|id| id.index()))
            .collect::<Vec<_>>(),
        [2, 3, 4]
    );
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: name(data!("definition-0.name.bin")),
        level_params: vec![],
        type_: expression(data!("definition-0.type.bin")),
        value: expression(data!("definition-0.value.bin")),
        is_reducible: false,
    })
    .unwrap();
    let source = Name::from_string("boundActualEquation");
    assert_eq!(
        env.closure_digest(&source).unwrap().as_slice(),
        data!("source-closure-digest.bin")
    );
    let theorem = Declaration::Theorem {
        name: name(data!("theorem.name.bin")),
        level_params: vec![],
        type_: expression(data!("theorem.type.bin")),
        value: expression(data!("theorem.value.bin")),
    };
    (module, env, source, theorem)
}
fn addresses(m: &Module) -> Vec<(FuncId, u64)> {
    m.functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, 4096 + 8 * i as u64))
        .collect()
}
fn metadata_variant(original: &Module) -> Module {
    assert!(
        !original
            .proof_obligations
            .iter()
            .any(|o| o.id == ProofId::new(1))
    );
    let row = ProofObligation::new(
        ProofId::new(1),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "independently replayed unrelated literal contract",
    )
    .with_formula(ProofFormula::smtlib2("(= 1 1)", "Bool"));
    // This real minter grounds and kernel-discharges the goal; a status flag alone is never authority.
    let certificate =
        trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_bound_in(
            original,
            &row,
            "metadata-variant-contract",
        )
        .expect("real bound certificate, not fabricated receipt");
    let mut variant = original.clone();
    variant.proof_obligations.push(row);
    variant.proof_certificates.push(certificate);
    variant
}
fn same_retained_fields(a: &Module, b: &Module) {
    assert_eq!(a.name, b.name, "retained name");
    assert_eq!(a.functions, b.functions, "retained functions");
    assert_eq!(a.structs, b.structs, "retained structs");
    assert_eq!(a.enums, b.enums, "retained enums");
    assert_eq!(a.records, b.records, "retained records");
    assert_eq!(a.closure_types, b.closure_types, "retained closure_types");
    assert_eq!(a.globals, b.globals, "retained globals");
    assert_eq!(a.func_types, b.func_types, "retained func_types");
    assert_eq!(a.types, b.types, "retained types");
    assert_eq!(a.target_info, b.target_info, "retained target_info");
    assert_eq!(a.files, b.files, "retained files");
    assert_eq!(
        a.obligation_diagnostics, b.obligation_diagnostics,
        "retained obligation_diagnostics"
    );
    assert_eq!(a.spec_modules, b.spec_modules, "retained spec_modules");
    assert_eq!(a.universes, b.universes, "retained universes");
    assert_eq!(a.predicates, b.predicates, "retained predicates");
    assert_eq!(a.global_asm, b.global_asm, "retained global_asm");
    assert_eq!(a.imports, b.imports, "retained imports");
    assert_eq!(a.tuple_layouts, b.tuple_layouts, "retained tuple_layouts");
    assert_eq!(a.completeness, b.completeness, "retained completeness");
    assert_eq!(a.drop_glue, b.drop_glue, "retained drop_glue");
    assert_eq!(
        a.closure_layouts, b.closure_layouts,
        "retained closure_layouts"
    );
    // functions' derived equality includes ALL19 fields, including body_gate/proofs/provenance.
}
fn ir_list(ty: &str, values: impl IntoIterator<Item = Expr>) -> Expr {
    let values: Vec<_> = values.into_iter().collect();
    values
        .into_iter()
        .rev()
        .fold(app("IRList.nil", [Expr::const_str(ty)]), |tail, value| {
            app("IRList.cons", [Expr::const_str(ty), value, tail])
        })
}

fn integer(value: u64) -> Expr {
    app("IRScalar.int_", [Expr::nat_lit(value)])
}

fn memory(bad_owner: bool) -> Expr {
    let allocations = if bad_owner {
        vec![app(
            "IRByteAllocationV1.mk",
            [
                Expr::nat_lit(16u64),
                Expr::nat_lit(8u64),
                Expr::nat_lit(7u64),
                Expr::const_str("Bool.true"),
            ],
        )]
    } else {
        vec![]
    };
    app(
        "IRByteMemoryV1.mk",
        [
            ir_list("IRByteAllocationV1", allocations),
            Expr::lam(
                BinderInfo::Default,
                Expr::const_str("Nat"),
                app(
                    "IROption.some",
                    [Expr::const_str("Nat"), Expr::nat_lit(173u64)],
                ),
            ),
            Expr::nat_lit(128u64),
        ],
    )
}

fn providers() -> Expr {
    let result = app(
        "IRByteImportResultV1.mk",
        [
            Expr::const_str("Nat"),
            app("IROutcome.stuck", [Expr::const_str("IRFault.no_func")]),
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    );
    [
        Expr::const_str("Nat"),
        app("IRList", [Expr::const_str("IRScalar")]),
        Expr::const_str("IRByteMemoryV1"),
        Expr::const_str("Nat"),
    ]
    .into_iter()
    .rev()
    .fold(result, |body, ty| Expr::lam(BinderInfo::Default, ty, body))
}

fn world(memory: Expr, owners: &[u64], next: u64) -> Expr {
    app(
        "IRByteWorldV1.mk",
        [
            Expr::const_str("Nat"),
            memory,
            Expr::nat_lit(99u64),
            ir_list("Nat", owners.iter().map(|&x| Expr::nat_lit(x))),
            Expr::nat_lit(next),
        ],
    )
}

fn halted(memory: Expr, owners: &[u64], next: u64, outcome: Expr) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [Expr::const_str("Nat"), outcome, world(memory, owners, next)],
    )
}

// Expected states are independent literal SSA and world constructions, not
// the candidate's projection. Both fixtures have Const, arithmetic, arithmetic, Return.
fn expected_prefix(fuel: u64) -> Expr {
    let values = [7, 10, 50];
    if fuel >= 4 {
        return halted(
            memory(false),
            &[],
            2,
            app("IROutcome.ret", [ir_list("IRScalar", [integer(values[2])])]),
        );
    }
    let mut bindings = vec![(0, 3), (1, 5)];
    for (index, value) in values
        .iter()
        .take(usize::try_from(fuel).unwrap())
        .enumerate()
    {
        bindings.insert(0, (2 + u64::try_from(index).unwrap(), *value));
    }
    let frame = app(
        "IRFrame.mk",
        [
            Expr::nat_lit(70),
            Expr::nat_lit(0),
            Expr::nat_lit(fuel),
            ir_list(
                "IRBinding",
                bindings
                    .into_iter()
                    .map(|(id, v)| app("IRBinding.mk", [Expr::nat_lit(id), integer(v)])),
            ),
            ir_list("Nat", []),
        ],
    );
    app(
        "IRByteConfigV1.running",
        [
            Expr::const_str("Nat"),
            app(
                "IRMachine.mk",
                [
                    ir_list("IRFrame", [frame]),
                    ir_list("IRMemSlot", []),
                    Expr::nat_lit(0),
                ],
            ),
            world(memory(false), &[1], 2),
        ],
    )
}

fn actual_run(context: Expr, arguments: Expr, memory: Expr, fuel: u64) -> Expr {
    let initial = app(
        "ir_byte_init_v1",
        [
            Expr::const_str("Nat"),
            context.clone(),
            Expr::nat_lit(70u64),
            arguments,
            memory,
            Expr::nat_lit(99u64),
        ],
    );
    app(
        "ir_byte_run_v1",
        [
            Expr::const_str("Nat"),
            context,
            providers(),
            Expr::nat_lit(fuel),
            initial,
        ],
    )
}

fn config_equality(actual: Expr, expected: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            app("IRByteConfigV1", [Expr::const_str("Nat")]),
            actual,
            expected,
        ],
    )
}

fn check_point(environment: &Environment, proof: &Expr, goal: &Expr, accepted: bool) {
    let mut checker = TypeChecker::new(environment);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    assert_eq!(checker.heartbeat_limit(), 2_000_000);
    let result = checker.check_type(proof, goal);
    assert!(
        !checker.heartbeat_spent(),
        "resource stop is not a verdict: {result:?}"
    );
    if accepted {
        result.unwrap();
    } else {
        assert!(
            matches!(result, Err(TypeError::TypeMismatch { .. })),
            "{result:?}"
        );
    }
}

fn config_reflexivity(expected: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [app("IRByteConfigV1", [Expr::const_str("Nat")]), expected],
    )
}

#[test]
fn intact_actual_module_and_separately_admitted_metadata_variant_derive_both_contracts() {
    let (original, env, source, theorem) = fixture();
    let before = original.clone();
    let variant = metadata_variant(&original);
    same_retained_fields(&original, &variant);
    assert_eq!(variant.proof_obligations[0], original.proof_obligations[0]);
    assert_eq!(
        variant.proof_certificates[0],
        original.proof_certificates[0]
    );
    let mut contexts = Vec::new();
    let mut authority_sets = Vec::new();
    for module in [&original, &variant] {
        let independent = validate_module_with_config(module, &ValidationConfig::pinned());
        assert!(independent.is_ok(), "{:?}", independent.errors());
        assert!(std::ptr::eq(
            independent.validated_module().unwrap(),
            module
        ));
        let value =
            check_uint_source_value_equation(module, FuncId::new(70), &env, &source, &theorem)
                .unwrap();
        let checked = check_u32_straight_line_source_value_with_validated_runtime_context(
            &value,
            &addresses(module),
            limits(),
        )
        .unwrap();
        let report = checked
            .retained_validation_report()
            .expect("exact original SourceEq admission");
        assert!(std::ptr::eq(report.validated_module().unwrap(), module));
        assert!(report.handle_registry_is_pinned());
        assert_eq!(
            report.replayed_certificate_refs(),
            independent.replayed_certificate_refs()
        );
        for cert in &module.proof_certificates {
            assert!(
                report
                    .replayed_certificate_refs()
                    .unwrap()
                    .contains(&cert.lineage_ref())
            );
        }
        authority_sets.push(report.replayed_certificate_refs().unwrap().clone());
        assert!(std::ptr::eq(checked.source_value(), &value));
        assert!(reflect_core_module_v1(module, &addresses(module)).is_err());
        assert!(
            reflect_core_module_with_runtime_signature_descriptors_v1(module, &addresses(module))
                .is_err()
        );
        assert!(
            check_u32_straight_line_source_value(&value, &addresses(module), limits()).is_err()
        );
        assert!(
            check_u64_straight_line_source_value(&value, &addresses(module), limits()).is_err()
        );
        assert!(
            check_u32_straight_line_source_value_with_runtime_signature_descriptors(
                &value,
                &addresses(module),
                limits()
            )
            .is_err()
        );
        for fuel in [0, 1, 2, 3, 4, 10] {
            let expected = expected_prefix(fuel);
            let raw = ir_list("IRScalar", [integer(3), integer(5)]);
            let goal = config_equality(
                actual_run(checked.context().clone(), raw.clone(), memory(false), fuel),
                expected.clone(),
            );
            check_point(
                checked.environment(),
                &config_reflexivity(expected),
                &goal,
                true,
            );
            let total = Expr::apps(
                checked.total_proof().clone(),
                [
                    Expr::const_str("Nat"),
                    memory(false),
                    Expr::nat_lit(99),
                    providers(),
                    raw,
                    Expr::nat_lit(fuel),
                ],
            );
            check_point(checked.environment(), &total, &goal, true);
            let typed = Expr::apps(
                checked.typed_proof().clone(),
                [
                    Expr::const_str("Nat"),
                    memory(false),
                    Expr::nat_lit(99),
                    providers(),
                    app("UInt32.ofNat", [Expr::nat_lit(3)]),
                    app("UInt32.ofNat", [Expr::nat_lit(5)]),
                    Expr::nat_lit(fuel),
                ],
            );
            check_point(checked.environment(), &typed, &goal, true);
        }
        for bad in [false, true] {
            for fuel in [0, 10] {
                let raw = ir_list("IRScalar", [integer(1_u64 << 32), integer(0)]);
                let expected = halted(
                    memory(bad),
                    if bad { &[8] } else { &[1] },
                    if bad { 9 } else { 2 },
                    app(
                        "IROutcome.type_error",
                        [Expr::const_str(if bad {
                            "IRFault.bad_addr"
                        } else {
                            "IRFault.bad_field"
                        })],
                    ),
                );
                let goal = config_equality(
                    actual_run(checked.context().clone(), raw.clone(), memory(bad), fuel),
                    expected.clone(),
                );
                check_point(
                    checked.environment(),
                    &config_reflexivity(expected),
                    &goal,
                    true,
                );
                let total = Expr::apps(
                    checked.total_proof().clone(),
                    [
                        Expr::const_str("Nat"),
                        memory(bad),
                        Expr::nat_lit(99),
                        providers(),
                        raw,
                        Expr::nat_lit(fuel),
                    ],
                );
                check_point(checked.environment(), &total, &goal, true);
            }
        }
        assert!(trust_ir_build::validate_module_for_codegen(module).iter().any(|e|matches!(e,trust_ir_build::ValidationError::UngatedBodyForCodegen{function,..} if *function==71)));
        contexts.push(checked.context().clone());
    }
    assert_ne!(authority_sets[0], authority_sets[1]);
    assert_eq!(contexts[0], contexts[1]);
    // Exact ACTUAL context equality; no fake metadata-bearing evaluator is introduced.
    let ty = Expr::const_str("IRByteContextV1");
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty.clone(), contexts[0].clone(), contexts[1].clone()],
    );
    let refl = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, contexts[0].clone()],
    );
    let value =
        check_uint_source_value_equation(&original, FuncId::new(70), &env, &source, &theorem)
            .unwrap();
    let checked = check_u32_straight_line_source_value_with_validated_runtime_context(
        &value,
        &addresses(&original),
        limits(),
    )
    .unwrap();
    check_point(checked.environment(), &refl, &eq, true);
    assert_eq!(original, before);
}
#[test]
fn original_certificate_context_statement_and_obligation_mutants_reenter_admission() {
    let (original, env, source, theorem) = fixture();
    for case in 0..7 {
        let mut m = original.clone();
        match case {
            0 => {
                let trust_ir::ProofEvidence::CleanCic { term, .. } =
                    &mut m.proof_certificates[0].evidence
                else {
                    panic!("actualCic")
                };
                term.clear();
            }
            1 => {
                let trust_ir::ProofEvidence::CleanCic { context, .. } =
                    &mut m.proof_certificates[0].evidence
                else {
                    panic!("actualCic")
                };
                *context = vec![255];
            }
            2 => {
                m.proof_obligations[0].formula = None;
            }
            3 => {
                m.proof_obligations[0].id = ProofId::new(1);
            }
            4 => {
                m.proof_certificates[0].obligation = ProofId::new(1);
            }
            5 => {
                m.proof_obligations[0]
                    .description
                    .push_str(" changed lineage");
            }
            _ => {
                let names: std::collections::BTreeMap<_, _> =
                    m.functions.iter().map(|f| (f.id, f.name.clone())).collect();
                let row = m.proof_obligations[0].clone();
                let trust_ir::ProofEvidence::CleanCic {
                    lineage,
                    kernel_recheck: Some(directive),
                    ..
                } = &mut m.proof_certificates[0].evidence
                else {
                    panic!("bound actualCic")
                };
                let binding = directive.binding.as_mut().unwrap();
                binding.statement_digest = trust_ir::ProofDigest::sha256([0; 32]);
                *lineage = trust_ir::proof::clean_cic_lineage_digest_v8(
                    &row,
                    &|id| names.get(&id).cloned(),
                    Some(binding),
                )
                .unwrap();
            }
        }
        let report = validate_module_with_config(&m, &ValidationConfig::pinned());
        assert!(!report.is_ok(), "case{case}");
        if case == 6 {
            assert!(report.errors().iter().any(|e|matches!(e,trust_ir_build::ValidationError::CertificateBindingMismatch{field,..} if field=="statement_digest")));
        }
        assert!(
            matches!(
                check_uint_source_value_equation(&m, FuncId::new(70), &env, &source, &theorem),
                Err(trust_ir_build::SourceValueEquationError::InvalidModule(_))
            ),
            "case{case}"
        );
    }
    let mut false_row = ProofObligation::new(
        ProofId::new(1),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "false",
    );
    false_row.formula = Some(ProofFormula::smtlib2("(= 1 2)", "Bool"));
    assert!(
        trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_bound_in(
            &original, &false_row, "probe"
        )
        .is_none()
    );
}
#[test]
fn field_sensitivity_preserves_real_ids_orders_varargs_conventions_and_address_inputs() {
    let (original, env, source, theorem) = fixture();
    let value =
        check_uint_source_value_equation(&original, FuncId::new(70), &env, &source, &theorem)
            .unwrap();
    let checked = check_u32_straight_line_source_value_with_validated_runtime_context(
        &value,
        &addresses(&original),
        limits(),
    )
    .unwrap();
    let baseline = checked.context().clone();
    // Actual declaration0 is clean_inc, whose complete signature and C
    // convention are pinned RC ABI requirements. It is NOT a success mutant.
    let rc = original.function_by_id(FuncId::new(0)).unwrap();
    assert_eq!(rc.name, "clean_inc");
    assert_eq!(rc.ty.index(), 0);
    for change_vararg in [false, true] {
        let mut changed = original.clone();
        if change_vararg {
            changed.func_types[0].is_vararg = true;
        } else {
            changed
                .function_by_id_mut(FuncId::new(0))
                .unwrap()
                .calling_conv = trust_ir::CallingConv::Fast;
        }
        let report = validate_module_with_config(&changed, &ValidationConfig::pinned());
        assert!(!report.is_ok());
        assert!(report.errors().iter().any(|error| matches!(error,
            trust_ir_build::ValidationError::RcEntryPointSignatureMismatch { function: 0, symbol, .. }
                if symbol == "clean_inc")));
        assert!(matches!(
            check_uint_source_value_equation(&changed, FuncId::new(70), &env, &source, &theorem),
            Err(trust_ir_build::SourceValueEquationError::InvalidModule(_))
        ));
    }
    // clean_box is an unused, non-special declaration, unlike the pinned RC
    // namespace. Its actual U64->Ptr descriptor is retained in both contexts.
    let unused = original.function_by_id(FuncId::new(3)).unwrap();
    assert_eq!(unused.name, "clean_box");
    assert_eq!(unused.ty.index(), 3);
    assert!(unused.is_declaration());
    let signature = original.func_type(unused.ty).unwrap();
    assert_eq!(signature.params, [trust_ir::Ty::U64]);
    assert_eq!(signature.returns, [trust_ir::Ty::Ptr]);
    assert!(!signature.is_vararg);
    assert_eq!(unused.calling_conv, trust_ir::CallingConv::C);
    assert!(
        !original
            .functions
            .iter()
            .flat_map(|function| &function.blocks)
            .flat_map(|block| &block.body)
            .any(|node| matches!(node.inst,
            trust_ir::Inst::Call { callee, .. } if callee == unused.id))
    );
    for case in 0..3 {
        let mut changed = original.clone();
        match case {
            0 => changed.functions.reverse(),
            1 => {
                changed.function_by_id_mut(unused.id).unwrap().calling_conv =
                    trust_ir::CallingConv::Fast
            }
            _ => changed.func_types[unused.ty.as_usize()].is_vararg = true,
        }
        let value =
            check_uint_source_value_equation(&changed, FuncId::new(70), &env, &source, &theorem)
                .unwrap();
        let observed = check_u32_straight_line_source_value_with_validated_runtime_context(
            &value,
            &addresses(&original),
            limits(),
        )
        .unwrap();
        assert_ne!(*observed.context(), baseline, "case{case}");
    }
    let mut shifted = addresses(&original);
    for (_, address) in &mut shifted {
        *address += 8;
    }
    assert_ne!(
        *check_u32_straight_line_source_value_with_validated_runtime_context(
            &value,
            &shifted,
            limits()
        )
        .unwrap()
        .context(),
        baseline
    );
    let mut wrong_result = original.clone();
    wrong_result
        .functions
        .iter_mut()
        .find(|f| f.id.index() == 70)
        .unwrap()
        .blocks[0]
        .body[0]
        .results
        .clear();
    assert!(matches!(
        check_uint_source_value_equation(&wrong_result, FuncId::new(70), &env, &source, &theorem),
        Err(trust_ir_build::SourceValueEquationError::InvalidModule(_))
    ));
}
#[test]
fn opaque_global_assembly_is_a_shared_new_refusal_on_otherwise_admitted_real_module() {
    let mut b = trust_ir_build::ModuleBuilder::new_with_target_info(
        "opaque_asm",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let sig = b.add_func_type(vec![trust_ir::Ty::U32], vec![trust_ir::Ty::U32]);
    let f = b.declare_function("identity", sig);
    let mut body = b.define_function(f).unwrap();
    let entry = body.create_block();
    let x = body.add_block_param(entry, trust_ir::Ty::U32);
    body.switch_to_block(entry);
    body.ret(vec![x]);
    body.build();
    let mut m = b.build().unwrap();
    let addrs = addresses(&m);
    assert!(reflect_core_module_v1(&m, &addrs).is_ok());
    assert!(reflect_core_module_with_runtime_signature_descriptors_v1(&m, &addrs).is_ok());
    m.global_asm.push(".p2align 2".into());
    assert!(validate_module_with_config(&m, &ValidationConfig::pinned()).is_ok());
    for error in [
        reflect_core_module_v1(&m, &addrs).unwrap_err(),
        reflect_core_module_with_runtime_signature_descriptors_v1(&m, &addrs).unwrap_err(),
    ] {
        assert_eq!(
            error.to_string(),
            "global assembly has no byte-profile interpretation"
        );
    }
    let (mut full, env, source, theorem) = fixture();
    full.global_asm.push(".p2align 2".into());
    let value =
        check_uint_source_value_equation(&full, FuncId::new(70), &env, &source, &theorem).unwrap();
    let error = check_u32_straight_line_source_value_with_validated_runtime_context(
        &value,
        &addresses(&full),
        limits(),
    )
    .err()
    .expect("new path cannot erase assembly");
    assert_eq!(
        error.to_string(),
        "global assembly has no byte-profile interpretation"
    );
    // No Rust/native execution counterexample or assembler-equivalence claim is inferred.
}

#[test]
fn exact_unused_layout_geometry_changes_context_without_metadata_erasure() {
    let (original, env, source, theorem) = fixture();
    let mut contexts = Vec::new();
    for size in [4, 8] {
        let mut m = original.clone();
        m.structs.push(trust_ir::StructDef {
            id: trust_ir::StructId::new(42),
            name: "unused_nominal_layout_probe".into(),
            fields: vec![trust_ir::ty::FieldDef {
                name: "field".into(),
                ty: trust_ir::Ty::U32,
                offset: Some(0),
            }],
            size: Some(size),
            align: Some(4),
            repr: trust_ir::StructRepr::Rust,
            origin: None,
        });
        let value =
            check_uint_source_value_equation(&m, FuncId::new(70), &env, &source, &theorem).unwrap();
        contexts.push(
            check_u32_straight_line_source_value_with_validated_runtime_context(
                &value,
                &addresses(&m),
                limits(),
            )
            .unwrap()
            .context()
            .clone(),
        );
    }
    assert_ne!(contexts[0], contexts[1]);
}
// Independent data observers: no projection/helper under test authors the expected graph.
fn constructor_fields(term: &Expr, name: &str, count: usize) -> Vec<Expr> {
    assert_eq!(term.get_app_fn(), &Expr::const_str(name));
    let args = term.get_app_args();
    assert_eq!(args.len(), count);
    args.into_iter().cloned().collect()
}
fn list_values(mut term: &Expr) -> Vec<Expr> {
    let mut values = Vec::new();
    loop {
        let args = term.get_app_args();
        if term.get_app_fn() == &Expr::const_str("IRList.nil") {
            assert_eq!(args.len(), 1);
            return values;
        }
        assert_eq!(term.get_app_fn(), &Expr::const_str("IRList.cons"));
        assert_eq!(args.len(), 3);
        values.push(args[1].clone());
        term = args[2];
    }
}
fn emitted_boxed_helper(context: &Expr) -> Expr {
    let ctx = constructor_fields(context, "IRByteContextV1.mk", 5);
    let program = constructor_fields(&ctx[0], "IRModule.mk", 2);
    let functions = list_values(&program[0]);
    assert_eq!(
        functions.len(),
        72,
        "the complete function graph remains present"
    );
    let helpers: Vec<_> = functions
        .into_iter()
        .filter(|function| constructor_fields(function, "IRFunc.mk", 4)[0] == Expr::nat_lit(71))
        .collect();
    assert_eq!(helpers.len(), 1);
    helpers[0].clone()
}
fn expected_helper_nodes() -> Vec<Expr> {
    let node = |inst, results: Vec<u64>| {
        app(
            "IRNode.mk",
            [inst, ir_list("Nat", results.into_iter().map(Expr::nat_lit))],
        )
    };
    let call = |fid, args: Vec<u64>| {
        app(
            "IRInst.call",
            [
                Expr::nat_lit(fid),
                ir_list("Nat", args.into_iter().map(Expr::nat_lit)),
            ],
        )
    };
    vec![
        node(call(10, vec![0]), vec![2]),
        node(call(10, vec![1]), vec![3]),
        node(app("IRInst.release", [Expr::nat_lit(0)]), vec![]),
        node(app("IRInst.release", [Expr::nat_lit(1)]), vec![]),
        node(call(70, vec![2, 3]), vec![4]),
        node(call(4, vec![4]), vec![5]),
        node(
            app("IRInst.ret", [ir_list("Nat", [Expr::nat_lit(5)])]),
            vec![],
        ),
    ]
}
fn expected_boxed_helper(nodes: Vec<Expr>) -> Expr {
    let params = ir_list("Nat", [Expr::nat_lit(0), Expr::nat_lit(1)]);
    app(
        "IRFunc.mk",
        [
            Expr::nat_lit(71),
            params.clone(),
            Expr::nat_lit(0),
            ir_list(
                "IRBlock",
                [app(
                    "IRBlock.mk",
                    [Expr::nat_lit(0), params, ir_list("IRNode", nodes)],
                )],
            ),
        ],
    )
}
fn emitted_site(context: &Expr, pc: u64) -> Expr {
    let ctx = constructor_fields(context, "IRByteContextV1.mk", 5);
    let sites: Vec<_> = list_values(&ctx[4])
        .into_iter()
        .filter(|site| {
            let fields = site.get_app_args();
            assert!(fields.len() >= 3);
            fields[0] == &Expr::nat_lit(71)
                && fields[1] == &Expr::nat_lit(0)
                && fields[2] == &Expr::nat_lit(pc)
        })
        .collect();
    assert_eq!(
        sites.len(),
        1,
        "one original helper site at each real coordinate"
    );
    sites[0].clone()
}
fn expected_release_site(pc: u64) -> Expr {
    app(
        "IRByteSiteV1.mk",
        [
            Expr::nat_lit(71),
            Expr::nat_lit(0),
            Expr::nat_lit(pc),
            Expr::nat_lit(0),
            Expr::nat_lit(0),
            ir_list("IRTy", []),
        ],
    )
}
#[test]
fn actual_boxed_helper_release_pointers_results_and_sites_retain_unmodelled_step() {
    let (m, env, source, theorem) = fixture();
    let value =
        check_uint_source_value_equation(&m, FuncId::new(70), &env, &source, &theorem).unwrap();
    let checked = check_u32_straight_line_source_value_with_validated_runtime_context(
        &value,
        &addresses(&m),
        limits(),
    )
    .unwrap();
    let helper = m.function_by_id(FuncId::new(71)).unwrap();
    assert_eq!(helper.blocks[0].body.len(), 7);
    // A wrong mapper that emits release0 twice must fail BEFORE any operational
    // endpoint test: unmodelled Release deliberately ignores its pointer.
    assert_eq!(
        emitted_boxed_helper(checked.context()),
        expected_boxed_helper(expected_helper_nodes())
    );
    for pc in [2, 3] {
        assert_eq!(
            emitted_site(checked.context(), pc),
            expected_release_site(pc)
        );
    }
    for (pc, ptr) in [(2, 0), (3, 1)] {
        assert_eq!(
            helper.blocks[0].body[pc].inst,
            trust_ir::Inst::Release {
                ptr: trust_ir::ValueId::new(ptr)
            }
        );
        assert!(helper.blocks[0].body[pc].results.is_empty());
        // An explicit valid state AT the original fetched helper coordinate;
        // no claim that arbitrary host providers reach it or execute ARC.
        let frame = app(
            "IRFrame.mk",
            [
                Expr::nat_lit(71),
                Expr::nat_lit(0),
                Expr::nat_lit(pc as u64),
                ir_list(
                    "IRBinding",
                    [
                        (0, app("IRScalar.ptr_", [Expr::nat_lit(16)])),
                        (1, app("IRScalar.ptr_", [Expr::nat_lit(24)])),
                        (2, integer(3)),
                        (3, integer(5)),
                    ]
                    .into_iter()
                    .map(|(id, value)| app("IRBinding.mk", [Expr::nat_lit(id), value])),
                ),
                ir_list("Nat", []),
            ],
        );
        let state = app(
            "IRByteConfigV1.running",
            [
                Expr::const_str("Nat"),
                app(
                    "IRMachine.mk",
                    [
                        ir_list("IRFrame", [frame]),
                        ir_list("IRMemSlot", []),
                        Expr::nat_lit(1),
                    ],
                ),
                world(memory(false), &[1], 2),
            ],
        );
        let actual = app(
            "ir_byte_step_v1",
            [
                Expr::const_str("Nat"),
                checked.context().clone(),
                providers(),
                state,
            ],
        );
        let expected = halted(
            memory(false),
            &[1],
            2,
            app(
                "IROutcome.unmodelled",
                [Expr::const_str("IRFault.width_bounded")],
            ),
        );
        check_point(
            checked.environment(),
            &config_reflexivity(expected.clone()),
            &config_equality(actual, expected),
            true,
        );
    }
    for mutation in ["swap", "delete"] {
        let mut changed = m.clone();
        let body = &mut changed.function_by_id_mut(FuncId::new(71)).unwrap().blocks[0].body;
        let mut expected_nodes = expected_helper_nodes();
        if mutation == "swap" {
            body[2].inst = trust_ir::Inst::Release {
                ptr: trust_ir::ValueId::new(1),
            };
            body[3].inst = trust_ir::Inst::Release {
                ptr: trust_ir::ValueId::new(0),
            };
            expected_nodes.swap(2, 3);
        } else {
            body.remove(2);
            let _removed_node = expected_nodes.remove(2);
        }
        // Changed subjects require their OWN complete admission and SourceEq.
        // A refusal is accepted only at that real whole-module validation stage.
        let changed_source = match check_uint_source_value_equation(
            &changed,
            FuncId::new(70),
            &env,
            &source,
            &theorem,
        ) {
            Ok(value) => value,
            Err(trust_ir_build::SourceValueEquationError::InvalidModule(errors)) => {
                assert!(!errors.is_empty());
                eprintln!("RELEASE_SYNTAX_{mutation}_ADMISSION_REFUSAL={errors:?}");
                continue;
            }
            Err(error) => panic!("unexpected selected source change for {mutation}: {error}"),
        };
        let observed = check_u32_straight_line_source_value_with_validated_runtime_context(
            &changed_source,
            &addresses(&changed),
            limits(),
        )
        .unwrap();
        assert_ne!(
            observed.context(),
            checked.context(),
            "syntax fidelity: {mutation}"
        );
        assert_eq!(
            emitted_boxed_helper(observed.context()),
            expected_boxed_helper(expected_nodes)
        );
        assert_eq!(
            emitted_site(observed.context(), 2),
            expected_release_site(2)
        );
        if mutation == "swap" {
            assert_eq!(
                emitted_site(observed.context(), 3),
                expected_release_site(3)
            );
        } else {
            // The following Call70 moved to pc3 and retains its actual U32 result.
            assert_eq!(
                emitted_site(observed.context(), 3),
                app(
                    "IRByteSiteV1.mk",
                    [
                        Expr::nat_lit(71),
                        Expr::nat_lit(0),
                        Expr::nat_lit(3),
                        Expr::nat_lit(0),
                        Expr::nat_lit(0),
                        ir_list("IRTy", [app("IRTy.uint_", [Expr::nat_lit(32)])])
                    ]
                )
            );
        }
        // These are syntax differences. Pointer-independent unmodelled Release
        // is NOT a false semantic endpoint, so no swapped-pointer TypeMismatch is asserted.
    }
    assert!(trust_ir_build::validate_module_for_codegen(&m).iter().any(|e|matches!(e,trust_ir_build::ValidationError::UngatedBodyForCodegen{function,..} if *function==71)));
}
