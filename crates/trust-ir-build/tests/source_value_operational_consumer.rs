// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "source-value-operational")]

//! Ordinary authored source/body pairs, independent of the operational builder.
//! These checks do not grant a body license or frontend/native assurance.

use trust_ir::inst::{BinOp, Inst};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::{Endianness, FuncId, Module, StructPassingPolicy, TargetInfo, Ty, ValueId};
use trust_ir_build::clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, ExprKind, Level, Name, TypeChecker, TypeError,
};
use trust_ir_build::core_execution::Limits;
use trust_ir_build::{
    ModuleBuilder, SourceValueEquationError, check_u64_straight_line_source_value,
    check_uint_source_value_equation,
};

#[derive(Clone, Copy, Debug)]
enum Program {
    Weighted,
    LiteralOffset,
}

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}

fn modulo_sum(a: Expr, b: Expr) -> Expr {
    app(
        "Nat.mod",
        [app("Nat.add", [a, b]), Expr::nat_lit_u128(1u128 << 64)],
    )
}

fn to_nat(value: Expr) -> Expr {
    app("UInt64.toNat", [value])
}

fn fixture(program: Program) -> (Module, Environment, Name, Declaration) {
    fixture_named(
        program,
        Name::from_string(match program {
            Program::Weighted => "Ordinary.weighted",
            Program::LiteralOffset => "Ordinary.literalOffset",
        }),
    )
}

fn fixture_named(program: Program, source: Name) -> (Module, Environment, Name, Declaration) {
    let mut builder = ModuleBuilder::new_with_target_info(
        "ordinary_source_execution",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let function = builder.declare_function("ordinary", signature);
    let mut body = builder.define_function(function).unwrap();
    let entry = body.create_block();
    let x = body.add_block_param(entry, Ty::U64);
    let y = body.add_block_param(entry, Ty::U64);
    body.switch_to_block(entry);
    let result = match program {
        Program::Weighted => {
            let twice_y = body.add(Ty::U64, y, y);
            body.add(Ty::U64, x, twice_y)
        }
        Program::LiteralOffset => {
            let constant = body.uconst(Ty::U64, 17);
            body.add(Ty::U64, x, constant)
        }
    };
    body.ret(vec![result]);
    body.build();
    let module = builder.build().unwrap();

    // Source order is x,y; the innermost de Bruijn variable is y.
    let x = Expr::bvar(1);
    let y = Expr::bvar(0);
    let (source_body, denotation) = match program {
        Program::Weighted => (
            app(
                "UInt64.add",
                [x.clone(), app("UInt64.add", [y.clone(), y.clone()])],
            ),
            modulo_sum(to_nat(x), modulo_sum(to_nat(y.clone()), to_nat(y))),
        ),
        Program::LiteralOffset => (
            app(
                "UInt64.add",
                [x.clone(), app("UInt64.ofNat", [Expr::nat_lit(17u64)])],
            ),
            modulo_sum(to_nat(x), Expr::nat_lit(17u64)),
        ),
    };
    let uint = Expr::const_str("UInt64");
    let bind = |mut expression, theorem| {
        for _ in 0..2 {
            expression = if theorem {
                Expr::pi(BinderInfo::Default, uint.clone(), expression)
            } else {
                Expr::lam(BinderInfo::Default, uint.clone(), expression)
            };
        }
        expression
    };
    let mut environment = Environment::with_prelude();
    environment
        .add_decl(Declaration::Definition {
            name: source.clone(),
            level_params: vec![],
            type_: Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
            value: bind(source_body, false),
            is_reducible: true,
        })
        .unwrap();
    let source_word = to_nat(Expr::apps(
        Expr::const_(source.clone(), vec![]),
        [Expr::bvar(1), Expr::bvar(0)],
    ));
    let equality = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_str("Nat"), source_word.clone(), denotation],
    );
    let reflexivity = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Nat"), source_word],
    );
    let theorem = Declaration::Theorem {
        name: Name::from_string("Untrusted.sourceEquation"),
        level_params: vec![],
        type_: bind(equality, true),
        value: bind(reflexivity, false),
    };
    (module, environment, source, theorem)
}

fn limits() -> Limits {
    Limits {
        max_operations: 20_000,
        max_locals: 4_096,
        max_list_items: 4_096,
        max_lookup_candidates: 1_024,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 100_000,
    }
}

fn replay(environment: &Environment, claim: &Expr, proof: &Expr) {
    assert!(!claim.has_fvar_quick() && !claim.has_loose_bvars());
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
    assert!(environment.audit_certification(claim, proof).is_certified());
    let mut checker = TypeChecker::new(environment);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(2_000_000);
    checker.set_max_cache_entries(100_000);
    checker
        .check_type(claim, &Expr::sort(Level::zero()))
        .unwrap();
    checker
        .check_type(proof, claim)
        .expect("complete strict claim replay");
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(proof).unwrap();
    let restored = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
    assert_eq!(&restored, proof);
    checker
        .check_type(&restored, claim)
        .expect("lossless DAG strict replay");
    assert!(!checker.heartbeat_spent());
    assert!(!trust_ir_build::clean_kernel::tc::declaration_budget_exhausted());
}

#[test]
fn two_ordinary_sources_replay_complete_typed_and_arbitrary_argument_contracts() {
    for program in [Program::Weighted, Program::LiteralOffset] {
        let (module, environment, source, theorem) = fixture(program);
        let before = module.clone();
        let source_value = check_uint_source_value_equation(
            &module,
            FuncId::new(0),
            &environment,
            &source,
            &theorem,
        )
        .unwrap();
        let operational = check_u64_straight_line_source_value(
            &source_value,
            &[(FuncId::new(0), 4096)],
            limits(),
        )
        .unwrap();
        assert!(std::ptr::eq(operational.source_value(), &source_value));
        assert_eq!(
            operational.instruction_count(),
            match program {
                Program::Weighted => 3,
                Program::LiteralOffset => 3,
            }
        );
        replay(
            operational.environment(),
            operational.typed_claim(),
            operational.typed_proof(),
        );
        replay(
            operational.environment(),
            operational.total_claim(),
            operational.total_proof(),
        );
        if let Some(root) = std::env::var_os("TRUST_IR_SOURCE_OPERATIONAL_EVIDENCE_DIR") {
            let directory = std::path::PathBuf::from(root).join(match program {
                Program::Weighted => "weighted",
                Program::LiteralOffset => "literal-offset",
            });
            std::fs::create_dir_all(&directory).unwrap();
            // Mathematical terms only; replay still needs this exact fixture's
            // original declarations and the pinned canonical model environment.
            for (name, expression) in [
                ("typed-claim", operational.typed_claim()),
                ("typed-proof", operational.typed_proof()),
                ("total-claim", operational.total_claim()),
                ("total-proof", operational.total_proof()),
            ] {
                std::fs::write(
                    directory.join(format!("{name}.dag-v2")),
                    trust_ir::proof::encode_clean_expr_dag_v2(expression).unwrap(),
                )
                .unwrap();
            }
        }
        let audit = operational
            .environment()
            .audit_certification(operational.typed_claim(), operational.typed_proof());
        for required in [
            source.clone(),
            Name::from_string("ir_byte_run_v1"),
            Name::from_string("ir_byte_init_v1"),
        ] {
            assert!(
                audit.dependencies.contains(&required),
                "missing actual source/model root {required:?}"
            );
        }
        assert_eq!(
            module, before,
            "a mathematical consumer cannot rewrite or license its subject"
        );
    }
}

fn reference_word(module: &Module, x: u64, y: u64) -> u64 {
    let result = Interpreter::with_module(module)
        .execute_func(
            FuncId::new(0),
            [
                InterpretValue::int(Ty::U64, i128::from(x)).unwrap(),
                InterpretValue::int(Ty::U64, i128::from(y)).unwrap(),
            ],
        )
        .unwrap();
    assert_eq!(result.host_calls, 0);
    assert_eq!(result.returns.len(), 1);
    assert_eq!(result.returns[0].ty, Ty::U64);
    u64::try_from(result.returns[0].as_int().unwrap().as_unsigned()).unwrap()
}

#[test]
fn weighted_body_mutants_have_different_actual_reference_results_before_source_refusal() {
    let (module, environment, source, theorem) = fixture(Program::Weighted);
    assert_eq!(reference_word(&module, 3, 5), 13);
    assert_eq!(reference_word(&module, u64::MAX, 1), 1);
    for mutation in 0..3 {
        let mut changed = module.clone();
        let body = &mut changed.functions[0].blocks[0].body;
        match mutation {
            0 => {
                body[0].inst = Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::U64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(0),
                };
                body[1].inst = Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::U64,
                    lhs: ValueId::new(1),
                    rhs: ValueId::new(2),
                };
            }
            1 => {
                body[1].inst = Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::U64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(2),
                }
            }
            _ => {
                body[2].inst = Inst::Return {
                    values: vec![ValueId::new(1)],
                }
            }
        }
        assert_ne!(reference_word(&changed, 3, 5), 13);
        assert!(matches!(
            check_uint_source_value_equation(
                &changed,
                FuncId::new(0),
                &environment,
                &source,
                &theorem,
            ),
            Err(SourceValueEquationError::Rejected(_))
        ));
    }
}

#[test]
fn changed_constant_is_an_actual_different_result_and_cannot_keep_the_original_source_claim() {
    let (mut module, environment, source, theorem) = fixture(Program::LiteralOffset);
    assert_eq!(reference_word(&module, 3, 5), 20);
    let Inst::Const { value, .. } = &mut module.functions[0].blocks[0].body[0].inst else {
        panic!("authored constant coordinate");
    };
    *value = trust_ir::Constant::Int(18);
    assert_eq!(reference_word(&module, 3, 5), 21);
    assert!(matches!(
        check_uint_source_value_equation(&module, FuncId::new(0), &environment, &source, &theorem,),
        Err(SourceValueEquationError::Rejected(_))
    ));
}

#[test]
fn proof_resource_exhaustion_does_not_return_a_checked_operational_value() {
    let (module, environment, source, theorem) = fixture(Program::Weighted);
    let source_value =
        check_uint_source_value_equation(&module, FuncId::new(0), &environment, &source, &theorem)
            .unwrap();
    let mut exhausted = limits();
    exhausted.max_operations = 0;
    assert!(
        check_u64_straight_line_source_value(&source_value, &[(FuncId::new(0), 4096)], exhausted,)
            .is_err()
    );
}

#[test]
fn original_source_cannot_shadow_the_operational_model_during_environment_extension() {
    let (module, environment, source, theorem) =
        fixture_named(Program::Weighted, Name::from_string("ir_byte_run_v1"));
    let source_value =
        check_uint_source_value_equation(&module, FuncId::new(0), &environment, &source, &theorem)
            .unwrap();
    assert!(
        check_u64_straight_line_source_value(&source_value, &[(FuncId::new(0), 4096)], limits(),)
            .is_err()
    );
}

#[test]
fn an_actual_copy_remains_outside_the_original_denotation_reader() {
    let (mut module, environment, source, theorem) = fixture(Program::LiteralOffset);
    let body = &mut module.functions[0].blocks[0].body;
    body.insert(
        1,
        trust_ir::InstrNode::new(Inst::Copy {
            ty: Ty::U64,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(4)),
    );
    let Inst::BinOp { lhs, .. } = &mut body[2].inst else {
        panic!("authored addition coordinate");
    };
    *lhs = ValueId::new(4);
    assert_eq!(reference_word(&module, 3, 5), 20);
    let result =
        check_uint_source_value_equation(&module, FuncId::new(0), &environment, &source, &theorem);
    assert!(matches!(
        result,
        Err(SourceValueEquationError::Unsupported(_))
    ));
}

#[test]
fn the_complete_actual_clean_module_keeps_its_profile_and_boxed_helper_boundary() {
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
        let expression = expression(raw);
        let ExprKind::Const(name, levels) = expression.kind() else {
            panic!("retained kernel name carrier");
        };
        assert!(levels.is_empty());
        name.clone()
    }
    let module = trust_ir::binary::deserialize_module(data!("module.bin")).unwrap();
    let before = module.clone();
    let mut environment = Environment::with_prelude();
    environment
        .add_decl(Declaration::Definition {
            name: name(data!("definition-0.name.bin")),
            level_params: vec![],
            type_: expression(data!("definition-0.type.bin")),
            value: expression(data!("definition-0.value.bin")),
            is_reducible: false,
        })
        .unwrap();
    let source = Name::from_string("boundActualEquation");
    assert_eq!(
        environment.closure_digest(&source).unwrap().as_slice(),
        data!("source-closure-digest.bin")
    );
    let selected = module
        .functions
        .iter()
        .find(|f| f.name == "boundActualEquation")
        .unwrap()
        .id;
    let helper = module
        .functions
        .iter()
        .find(|f| f.name == "l_boundActualEquation___boxed")
        .unwrap()
        .id;
    assert_eq!(
        module
            .functions
            .iter()
            .filter(|f| !f.is_declaration())
            .count(),
        2
    );
    let proposed = Declaration::Theorem {
        name: name(data!("theorem.name.bin")),
        level_params: vec![],
        type_: expression(data!("theorem.type.bin")),
        value: expression(data!("theorem.value.bin")),
    };
    let source_value =
        check_uint_source_value_equation(&module, selected, &environment, &source, &proposed)
            .unwrap();
    let addresses: Vec<_> = module
        .functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, 4096 + 8 * u64::try_from(i).unwrap()))
        .collect();
    // Check the complete module independently; never remove the boxed helper
    // to turn a full-module profile refusal into a selected-body success.
    let reflection = trust_ir_build::core_reflection::reflect_core_module_v1(&module, &addresses);
    let operational = check_u64_straight_line_source_value(&source_value, &addresses, limits());
    match reflection {
        Err(expected) => {
            let Err(observed) = operational else {
                panic!(
                    "an unchanged full-module reflection refusal cannot become a checked receipt"
                );
            };
            assert_eq!(observed.to_string(), expected.to_string());
            eprintln!("ACTUAL_CLEAN_PROFILE_REFUSAL={observed}");
        }
        Ok(_) => {
            let checked =
                operational.expect("the actual selected profile must be connected when admitted");
            replay(
                checked.environment(),
                checked.total_claim(),
                checked.total_proof(),
            );
            replay(
                checked.environment(),
                checked.typed_claim(),
                checked.typed_proof(),
            );
            eprintln!("ACTUAL_CLEAN_PROFILE_CONNECTED");
        }
    }
    let strict = trust_ir_build::validate_module_for_codegen(&module);
    assert!(strict.iter().any(|error| matches!(error,
        trust_ir_build::ValidationError::UngatedBodyForCodegen { function, .. }
            if *function == helper.index())));
    assert_eq!(module, before);
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

// These finite expected states are authored directly for the two fixtures;
// they call no source-value projection, SSA reader, candidate assembler or run.
fn expected_prefix(program: Program, fuel: u64) -> Expr {
    let first = match program {
        Program::Weighted => 10,
        Program::LiteralOffset => 17,
    };
    let answer = match program {
        Program::Weighted => 13,
        Program::LiteralOffset => 20,
    };
    if fuel >= 3 {
        return halted(
            memory(false),
            &[],
            2,
            app("IROutcome.ret", [ir_list("IRScalar", [integer(answer)])]),
        );
    }
    let mut bindings: Vec<(u64, u64)> = vec![(0, 3), (1, 5)];
    if fuel >= 1 {
        bindings.insert(0, (2, first));
    }
    if fuel >= 2 {
        bindings.insert(0, (3, answer));
    }
    let bindings = ir_list(
        "IRBinding",
        bindings
            .into_iter()
            .map(|(id, value)| app("IRBinding.mk", [Expr::nat_lit(id), integer(value)])),
    );
    let frame = app(
        "IRFrame.mk",
        [
            Expr::nat_lit(0u64),
            Expr::nat_lit(0u64),
            Expr::nat_lit(fuel),
            bindings,
            ir_list("Nat", []),
        ],
    );
    let machine = app(
        "IRMachine.mk",
        [
            ir_list("IRFrame", [frame]),
            ir_list("IRMemSlot", []),
            Expr::nat_lit(0u64),
        ],
    );
    app(
        "IRByteConfigV1.running",
        [
            Expr::const_str("Nat"),
            machine,
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
            Expr::nat_lit(0u64),
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
    checker.set_heartbeat_limit(2_000_000);
    checker.set_max_cache_entries(100_000);
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
fn actual_core_normal_forms_pin_all_prefixes_error_priority_and_false_claim_refusals() {
    for program in [Program::Weighted, Program::LiteralOffset] {
        let (module, environment, source, theorem) = fixture(program);
        let source_value = check_uint_source_value_equation(
            &module,
            FuncId::new(0),
            &environment,
            &source,
            &theorem,
        )
        .unwrap();
        let checked = check_u64_straight_line_source_value(
            &source_value,
            &[(FuncId::new(0), 4096)],
            limits(),
        )
        .unwrap();
        for fuel in [0, 1, 2, 3, 10] {
            let actual = actual_run(
                checked.context().clone(),
                ir_list("IRScalar", [integer(3), integer(5)]),
                memory(false),
                fuel,
            );
            let expected = expected_prefix(program, fuel);
            let goal = config_equality(actual, expected.clone());
            // First check the actual evaluator's independently stated normal form.
            check_point(
                checked.environment(),
                &config_reflexivity(expected),
                &goal,
                true,
            );
            let proof = Expr::apps(
                checked.typed_proof().clone(),
                [
                    Expr::const_str("Nat"),
                    memory(false),
                    Expr::nat_lit(99u64),
                    providers(),
                    app("UInt64.ofNat", [Expr::nat_lit(3u64)]),
                    app("UInt64.ofNat", [Expr::nat_lit(5u64)]),
                    Expr::nat_lit(fuel),
                ],
            );
            check_point(checked.environment(), &proof, &goal, true);
        }
        let bad_arguments = [
            ir_list("IRScalar", []),
            ir_list("IRScalar", [integer(3)]),
            ir_list("IRScalar", [integer(3), integer(5), integer(7)]),
            ir_list(
                "IRScalar",
                [
                    app("IRScalar.bool_", [Expr::const_str("Bool.true")]),
                    integer(5),
                ],
            ),
            ir_list(
                "IRScalar",
                [
                    integer(3),
                    app("IRScalar.int_", [Expr::nat_lit_u128(1u128 << 64)]),
                ],
            ),
        ];
        for arguments in bad_arguments {
            for bad_memory in [false, true] {
                let (owners, next, fault) = if bad_memory {
                    (vec![8], 9, "IRFault.bad_addr")
                } else {
                    (vec![1], 2, "IRFault.bad_field")
                };
                let expected = halted(
                    memory(bad_memory),
                    &owners,
                    next,
                    app("IROutcome.type_error", [Expr::const_str(fault)]),
                );
                let actual = actual_run(
                    checked.context().clone(),
                    arguments.clone(),
                    memory(bad_memory),
                    0,
                );
                let goal = config_equality(actual, expected.clone());
                check_point(
                    checked.environment(),
                    &config_reflexivity(expected),
                    &goal,
                    true,
                );
                let proof = Expr::apps(
                    checked.total_proof().clone(),
                    [
                        Expr::const_str("Nat"),
                        memory(bad_memory),
                        Expr::nat_lit(99u64),
                        providers(),
                        arguments.clone(),
                        Expr::nat_lit(0u64),
                    ],
                );
                check_point(checked.environment(), &proof, &goal, true);
            }
        }
        if matches!(program, Program::Weighted) {
            let mut changed = module.clone();
            changed.functions[0].blocks[0].body[2].inst = Inst::Return {
                values: vec![ValueId::new(1)],
            };
            let reflected = trust_ir_build::core_reflection::reflect_core_module_v1(
                &changed,
                &[(FuncId::new(0), 4096)],
            )
            .unwrap();
            let actual = actual_run(
                reflected.context_term().clone(),
                ir_list("IRScalar", [integer(3), integer(5)]),
                memory(false),
                3,
            );
            let observed = halted(
                memory(false),
                &[],
                2,
                app("IROutcome.ret", [ir_list("IRScalar", [integer(5)])]),
            );
            check_point(
                checked.environment(),
                &config_reflexivity(observed),
                &config_equality(
                    actual.clone(),
                    halted(
                        memory(false),
                        &[],
                        2,
                        app("IROutcome.ret", [ir_list("IRScalar", [integer(5)])]),
                    ),
                ),
                true,
            );
            // Actual changed-body normal form is 5 before the unchanged claim
            // of 13 is presented to the strict kernel and refused.
            let wrong_goal = config_equality(actual, expected_prefix(program, 3));
            let old_proof = Expr::apps(
                checked.typed_proof().clone(),
                [
                    Expr::const_str("Nat"),
                    memory(false),
                    Expr::nat_lit(99u64),
                    providers(),
                    app("UInt64.ofNat", [Expr::nat_lit(3u64)]),
                    app("UInt64.ofNat", [Expr::nat_lit(5u64)]),
                    Expr::nat_lit(3u64),
                ],
            );
            check_point(checked.environment(), &old_proof, &wrong_goal, false);
        }
    }
}
