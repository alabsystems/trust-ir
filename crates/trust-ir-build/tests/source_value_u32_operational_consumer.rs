// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "source-value-operational")]
//! Independently authored U32 sources and actual Core observations; no body license.
use trust_ir::inst::{BinOp, Inst};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::{
    Constant, Endianness, FuncId, Module, StructPassingPolicy, TargetInfo, Ty, ValueId,
};
use trust_ir_build::clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker, TypeError,
};
use trust_ir_build::core_execution::Limits;
use trust_ir_build::{
    ModuleBuilder, SourceValueEquationError, check_u32_straight_line_source_value,
    check_u64_straight_line_source_value, check_uint_source_value_equation,
};
#[derive(Clone, Copy, Debug)]
enum Program {
    Mixed,
    ProductOffset,
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}
fn modulus(width: u64) -> Expr {
    Expr::nat_lit_u128(1_u128 << width)
}
fn den(op: &str, width: u64, a: Expr, b: Expr) -> Expr {
    app("Nat.mod", [app(op, [a, b]), modulus(width)])
}
fn fixture(program: Program) -> (Module, Environment, Name, Declaration) {
    fixture_at(program, 32)
}
fn fixture_at(program: Program, width: u64) -> (Module, Environment, Name, Declaration) {
    fixture_named(
        program,
        width,
        Name::from_string(&format!("AuthoredUInt{width}.{:?}", program)),
    )
}
fn fixture_named(
    program: Program,
    width: u64,
    source: Name,
) -> (Module, Environment, Name, Declaration) {
    let ty = if width == 32 { Ty::U32 } else { Ty::U64 };
    let mut builder = ModuleBuilder::new_with_target_info(
        "authored_u32_operational",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let sig = builder.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let f = builder.declare_function("authored", sig);
    let mut body = builder.define_function(f).unwrap();
    let entry = body.create_block();
    let x = body.add_block_param(entry, ty.clone());
    let y = body.add_block_param(entry, ty.clone());
    body.switch_to_block(entry);
    let result = match program {
        Program::Mixed => {
            let seven = body.uconst(ty.clone(), 7);
            let sum = body.add(ty.clone(), x, seven);
            body.mul(ty.clone(), sum, y)
        }
        Program::ProductOffset => {
            let eleven = body.uconst(ty.clone(), 11);
            let product = body.mul(ty.clone(), x, y);
            body.add(ty.clone(), product, eleven)
        }
    };
    body.ret(vec![result]);
    body.build();
    let module = builder.build().unwrap();
    let uint = if width == 32 { "UInt32" } else { "UInt64" };
    let to_nat = |x| app(&format!("{uint}.toNat"), [x]);
    let x = Expr::bvar(1);
    let y = Expr::bvar(0);
    let (expression, denotation) = match program {
        Program::Mixed => (
            app(
                &format!("{uint}.mul"),
                [
                    app(
                        &format!("{uint}.add"),
                        [x.clone(), app(&format!("{uint}.ofNat"), [Expr::nat_lit(7)])],
                    ),
                    y.clone(),
                ],
            ),
            den(
                "Nat.mul",
                width,
                den("Nat.add", width, to_nat(x), Expr::nat_lit(7)),
                to_nat(y),
            ),
        ),
        Program::ProductOffset => (
            app(
                &format!("{uint}.add"),
                [
                    app(&format!("{uint}.mul"), [x.clone(), y.clone()]),
                    app(&format!("{uint}.ofNat"), [Expr::nat_lit(11)]),
                ],
            ),
            den(
                "Nat.add",
                width,
                den("Nat.mul", width, to_nat(x), to_nat(y)),
                Expr::nat_lit(11),
            ),
        ),
    };
    let bind = |mut e, pi| {
        for _ in 0..2 {
            e = if pi {
                Expr::pi(BinderInfo::Default, Expr::const_str(uint), e)
            } else {
                Expr::lam(BinderInfo::Default, Expr::const_str(uint), e)
            }
        }
        e
    };
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: source.clone(),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_str(uint),
            Expr::arrow(Expr::const_str(uint), Expr::const_str(uint)),
        ),
        value: bind(expression, false),
        is_reducible: true,
    })
    .unwrap();
    let call = to_nat(Expr::apps(
        Expr::const_(source.clone(), vec![]),
        [Expr::bvar(1), Expr::bvar(0)],
    ));
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_str("Nat"), call.clone(), denotation],
    );
    let refl = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Nat"), call],
    );
    (
        module,
        env,
        source,
        Declaration::Theorem {
            name: Name::from_string("Untrusted.u32Equation"),
            level_params: vec![],
            type_: bind(eq, true),
            value: bind(refl, false),
        },
    )
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
fn replay(env: &Environment, claim: &Expr, proof: &Expr) {
    assert!(!claim.has_fvar_quick() && !claim.has_loose_bvars());
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
    let claim_bytes = trust_ir::proof::encode_clean_expr_dag_v2(claim).unwrap();
    let proof_bytes = trust_ir::proof::encode_clean_expr_dag_v2(proof).unwrap();
    let dc = trust_ir::proof::decode_clean_expr_dag_v2(&claim_bytes).unwrap();
    let dp = trust_ir::proof::decode_clean_expr_dag_v2(&proof_bytes).unwrap();
    assert_eq!(&dc, claim);
    assert_eq!(&dp, proof);
    for (claim, proof) in [(claim, proof), (&dc, &dp)] {
        let mut tc = TypeChecker::new(env);
        tc.set_allow_unsafe(false);
        tc.set_allow_partial(false);
        assert_eq!(tc.heartbeat_limit(), 2000000);
        tc.check_type(claim, &Expr::prop()).unwrap();
        let result = tc.check_type(proof, claim);
        assert!(
            !tc.heartbeat_spent(),
            "resource stop is not a verdict: {result:?}"
        );
        assert!(!trust_ir_build::clean_kernel::tc::declaration_budget_exhausted());
        result.unwrap();
        let audit = env.audit_certification(claim, proof);
        assert!(audit.is_certified(), "{audit:?}");
        for name in audit.dependencies {
            assert!(env.axiom_deps(&name).unwrap().is_empty());
            assert!(env.foundational_axiom_deps(&name).unwrap().is_empty());
            assert!(env.trust_marker_deps(&name).unwrap().is_empty());
        }
    }
}
#[test]
fn two_authored_sources_bind_the_exact_original_typed_and_total_claims() {
    for program in [Program::Mixed, Program::ProductOffset] {
        let (module, env, source, theorem) = fixture(program);
        let before = module.clone();
        let value =
            check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &theorem)
                .unwrap();
        let checked =
            check_u32_straight_line_source_value(&value, &[(FuncId::new(0), 4096)], limits())
                .unwrap();
        assert!(std::ptr::eq(checked.source_value(), &value));
        assert_eq!(checked.instruction_count(), 4);
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
        let audit = checked
            .environment()
            .audit_certification(checked.typed_claim(), checked.typed_proof());
        for name in [
            source.clone(),
            Name::from_string("ir_byte_run_v1"),
            Name::from_string("ir_byte_init_v1"),
        ] {
            assert!(audit.dependencies.contains(&name));
        }
        if let Some(dir) = std::env::var_os("TRUST_IR_U32_OPERATIONAL_EVIDENCE_DIR") {
            let p = std::path::PathBuf::from(dir).join(format!("{program:?}"));
            std::fs::create_dir_all(&p).unwrap();
            for (label, term) in [
                ("total-claim", checked.total_claim()),
                ("total-proof", checked.total_proof()),
                ("typed-claim", checked.typed_claim()),
                ("typed-proof", checked.typed_proof()),
            ] {
                std::fs::write(
                    p.join(format!("{label}.dag-v2")),
                    trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap(),
                )
                .unwrap();
            }
        }
        assert_eq!(module, before);
        assert!(
            check_u64_straight_line_source_value(&value, &[(FuncId::new(0), 4096)], limits())
                .is_err()
        );
    }
}
fn reference_word(module: &Module, x: u64, y: u64) -> u64 {
    let ty = module.func_types[module.functions[0].ty.as_usize()].returns[0].clone();
    let result = Interpreter::with_module(module)
        .execute_func(
            FuncId::new(0),
            [
                InterpretValue::int(ty.clone(), i128::from(x)).unwrap(),
                InterpretValue::int(ty.clone(), i128::from(y)).unwrap(),
            ],
        )
        .unwrap();
    assert_eq!(result.host_calls, 0);
    assert_eq!(result.returns.len(), 1);
    assert_eq!(result.returns[0].ty, ty);
    u64::try_from(result.returns[0].as_int().unwrap().as_unsigned()).unwrap()
}
#[test]
fn real_width_op_operand_constant_and_return_mutants_cannot_keep_the_source_equation() {
    let (module, env, source, theorem) = fixture(Program::Mixed);
    assert_eq!(reference_word(&module, 3, 5), 50);
    assert_eq!(reference_word(&module, u32::MAX.into(), 3), 18);
    for mutation in 0..6 {
        let mut changed = module.clone();
        let body = &mut changed.functions[0].blocks[0].body;
        match mutation {
            0 => {
                changed.func_types[0].params = vec![Ty::U64, Ty::U64];
                changed.func_types[0].returns = vec![Ty::U64];
                for p in &mut changed.functions[0].blocks[0].params {
                    p.1 = Ty::U64;
                }
                for node in &mut changed.functions[0].blocks[0].body {
                    match &mut node.inst {
                        Inst::Const { ty, .. } | Inst::BinOp { ty, .. } => *ty = Ty::U64,
                        _ => {}
                    }
                }
            }
            1 => {
                if let Inst::BinOp { op, .. } = &mut body[2].inst {
                    *op = BinOp::Add
                }
            }
            2 => {
                if let Inst::BinOp { lhs, .. } = &mut body[1].inst {
                    *lhs = ValueId::new(1)
                }
                if let Inst::BinOp { rhs, .. } = &mut body[2].inst {
                    *rhs = ValueId::new(0)
                }
            }
            3 => {
                if let Inst::BinOp { rhs, .. } = &mut body[2].inst {
                    *rhs = ValueId::new(0)
                }
            }
            4 => {
                if let Inst::Const { value, .. } = &mut body[0].inst {
                    *value = Constant::Int(8)
                }
            }
            _ => {
                body[3].inst = Inst::Return {
                    values: vec![ValueId::new(1)],
                }
            }
        }
        let actual = if mutation == 0 {
            reference_word(&changed, u32::MAX.into(), 3)
        } else {
            reference_word(&changed, 3, 5)
        };
        assert_ne!(actual, if mutation == 0 { 18 } else { 50 });
        match check_uint_source_value_equation(&changed, FuncId::new(0), &env, &source, &theorem) {
            Err(SourceValueEquationError::Rejected(reason)) => {
                assert!(reason.contains("exact independently re-derived"))
            }
            Err(SourceValueEquationError::Unsupported(reason)) if mutation == 0 => {
                assert!(reason.contains("exact UInt signature"))
            }
            _ => panic!("mutation{mutation} did not receive the required semantic/width refusal"),
        }
    }
}
#[test]
fn constants_and_unsupported_instructions_are_refused_without_receipt_forgery() {
    let (module, env, source, theorem) = fixture(Program::Mixed);
    for constant in [-1_i128, i128::from(u32::MAX) + 1] {
        let mut changed = module.clone();
        let Inst::Const { value, .. } = &mut changed.functions[0].blocks[0].body[0].inst else {
            panic!("constant")
        };
        *value = Constant::Int(constant);
        match check_uint_source_value_equation(&changed, FuncId::new(0), &env, &source, &theorem) {
            Err(SourceValueEquationError::InvalidModule(e)) => {
                assert!(!e.is_empty());
                eprintln!("actual upstream invalid-module constant refusal {constant}: {e:?}")
            }
            Err(e) => panic!("unexpected constant refusal phase: {e}"),
            Ok(value) => {
                let e = check_u32_straight_line_source_value(
                    &value,
                    &[(FuncId::new(0), 4096)],
                    limits(),
                )
                .err()
                .expect("operational profile rejects noncanonical literal");
                assert!(e.0.contains("only actual U32"));
            }
        }
    }
    let mut changed = module.clone();
    changed.functions[0].blocks[0].body.insert(
        1,
        trust_ir::InstrNode::new(Inst::Copy {
            ty: Ty::U32,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(8)),
    );
    let result =
        check_uint_source_value_equation(&changed, FuncId::new(0), &env, &source, &theorem);
    assert!(matches!(
        result,
        Err(SourceValueEquationError::Unsupported(_))
    ));
    let (u64module, u64env, u64source, u64theorem) = fixture_at(Program::Mixed, 64);
    let value = check_uint_source_value_equation(
        &u64module,
        FuncId::new(0),
        &u64env,
        &u64source,
        &u64theorem,
    )
    .unwrap();
    let e = check_u64_straight_line_source_value(&value, &[(FuncId::new(0), 4096)], limits())
        .err()
        .unwrap();
    assert!(e.0.contains("only actual U64"));
}
#[test]
fn unsupported_calls_casts_overflow_asserts_and_annotations_keep_their_refusal_phase() {
    let (module, env, source, theorem) = fixture(Program::Mixed);
    for case in 0..5 {
        let mut changed = module.clone();
        let body = &mut changed.functions[0].blocks[0].body;
        match case {
            0 => body.insert(
                1,
                trust_ir::InstrNode::new(Inst::Call {
                    callee: FuncId::new(0),
                    args: vec![ValueId::new(0), ValueId::new(1)],
                })
                .with_result(ValueId::new(8)),
            ),
            1 => body.insert(
                1,
                trust_ir::InstrNode::new(Inst::Cast {
                    op: trust_ir::CastOp::ZExt,
                    src_ty: Ty::U32,
                    dst_ty: Ty::U64,
                    operand: ValueId::new(0),
                })
                .with_result(ValueId::new(8)),
            ),
            2 => body.insert(
                1,
                trust_ir::InstrNode::new(Inst::Overflow {
                    op: trust_ir::OverflowOp::MulOverflow,
                    ty: Ty::U32,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_results([ValueId::new(8), ValueId::new(9)]),
            ),
            3 => {
                body.insert(
                    1,
                    trust_ir::InstrNode::new(Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(true),
                    })
                    .with_result(ValueId::new(8)),
                );
                body.insert(
                    2,
                    trust_ir::InstrNode::new(Inst::Assert {
                        cond: ValueId::new(8),
                        kind: trust_ir::AssertKind::Unspecified,
                        site: None,
                    }),
                );
            }
            _ => body[1].proofs.push(trust_ir::ProofAnnotation::NoWrap),
        }
        match check_uint_source_value_equation(&changed, FuncId::new(0), &env, &source, &theorem) {
            Ok(value) => {
                let err = check_u32_straight_line_source_value(
                    &value,
                    &[(FuncId::new(0), 4096)],
                    limits(),
                )
                .err()
                .expect("unsupported operation cannot receive operational receipt");
                eprintln!("actual operational refusal case{case}: {err}");
                assert!(
                    err.0.contains("only actual U32")
                        || err.0.contains("annotation")
                        || err.0.contains("unsupported")
                );
            }
            Err(SourceValueEquationError::Unsupported(reason)) => {
                eprintln!("actual upstream reader refusal case{case}: {reason}")
            }
            Err(SourceValueEquationError::InvalidModule(errors)) => {
                assert!(!errors.is_empty());
                eprintln!("actual upstream validator refusal case{case}: {errors:?}");
            }
            Err(other) => panic!("unexpected refusal (not a resource verdict): {other}"),
        }
    }
}
#[test]
fn resource_exhaustion_and_model_name_collision_do_not_return_checked_values() {
    let (module, env, source, theorem) = fixture(Program::Mixed);
    let value =
        check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &theorem).unwrap();
    let mut small = limits();
    small.max_operations = 1;
    let e = check_u32_straight_line_source_value(&value, &[(FuncId::new(0), 4096)], small)
        .err()
        .unwrap();
    assert!(e.0.contains("operation budget"));
    let (module, env, source, theorem) =
        fixture_named(Program::Mixed, 32, Name::from_string("ir_byte_run_v1"));
    let value =
        check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &theorem).unwrap();
    let e = check_u32_straight_line_source_value(&value, &[(FuncId::new(0), 4096)], limits())
        .err()
        .unwrap();
    assert!(e.0.contains("collision"));
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
fn expected_prefix(program: Program, fuel: u64) -> Expr {
    let values = match program {
        Program::Mixed => [7, 10, 50],
        Program::ProductOffset => [11, 15, 26],
    };
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
            Expr::nat_lit(0),
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
fn actual_core_prefixes_errors_typed_linkage_and_wrapping_results_are_independent_normal_forms() {
    for program in [Program::Mixed, Program::ProductOffset] {
        let (module, env, source, theorem) = fixture(program);
        let value =
            check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &theorem)
                .unwrap();
        let checked =
            check_u32_straight_line_source_value(&value, &[(FuncId::new(0), 4096)], limits())
                .unwrap();
        for fuel in [0, 1, 2, 3, 4, 10] {
            let expected = expected_prefix(program, fuel);
            let goal = config_equality(
                actual_run(
                    checked.context().clone(),
                    ir_list("IRScalar", [integer(3), integer(5)]),
                    memory(false),
                    fuel,
                ),
                expected.clone(),
            );
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
                    Expr::nat_lit(99),
                    providers(),
                    app("UInt32.ofNat", [Expr::nat_lit(3)]),
                    app("UInt32.ofNat", [Expr::nat_lit(5)]),
                    Expr::nat_lit(fuel),
                ],
            );
            check_point(checked.environment(), &proof, &goal, true);
            let total = Expr::apps(
                checked.total_proof().clone(),
                [
                    Expr::const_str("Nat"),
                    memory(false),
                    Expr::nat_lit(99),
                    providers(),
                    ir_list("IRScalar", [integer(3), integer(5)]),
                    Expr::nat_lit(fuel),
                ],
            );
            check_point(checked.environment(), &total, &goal, true);
        }
        for arguments in [
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
            ir_list("IRScalar", [integer(3), integer(1_u64 << 32)]),
            ir_list("IRScalar", [integer(1_u64 << 32), integer(0)]),
        ] {
            for bad in [false, true] {
                let (owners, next, fault) = if bad {
                    (vec![8], 9, "IRFault.bad_addr")
                } else {
                    (vec![1], 2, "IRFault.bad_field")
                };
                let expected = halted(
                    memory(bad),
                    &owners,
                    next,
                    app("IROutcome.type_error", [Expr::const_str(fault)]),
                );
                for fuel in [0, 10] {
                    let goal = config_equality(
                        actual_run(
                            checked.context().clone(),
                            arguments.clone(),
                            memory(bad),
                            fuel,
                        ),
                        expected.clone(),
                    );
                    check_point(
                        checked.environment(),
                        &config_reflexivity(expected.clone()),
                        &goal,
                        true,
                    );
                    let proof = Expr::apps(
                        checked.total_proof().clone(),
                        [
                            Expr::const_str("Nat"),
                            memory(bad),
                            Expr::nat_lit(99),
                            providers(),
                            arguments.clone(),
                            Expr::nat_lit(fuel),
                        ],
                    );
                    check_point(checked.environment(), &proof, &goal, true);
                }
            }
        }
        for (x, y, result) in match program {
            Program::Mixed => vec![(u64::from(u32::MAX), 3, 18), ((1_u64 << 31) - 7, 2, 0)],
            Program::ProductOffset => vec![(u64::from(u32::MAX), 2, 9)],
        } {
            assert_eq!(reference_word(&module, x, y), result);
            let expected = halted(
                memory(false),
                &[],
                2,
                app("IROutcome.ret", [ir_list("IRScalar", [integer(result)])]),
            );
            let goal = config_equality(
                actual_run(
                    checked.context().clone(),
                    ir_list("IRScalar", [integer(x), integer(y)]),
                    memory(false),
                    10,
                ),
                expected.clone(),
            );
            check_point(
                checked.environment(),
                &config_reflexivity(expected),
                &goal,
                true,
            );
        }
    }
}

#[test]
fn the_complete_actual_clean_module_is_still_intact_and_refused_by_the_u32_factory() {
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
        let trust_ir_build::clean_kernel::ExprKind::Const(name, levels) = expression.kind() else {
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
    let operational = check_u32_straight_line_source_value(&source_value, &addresses, limits());
    let expected =
        reflection.expect_err("intact full actual Clean module remains outside this reflector");
    let observed = operational
        .err()
        .expect("a new U32 entry cannot bypass the full-module refusal");
    assert_eq!(observed.to_string(), expected.to_string());
    assert!(
        observed
            .0
            .contains("module table requires an explicit byte-profile interpretation")
    );
    eprintln!("ACTUAL_CLEAN_U32_PROFILE_REFUSAL={observed}");
    let strict = trust_ir_build::validate_module_for_codegen(&module);
    assert!(strict.iter().any(|error| matches!(error,
        trust_ir_build::ValidationError::UngatedBodyForCodegen { function, .. }
            if *function == helper.index())));
    assert_eq!(module, before);
}

#[test]
fn an_independently_checked_u32_sub_source_is_refused_by_the_fixed_operational_profile() {
    // This is a real shared-reader receipt, not forged source-value metadata.
    // The two UInt32 arguments are intentionally unused; 7-3 has literal4.
    let (mut module, _, _, _) = fixture(Program::Mixed);
    let body = &mut module.functions[0].blocks[0].body;
    body[1].inst = Inst::Const {
        ty: Ty::U32,
        value: Constant::Int(3),
    };
    body[2].inst = Inst::BinOp {
        op: BinOp::Sub,
        ty: Ty::U32,
        lhs: ValueId::new(2),
        rhs: ValueId::new(3),
    };
    let source = Name::from_string("AuthoredUInt32.constantSub");
    let uint = Expr::const_str("UInt32");
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: source.clone(),
        level_params: vec![],
        type_: Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
        value: Expr::lam(
            BinderInfo::Default,
            uint.clone(),
            Expr::lam(
                BinderInfo::Default,
                uint.clone(),
                app("UInt32.ofNat", [Expr::nat_lit(4)]),
            ),
        ),
        is_reducible: true,
    })
    .unwrap();
    let word = app(
        "UInt32.toNat",
        [Expr::apps(
            Expr::const_(source.clone(), vec![]),
            [Expr::bvar(1), Expr::bvar(0)],
        )],
    );
    let denotation = app(
        "Nat.mod",
        [
            app(
                "Nat.sub",
                [
                    app("Nat.add", [Expr::nat_lit(7), modulus(32)]),
                    Expr::nat_lit(3),
                ],
            ),
            modulus(32),
        ],
    );
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_str("Nat"), word.clone(), denotation],
    );
    let refl = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Nat"), word],
    );
    let close = |body, pi| {
        if pi {
            Expr::pi(
                BinderInfo::Default,
                uint.clone(),
                Expr::pi(BinderInfo::Default, uint.clone(), body),
            )
        } else {
            Expr::lam(
                BinderInfo::Default,
                uint.clone(),
                Expr::lam(BinderInfo::Default, uint.clone(), body),
            )
        }
    };
    let theorem = Declaration::Theorem {
        name: Name::from_string("Untrusted.constantSub"),
        level_params: vec![],
        type_: close(eq, true),
        value: close(refl, false),
    };
    assert_eq!(reference_word(&module, 3, 5), 4);
    let value = check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &theorem)
        .expect("shared source reader really accepts the ordinary Sub equation");
    let err = check_u32_straight_line_source_value(&value, &[(FuncId::new(0), 4096)], limits())
        .err()
        .expect("fixed operational profile does not admit Sub");
    assert_eq!(
        err.0,
        "operational source-value supports only actual U32 Const/Add/Mul and final Return"
    );
    eprintln!("CHECKED_U32_SUB_PROFILE_REFUSAL={err}");
}
