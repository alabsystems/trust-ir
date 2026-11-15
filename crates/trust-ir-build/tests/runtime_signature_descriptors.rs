// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "source-value-operational")]
//! Retained signature descriptors and actual fixed-profile U32 proof consumers.
use trust_ir::{Endianness, FuncId, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker, TypeError,
};
use trust_ir_build::core_execution::Limits;
use trust_ir_build::core_reflection::{
    CoreSignatureDescriptorProfileV1, reflect_core_module_v1,
    reflect_core_module_with_runtime_signature_descriptors_v1,
};
use trust_ir_build::{
    ModuleBuilder, check_u32_straight_line_source_value,
    check_u32_straight_line_source_value_with_runtime_signature_descriptors,
    check_uint_source_value_equation,
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
    for (name, params, returns) in [
        ("float_parameter", vec![Ty::F64], vec![Ty::Ptr]),
        ("float_return", vec![Ty::Ptr], vec![Ty::F64]),
        ("variadic", vec![Ty::U32], vec![Ty::Ptr]),
        ("float32_parameter", vec![Ty::F32], vec![]),
    ] {
        let signature = builder.add_func_type(params, returns);
        builder.declare_function(name, signature);
    }
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
    let mut module = builder.build().unwrap();
    module.func_types[2].is_vararg = true;
    module.functions[1].calling_conv = trust_ir::CallingConv::Fast;
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
            Expr::nat_lit(4),
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
            Expr::nat_lit(4u64),
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

fn addresses(module: &Module) -> Vec<(FuncId, u64)> {
    module
        .functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, 4096 + 16 * i as u64))
        .collect()
}
fn list_values(mut term: &Expr) -> Vec<Expr> {
    let mut result = Vec::new();
    loop {
        let head = term.get_app_fn();
        let args = term.get_app_args();
        if head == &Expr::const_str("IRList.nil") {
            assert_eq!(args.len(), 1);
            return result;
        }
        assert_eq!(head, &Expr::const_str("IRList.cons"));
        assert_eq!(args.len(), 3);
        result.push(args[1].clone());
        term = args[2];
    }
}
#[test]
fn all_original_signature_function_and_layout_rows_are_retained() {
    let (module, _, _, _) = fixture(Program::Mixed);
    let before = module.clone();
    assert!(reflect_core_module_v1(&module, &addresses(&module)).is_err());
    let reflected =
        reflect_core_module_with_runtime_signature_descriptors_v1(&module, &addresses(&module))
            .unwrap();
    assert!(std::ptr::eq(reflected.module(), &module));
    assert_eq!(
        reflected.signature_descriptor_profile(),
        CoreSignatureDescriptorProfileV1::RuntimeDeclarationsV1
    );
    let context = reflected.context_term().get_app_args();
    assert_eq!(context.len(), 5);
    let signatures = list_values(context[2]);
    assert_eq!(signatures.len(), module.func_types.len());
    for (id, (term, sig)) in signatures.iter().zip(&module.func_types).enumerate() {
        let a = term.get_app_args();
        assert_eq!(a[0], &Expr::nat_lit(id as u64));
        assert_eq!(
            a[3],
            &Expr::const_str(if sig.is_vararg {
                "Bool.true"
            } else {
                "Bool.false"
            })
        );
        assert_eq!(list_values(a[1]).len(), sig.params.len());
        assert_eq!(list_values(a[2]).len(), sig.returns.len());
    }
    assert_eq!(
        list_values(signatures[0].get_app_args()[1]),
        vec![app("IRTy.float_", [Expr::nat_lit(64)])]
    );
    assert_eq!(
        list_values(signatures[1].get_app_args()[2]),
        vec![app("IRTy.float_", [Expr::nat_lit(64)])]
    );
    assert_eq!(
        list_values(signatures[3].get_app_args()[1]),
        vec![app("IRTy.float_", [Expr::nat_lit(32)])]
    );
    let funcs = list_values(context[3]);
    assert_eq!(funcs.len(), module.functions.len());
    for (term, f) in funcs.iter().zip(&module.functions) {
        let a = term.get_app_args();
        assert_eq!(a[0], &Expr::nat_lit(u64::from(f.id.index())));
        assert_eq!(a[1], &Expr::nat_lit(u64::from(f.ty.index())));
        assert_eq!(a[2], &Expr::nat_lit(4096 + 16 * u64::from(f.id.index())));
        assert_eq!(
            a[3],
            &Expr::nat_lit(if f.calling_conv == trust_ir::CallingConv::Fast {
                1
            } else {
                0
            })
        );
        assert_eq!(
            a[4],
            &Expr::const_str(if f.is_declaration() {
                "Bool.true"
            } else {
                "Bool.false"
            })
        );
        assert!(std::ptr::eq(reflected.function(f.id).unwrap(), f));
    }
    let layouts = list_values(context[1]);
    for (bits, bytes) in [(32, 4), (64, 8)] {
        let row = layouts
            .iter()
            .find(|x| x.get_app_args()[0] == &app("IRTy.float_", [Expr::nat_lit(bits)]))
            .unwrap();
        let a = row.get_app_args();
        assert_eq!(a[1], &Expr::nat_lit(bytes));
        assert_eq!(a[2], &Expr::nat_lit(bytes));
    }
    assert_eq!(module, before);
}
#[test]
fn genuine_opt_in_u32_caller_checks_both_complete_independent_contracts() {
    for program in [Program::Mixed, Program::ProductOffset] {
        let (module, env, source, theorem) = fixture(program);
        let value =
            check_uint_source_value_equation(&module, FuncId::new(4), &env, &source, &theorem)
                .unwrap();
        assert!(
            check_u32_straight_line_source_value(&value, &addresses(&module), limits()).is_err()
        );
        let checked = check_u32_straight_line_source_value_with_runtime_signature_descriptors(
            &value,
            &addresses(&module),
            limits(),
        )
        .unwrap();
        assert!(std::ptr::eq(checked.source_value(), &value));
        assert_eq!(
            checked.signature_descriptor_profile(),
            CoreSignatureDescriptorProfileV1::RuntimeDeclarationsV1
        );
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
            for fuel in [0, 10] {
                let goal = config_equality(
                    actual_run(checked.context().clone(), raw.clone(), memory(bad), fuel),
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
                        raw.clone(),
                        Expr::nat_lit(fuel),
                    ],
                );
                check_point(checked.environment(), &proof, &goal, true);
            }
        }
    }
}
fn call_state(argument: Expr) -> Expr {
    app(
        "IRMachine.mk",
        [
            ir_list(
                "IRFrame",
                [app(
                    "IRFrame.mk",
                    [
                        Expr::nat_lit(4),
                        Expr::nat_lit(0),
                        Expr::nat_lit(0),
                        ir_list(
                            "IRBinding",
                            [app("IRBinding.mk", [Expr::nat_lit(70), argument])],
                        ),
                        ir_list("Nat", []),
                    ],
                )],
            ),
            ir_list("IRMemSlot", []),
            Expr::nat_lit(0),
        ],
    )
}
fn effect_provider(bad: bool) -> Expr {
    let result = app(
        "IRByteImportResultV1.mk",
        [
            Expr::const_str("Nat"),
            app(
                "IROutcome.ret",
                [ir_list(
                    "IRScalar",
                    [app("IRScalar.float_", [Expr::nat_lit(0)])],
                )],
            ),
            memory(bad),
            Expr::nat_lit(123),
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
    .fold(result, |b, t| Expr::lam(BinderInfo::Default, t, b))
}
#[test]
fn canonical_activation_keeps_pre_provider_refusals_and_post_provider_world_errors() {
    let (module, env, source, theorem) = fixture(Program::Mixed);
    let value =
        check_uint_source_value_equation(&module, FuncId::new(4), &env, &source, &theorem).unwrap();
    let checked = check_u32_straight_line_source_value_with_runtime_signature_descriptors(
        &value,
        &addresses(&module),
        limits(),
    )
    .unwrap();
    for (fid, arg, cc, return_type, post_provider) in [
        (
            0,
            app("IRScalar.float_", [Expr::nat_lit(0)]),
            0,
            Expr::const_str("IRTy.ptr_"),
            false,
        ),
        (2, integer(3), 0, Expr::const_str("IRTy.ptr_"), false),
        (
            1,
            app("IRScalar.ptr_", [Expr::nat_lit(16)]),
            1,
            app("IRTy.float_", [Expr::nat_lit(64)]),
            true,
        ),
    ] {
        for bad in [false, true] {
            let site = app(
                "IRByteSiteV1.mk",
                [
                    Expr::nat_lit(4),
                    Expr::nat_lit(0),
                    Expr::nat_lit(0),
                    Expr::nat_lit(0),
                    Expr::nat_lit(cc),
                    ir_list("IRTy", [return_type.clone()]),
                ],
            );
            let actual = app(
                "ir_byte_call_v1",
                [
                    Expr::const_str("Nat"),
                    checked.context().clone(),
                    effect_provider(bad),
                    call_state(arg.clone()),
                    world(memory(false), &[1], 2),
                    ir_list("Nat", [Expr::nat_lit(80)]),
                    site,
                    Expr::nat_lit(fid),
                    ir_list("Nat", [Expr::nat_lit(70)]),
                ],
            );
            let expected = if post_provider {
                app(
                    "IRByteConfigV1.halted",
                    [
                        Expr::const_str("Nat"),
                        app(
                            "IROutcome.type_error",
                            [Expr::const_str(if bad {
                                "IRFault.bad_addr"
                            } else {
                                "IRFault.bad_field"
                            })],
                        ),
                        app(
                            "IRByteWorldV1.mk",
                            [
                                Expr::const_str("Nat"),
                                memory(bad),
                                Expr::nat_lit(123),
                                ir_list("Nat", [Expr::nat_lit(1)]),
                                Expr::nat_lit(2),
                            ],
                        ),
                    ],
                )
            } else {
                halted(
                    memory(false),
                    &[1],
                    2,
                    app(
                        "IROutcome.type_error",
                        [Expr::const_str("IRFault.not_fnptr")],
                    ),
                )
            };
            let goal = config_equality(actual, expected.clone());
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
fn malformed_metadata_identity_target_and_structural_bounds_still_refuse() {
    let (module, _, _, _) = fixture(Program::Mixed);
    let reflect = |m: &Module| {
        reflect_core_module_with_runtime_signature_descriptors_v1(m, &addresses(m)).map(|_| ())
    };
    let mut changed = module.clone();
    changed.target_info.as_mut().unwrap().pointer_size = 4;
    assert!(reflect(&changed).is_err());
    let mut changed = module.clone();
    changed.functions[0].attrs.readnone = true;
    assert!(
        reflect(&changed)
            .unwrap_err()
            .to_string()
            .contains("function claims")
    );
    let mut changed = module.clone();
    changed.functions[1].id = changed.functions[0].id;
    assert!(reflect(&changed).is_err());
    let mut changed = module.clone();
    let mut ty = Ty::F32;
    for _ in 0..65 {
        ty = Ty::PtrConst(Box::new(ty));
    }
    changed.func_types[0].params = vec![ty];
    assert!(
        reflect(&changed)
            .unwrap_err()
            .to_string()
            .contains("size or depth")
    );
    let mut changed = module.clone();
    changed
        .func_types
        .resize(65_537, changed.func_types[0].clone());
    assert!(
        reflect(&changed)
            .unwrap_err()
            .to_string()
            .contains("table limit")
    );
    let mut changed = module.clone();
    changed.functions[4].blocks[0].body[0]
        .proofs
        .push(trust_ir::ProofAnnotation::NoWrap);
    assert!(
        reflect(&changed)
            .unwrap_err()
            .to_string()
            .contains("instruction annotation")
    );
    use trust_ir::signature_abi::{AbiArgument, AbiFrontend, AbiPassMode, AbiTarget, SignatureAbi};
    let abi = SignatureAbi {
        target: AbiTarget {
            triple: "aarch64-apple-darwin".into(),
            data_layout: "e-p:64:64".into(),
            abi: "aapcs64".into(),
            cpu: "generic".into(),
            features: vec![],
            target_spec: format!("sha256:{}", "0".repeat(64)),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "reflection-test".into(),
            revision: "fixture".into(),
        },
        convention: "C".into(),
        lowered_convention: trust_ir::CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: 0,
        arguments: vec![],
        result: AbiArgument {
            size: 0,
            align: 1,
            mode: AbiPassMode::Ignore,
            bindings: vec![],
        },
    };
    let mut changed = module.clone();
    changed.func_types.push(trust_ir::FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
        abi: Some(abi),
    });
    assert!(
        reflect(&changed)
            .unwrap_err()
            .to_string()
            .contains("typed signature ABI")
    );
    let mut wrong = addresses(&module);
    wrong[1].1 = wrong[0].1;
    assert!(reflect_core_module_with_runtime_signature_descriptors_v1(&module, &wrong).is_err());
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
    let reflection = reflect_core_module_with_runtime_signature_descriptors_v1(&module, &addresses);
    let operational = check_u32_straight_line_source_value_with_runtime_signature_descriptors(
        &source_value,
        &addresses,
        limits(),
    );
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
