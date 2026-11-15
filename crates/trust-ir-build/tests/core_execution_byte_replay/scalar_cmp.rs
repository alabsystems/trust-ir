// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reflected scalar ICmp/Return replay against the reference interpreter.
//! Every claim includes the complete terminal memory and provider world.
//! This bounded ByteV1 evidence grants no native execution authority.

use super::*;
use clean_kernel::TypeChecker;
use trust_ir::ICmpOp;
use trust_ir::interpret::{InterpretValue, Interpreter};

const OPS: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
];

#[derive(Clone, Copy, Debug)]
enum Kind {
    Bool,
    Usize,
}

impl Kind {
    fn ty(self) -> Ty {
        match self {
            Self::Bool => Ty::Bool,
            Self::Usize => Ty::Usize,
        }
    }

    fn scalar(self, value: u64) -> Expr {
        match self {
            Self::Bool => {
                assert!(value <= 1);
                boolean(value != 0)
            }
            Self::Usize => app("IRScalar.int_", [nat(value)]),
        }
    }

    fn argument(self, value: u64) -> InterpretValue {
        match self {
            Self::Bool => {
                assert!(value <= 1);
                InterpretValue::bool(value != 0)
            }
            Self::Usize => InterpretValue::int_at(Ty::Usize, i128::from(value), 64).unwrap(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct Comparison {
    kind: Kind,
    op: ICmpOp,
    lhs: u64,
    rhs: u64,
}

fn module(kind: Kind, op: ICmpOp) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "ordinary_scalar_comparison",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("darwinpcs".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let ty = kind.ty();
    let signature = builder.add_func_type(vec![ty.clone(), ty.clone()], vec![Ty::Bool]);
    let id = builder.declare_function("compare", signature);
    let mut function = builder.define_function(id).unwrap();
    let entry = function.create_block();
    let lhs = function.add_block_param(entry, ty.clone());
    let rhs = function.add_block_param(entry, ty.clone());
    function.switch_to_block(entry);
    let compared = function.icmp(op, ty, lhs, rhs);
    function.ret(vec![compared]);
    function.build();
    builder.build().expect("valid scalar comparison module")
}

fn reference(source: Comparison) -> bool {
    let module = module(source.kind, source.op);
    let outcome = Interpreter::with_module(&module)
        .execute_func(
            FuncId::new(0),
            [
                source.kind.argument(source.lhs),
                source.kind.argument(source.rhs),
            ],
        )
        .unwrap_or_else(|error| panic!("reference {source:?}: {error}"));
    assert_eq!(outcome.host_calls, 0);
    assert_eq!(outcome.steps, 2);
    assert_eq!(outcome.returns.len(), 1);
    outcome.returns[0]
        .as_bool()
        .expect("comparison returns Bool")
}

fn boolean(value: bool) -> Expr {
    app(
        "IRScalar.bool_",
        [c(if value { "Bool.true" } else { "Bool.false" })],
    )
}

fn terminal(value: bool, final_world: Expr) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app("IROutcome.ret", [list("IRScalar", &[boolean(value)])]),
            final_world,
        ],
    )
}

struct ScalarComparisonModel;

impl SourceTranslationModel for ScalarComparisonModel {
    type Source = Comparison;

    fn build_environment() -> Result<Environment, String> {
        LiteralReturnByteModel::build_environment()
    }

    fn reconstruct(source: &Comparison, target: &Module) -> Result<Expr, String> {
        let reflected = reflect_core_module_v1(target, &[(FuncId::new(0), 4096)])
            .map_err(|error| error.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let initial = app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(0),
                list(
                    "IRScalar",
                    &[
                        source.kind.scalar(source.lhs),
                        source.kind.scalar(source.rhs),
                    ],
                ),
                memory(173),
                nat(37),
            ],
        );
        Ok(eq(
            model.config_type(),
            model.run(&NatTerm::literal(2), initial),
            terminal(reference(*source), world(173, 37, &[], 9)),
        ))
    }
}

fn checker() -> &'static TranslationRechecker<ScalarComparisonModel> {
    static CHECKER: OnceLock<TranslationRechecker<ScalarComparisonModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

fn proof(value: bool, final_world: Expr) -> Vec<u8> {
    let term = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [
            app("IRByteConfigV1", [c("Nat")]),
            terminal(value, final_world),
        ],
    );
    trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap()
}

fn accepts(source: Comparison) {
    let bytes = proof(reference(source), world(173, 37, &[], 9));
    checker()
        .recheck_dag_v2(&source, &module(source.kind, source.op), &bytes)
        .unwrap_or_else(|error| panic!("actual reflected {source:?}: {error}"));
}

#[test]
fn core_scalar_icmp_baseline_bool_eq_ne_controls() {
    for op in [ICmpOp::Eq, ICmpOp::Ne] {
        for (lhs, rhs) in [(0, 0), (0, 1), (1, 0), (1, 1)] {
            accepts(Comparison {
                kind: Kind::Bool,
                op,
                lhs,
                rhs,
            });
        }
    }
}

#[test]
fn core_scalar_icmp_baseline_ordered_bool_uses_public_dispatch() {
    let source = Comparison {
        kind: Kind::Bool,
        op: ICmpOp::Slt,
        lhs: 1,
        rhs: 0,
    };
    // Signed Bool true is the one-bit value -1.
    assert!(reference(source));
    accepts(source);
}

#[test]
fn core_scalar_icmp_baseline_usize_eq_uses_public_dispatch() {
    accepts(Comparison {
        kind: Kind::Usize,
        op: ICmpOp::Eq,
        lhs: 0,
        rhs: 0,
    });
}

fn rejects(source: Comparison, target: &Module, bytes: &[u8]) {
    let error = checker()
        .recheck_dag_v2(&source, target, bytes)
        .unwrap_err();
    assert_eq!(error.stage(), "kernel audit", "{source:?}: {error}");
    assert!(
        error.reason().contains("TypeMismatch"),
        "{source:?}: {error}"
    );
}

fn bit_pattern_result(source: Comparison) -> bool {
    let Comparison { kind, op, lhs, rhs } = source;
    let signed = |value| match kind {
        Kind::Bool => -(value as i64),
        Kind::Usize => value as i64,
    };
    match op {
        ICmpOp::Eq => lhs == rhs,
        ICmpOp::Ne => lhs != rhs,
        ICmpOp::Ult => lhs < rhs,
        ICmpOp::Ule => lhs <= rhs,
        ICmpOp::Ugt => lhs > rhs,
        ICmpOp::Uge => lhs >= rhs,
        ICmpOp::Slt => signed(lhs) < signed(rhs),
        ICmpOp::Sle => signed(lhs) <= signed(rhs),
        ICmpOp::Sgt => signed(lhs) > signed(rhs),
        ICmpOp::Sge => signed(lhs) >= signed(rhs),
    }
}

#[test]
fn core_scalar_icmp_all_predicates_match_rust_and_bind_the_returned_result() {
    let bool_pairs = [(0, 0), (0, 1), (1, 0), (1, 1)];
    let usize_pairs = [
        (0, 0),
        (0, 1),
        (1, 0),
        (8, 7),
        (1 << 63, 0),
        (0, 1 << 63),
        (1 << 63, u64::MAX),
        (u64::MAX, 1 << 63),
        (u64::MAX, 0),
        (u64::MAX, u64::MAX),
    ];
    for (kind, pairs) in [
        (Kind::Bool, bool_pairs.as_slice()),
        (Kind::Usize, usize_pairs.as_slice()),
    ] {
        for op in OPS {
            let target = module(kind, op);
            for &(lhs, rhs) in pairs {
                let source = Comparison { kind, op, lhs, rhs };
                let expected = reference(source);
                assert_eq!(expected, bit_pattern_result(source), "{source:?}");
                checker()
                    .recheck_dag_v2(&source, &target, &proof(expected, world(173, 37, &[], 9)))
                    .unwrap_or_else(|error| panic!("{source:?}: {error}"));
                rejects(source, &target, &proof(!expected, world(173, 37, &[], 9)));
            }
        }
    }
}

#[test]
fn core_scalar_icmp_replay_binds_source_opcode_operands_and_return_site() {
    for source in [
        Comparison {
            kind: Kind::Bool,
            op: ICmpOp::Slt,
            lhs: 1,
            rhs: 0,
        },
        Comparison {
            kind: Kind::Usize,
            op: ICmpOp::Ne,
            lhs: 8,
            rhs: 7,
        },
    ] {
        let original = module(source.kind, source.op);
        let expected = reference(source);
        assert!(expected);
        let bytes = proof(expected, world(173, 37, &[], 9));
        checker()
            .recheck_dag_v2(&source, &original, &bytes)
            .unwrap();
        let changed_opcode = module(source.kind, ICmpOp::Eq);
        let mut changed_operand = original.clone();
        let Inst::ICmp { lhs, rhs, .. } = &mut changed_operand.functions[0].blocks[0].body[0].inst
        else {
            panic!("actual comparison node");
        };
        *lhs = *rhs;
        for target in [&changed_opcode, &changed_operand] {
            assert!(trust_ir_build::validate_module(target).is_empty());
            rejects(source, target, &bytes);
        }
        let changed_source = Comparison {
            lhs: source.rhs,
            ..source
        };
        rejects(changed_source, &original, &bytes);
        if matches!(source.kind, Kind::Bool) {
            let mut changed_return = original.clone();
            let rhs = changed_return.functions[0].blocks[0].params[1].0;
            let Inst::Return { values } = &mut changed_return.functions[0].blocks[0].body[1].inst
            else {
                panic!("actual return node");
            };
            values[0] = rhs;
            assert!(trust_ir_build::validate_module(&changed_return).is_empty());
            rejects(source, &changed_return, &bytes);
        }
    }
}

fn memory_mutation(base: u64, size: u64, owner: u64, alive: bool, cursor: u64) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[
                    app(
                        "IRByteAllocationV1.mk",
                        [
                            nat(base),
                            nat(size),
                            nat(owner),
                            c(if alive { "Bool.true" } else { "Bool.false" }),
                        ],
                    ),
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(80), nat(8), nat(7), c("Bool.false")],
                    ),
                ],
            ),
            lam(c("Nat"), app("IROption.some", [c("Nat"), nat(173)])),
            nat(cursor),
        ],
    )
}

#[test]
fn core_scalar_icmp_replay_preserves_every_terminal_world_field() {
    for source in [
        Comparison {
            kind: Kind::Bool,
            op: ICmpOp::Slt,
            lhs: 1,
            rhs: 0,
        },
        Comparison {
            kind: Kind::Usize,
            op: ICmpOp::Slt,
            lhs: 1 << 63,
            rhs: 0,
        },
    ] {
        let target = module(source.kind, source.op);
        let expected = reference(source);
        for wrong_world in [
            world(174, 37, &[], 9),
            world(173, 38, &[], 9),
            world(173, 37, &[nat(8)], 9),
            world(173, 37, &[], 8),
            world(173, 37, &[], 10),
        ]
        .into_iter()
        .chain(
            [
                memory_mutation(17, 16, 0, true, 128),
                memory_mutation(16, 17, 0, true, 128),
                memory_mutation(16, 16, 1, true, 128),
                memory_mutation(16, 16, 0, false, 128),
                memory_mutation(16, 16, 0, true, 129),
            ]
            .map(|memory| {
                app(
                    "IRByteWorldV1.mk",
                    [c("Nat"), memory, nat(37), list("Nat", &[]), nat(9)],
                )
            }),
        ) {
            rejects(source, &target, &proof(expected, wrong_world));
        }
    }
}

fn strict_replay(ty: Expr, actual: Expr, expected: Expr) {
    let env = checker().environment();
    let claim = eq(ty.clone(), actual, expected.clone());
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, expected],
    );
    let mut kernel = TypeChecker::new(env);
    kernel.set_allow_unsafe(false);
    kernel.set_allow_partial(false);
    kernel.set_heartbeat_limit(5_000_000);
    kernel.set_max_cache_entries(100_000);
    kernel
        .check_type(&claim, &Expr::sort(Level::zero()))
        .unwrap();
    kernel.check_type(&proof, &claim).unwrap();
    assert!(env.audit_certification(&claim, &proof).is_certified());
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&proof).unwrap();
    let replayed = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
    kernel.check_type(&replayed, &claim).unwrap();
    assert!(env.audit_certification(&claim, &replayed).is_certified());
}

#[test]
fn core_scalar_icmp_full_run_rechecks_in_strict_kernel_audit_and_dag() {
    for source in [
        Comparison {
            kind: Kind::Bool,
            op: ICmpOp::Slt,
            lhs: 1,
            rhs: 0,
        },
        Comparison {
            kind: Kind::Usize,
            op: ICmpOp::Slt,
            lhs: 1 << 63,
            rhs: 0,
        },
    ] {
        let target = module(source.kind, source.op);
        let claim = ScalarComparisonModel::reconstruct(&source, &target).unwrap();
        let bytes = proof(reference(source), world(173, 37, &[], 9));
        let replayed = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
        let env = checker().environment();
        let mut kernel = TypeChecker::new(env);
        kernel.set_allow_unsafe(false);
        kernel.set_allow_partial(false);
        kernel.set_heartbeat_limit(5_000_000);
        kernel.set_max_cache_entries(100_000);
        kernel
            .check_type(&claim, &Expr::sort(Level::zero()))
            .unwrap();
        kernel.check_type(&replayed, &claim).unwrap();
        assert!(env.audit_certification(&claim, &replayed).is_certified());
        checker().recheck_dag_v2(&source, &target, &bytes).unwrap();
    }
}

fn op_expr(op: ICmpOp) -> Expr {
    let name = match op {
        ICmpOp::Eq => "eq_",
        ICmpOp::Ne => "ne_",
        ICmpOp::Ult => "ult",
        ICmpOp::Ule => "ule",
        ICmpOp::Ugt => "ugt",
        ICmpOp::Uge => "uge",
        ICmpOp::Slt => "slt",
        ICmpOp::Sle => "sle",
        ICmpOp::Sgt => "sgt",
        ICmpOp::Sge => "sge",
    };
    c(&format!("IRICmpOp.{name}"))
}

fn fault(outcome: &str, reason: &str) -> Expr {
    app("IRStepResult.fault", [app(outcome, [c(reason)])])
}

#[test]
fn core_scalar_icmp_bool_poison_and_malformed_values_keep_refusal_priority() {
    let wrong = app("IRScalar.int_", [nat(1)]);
    for op in OPS {
        for (lhs, rhs, expected) in [
            (
                c("IRScalar.undef_"),
                boolean(false),
                fault("IROutcome.ub", "IRFault.uninit"),
            ),
            (
                boolean(true),
                c("IRScalar.undef_"),
                fault("IROutcome.ub", "IRFault.uninit"),
            ),
            (
                wrong.clone(),
                c("IRScalar.undef_"),
                fault("IROutcome.ub", "IRFault.uninit"),
            ),
            (
                c("IRScalar.undef_"),
                wrong.clone(),
                fault("IROutcome.ub", "IRFault.uninit"),
            ),
            (
                wrong.clone(),
                boolean(false),
                fault("IROutcome.type_error", "IRFault.not_bool"),
            ),
            (
                boolean(true),
                wrong.clone(),
                fault("IROutcome.type_error", "IRFault.not_bool"),
            ),
        ] {
            strict_replay(
                c("IRStepResult"),
                app(
                    "ir_byte_icmp_eval_v1",
                    [op_expr(op), c("IRTy.bool_"), lhs, rhs],
                ),
                expected,
            );
        }
    }
}

#[test]
fn core_scalar_icmp_legacy_profile_remains_distinct() {
    for op in [ICmpOp::Ult, ICmpOp::Slt] {
        strict_replay(
            c("IRStepResult"),
            app(
                "ir_icmp_eval",
                [op_expr(op), c("IRTy.bool_"), boolean(true), boolean(false)],
            ),
            fault("IROutcome.type_error", "IRFault.not_int"),
        );
    }
    for op in OPS {
        strict_replay(
            c("IRStepResult"),
            app(
                "ir_icmp_eval",
                [
                    op_expr(op),
                    app("IRTy.usize_", [nat(64)]),
                    Kind::Usize.scalar(8),
                    Kind::Usize.scalar(7),
                ],
            ),
            fault("IROutcome.type_error", "IRFault.not_int"),
        );
    }
}

#[test]
fn core_scalar_icmp_reflection_keeps_nominal_and_machine_profile_boundaries() {
    for kind in [Kind::Bool, Kind::Usize] {
        let mut target = module(kind, ICmpOp::Eq);
        let layout = target.target_info.as_mut().unwrap();
        layout.triple = "wasm32-unknown-unknown".into();
        layout.pointer_size = 4;
        layout.abi = None;
        layout.struct_passing = StructPassingPolicy::Unclassified;
        assert!(target.target_has_canonical_scalar_layout());
        assert!(trust_ir_build::validate_module(&target).is_empty());
        let error = reflect_core_module_v1(&target, &[(FuncId::new(0), 4096)]).unwrap_err();
        assert_eq!(
            error.to_string(),
            "unsupported byte-profile target layout or aggregate passing policy"
        );
    }
    // Valid identity functions keep the refused nominal types visible at the
    // reflection boundary without inventing ill-typed ICmp instructions.
    for ty in [Ty::Char, Ty::Isize, Ty::Vector(Box::new(Ty::Bool), 4)] {
        let mut builder = ModuleBuilder::new_with_target_info(
            "refused_scalar_profile",
            module(Kind::Bool, ICmpOp::Eq).target_info.unwrap(),
        );
        let signature = builder.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let id = builder.declare_function("identity", signature);
        let mut function = builder.define_function(id).unwrap();
        let entry = function.create_block();
        let value = function.add_block_param(entry, ty);
        function.switch_to_block(entry);
        function.ret(vec![value]);
        function.build();
        let target = builder.build().expect("valid refused-profile identity");
        assert!(trust_ir_build::validate_module(&target).is_empty());
        let error = reflect_core_module_v1(&target, &[(FuncId::new(0), 4096)]).unwrap_err();
        assert_eq!(error.to_string(), "unsupported byte-profile type");
    }
}
