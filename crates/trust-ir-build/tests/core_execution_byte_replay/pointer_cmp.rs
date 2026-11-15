// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual reflected pointer ICmp/Return execution in the public ByteV1 model.
//! These authored source invocations retain the whole terminal world. They
//! establish neither native installation nor Rust reference validity.

use super::*;
use clean_kernel::TypeChecker;
use trust_ir::ICmpOp;

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

#[derive(Clone, Copy)]
struct PointerComparison {
    op: ICmpOp,
    lhs: u64,
    rhs: u64,
}

fn pointer(address: u64) -> Expr {
    if address == 0 {
        c("IRScalar.nullptr_")
    } else {
        app("IRScalar.ptr_", [nat(address)])
    }
}

fn boolean(value: bool) -> Expr {
    app(
        "IRScalar.bool_",
        [c(if value { "Bool.true" } else { "Bool.false" })],
    )
}

fn result(source: PointerComparison) -> bool {
    let PointerComparison { op, lhs, rhs } = source;
    match op {
        ICmpOp::Eq => lhs == rhs,
        ICmpOp::Ne => lhs != rhs,
        ICmpOp::Ult => lhs < rhs,
        ICmpOp::Ule => lhs <= rhs,
        ICmpOp::Ugt => lhs > rhs,
        ICmpOp::Uge => lhs >= rhs,
        ICmpOp::Slt => (lhs as i64) < (rhs as i64),
        ICmpOp::Sle => (lhs as i64) <= (rhs as i64),
        ICmpOp::Sgt => (lhs as i64) > (rhs as i64),
        ICmpOp::Sge => (lhs as i64) >= (rhs as i64),
    }
}

fn op_name(op: ICmpOp) -> &'static str {
    match op {
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
    }
}

fn strict_equality(actual: Expr, expected: Expr) {
    let env = checker().environment();
    let ty = c("IRStepResult");
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

fn compare_at(op: ICmpOp, bits: u64, lhs: Expr, rhs: Expr) -> Expr {
    app(
        "ir_byte_pointer_icmp_at_v1",
        [c(&format!("IRICmpOp.{}", op_name(op))), nat(bits), lhs, rhs],
    )
}

fn fault(kind: &str, detail: &str) -> Expr {
    app("IRStepResult.fault", [app(kind, [c(detail)])])
}

fn incoming_memory() -> Expr {
    // Two adjacent actual external allocations plus historical retired owner7.
    // A comparison exposes addresses; it does not require a live dereference.
    let rows = list(
        "IRByteAllocationV1",
        &[
            app(
                "IRByteAllocationV1.mk",
                [nat(16), nat(8), nat(0), c("Bool.true")],
            ),
            app(
                "IRByteAllocationV1.mk",
                [nat(24), nat(8), nat(0), c("Bool.true")],
            ),
            app(
                "IRByteAllocationV1.mk",
                [nat(80), nat(8), nat(7), c("Bool.false")],
            ),
        ],
    );
    app(
        "IRByteMemoryV1.mk",
        [
            rows,
            lam(c("Nat"), app("IROption.some", [c("Nat"), nat(173)])),
            nat(128),
        ],
    )
}

fn terminal(value: bool, host: u64) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app("IROutcome.ret", [list("IRScalar", &[boolean(value)])]),
            app(
                "IRByteWorldV1.mk",
                [
                    c("Nat"),
                    incoming_memory(),
                    nat(host),
                    list("Nat", &[]),
                    nat(9),
                ],
            ),
        ],
    )
}

struct PointerComparisonModel;

impl SourceTranslationModel for PointerComparisonModel {
    type Source = PointerComparison;

    fn build_environment() -> Result<Environment, String> {
        LiteralReturnByteModel::build_environment()
    }

    fn reconstruct(source: &PointerComparison, target: &Module) -> Result<Expr, String> {
        let function = FuncId::new(0);
        let reflected = reflect_core_module_v1(target, &[(function, 4096)])
            .map_err(|error| error.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let initial = app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(0),
                list("IRScalar", &[pointer(source.lhs), pointer(source.rhs)]),
                incoming_memory(),
                nat(37),
            ],
        );
        Ok(eq(
            model.config_type(),
            model.run(&NatTerm::literal(2), initial),
            terminal(result(*source), 37),
        ))
    }
}

fn checker() -> &'static TranslationRechecker<PointerComparisonModel> {
    static CHECKER: OnceLock<TranslationRechecker<PointerComparisonModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

fn module(op: ICmpOp) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "ordinary_pointer_comparison",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("darwinpcs".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![Ty::Bool]);
    let id = builder.declare_function("compare", signature);
    let mut function = builder.define_function(id).unwrap();
    let entry = function.create_block();
    let lhs = function.add_block_param(entry, Ty::Ptr);
    let rhs = function.add_block_param(entry, Ty::Ptr);
    function.switch_to_block(entry);
    let compared = function.icmp(op, Ty::Ptr, lhs, rhs);
    function.ret(vec![compared]);
    function.build();
    builder.build().expect("valid pointer comparison module")
}

fn proof(value: bool, host: u64) -> Vec<u8> {
    let ty = app("IRByteConfigV1", [c("Nat")]);
    let term = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, terminal(value, host)],
    );
    trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap()
}

#[test]
fn core_pointer_icmp_ordering_runs_actual_byte_dispatch() {
    // Before the Byte pointer dispatch fix, Eq succeeds but admitted Ult
    // reaches legacy not_int instead of returning the address comparison.
    for op in [ICmpOp::Eq, ICmpOp::Ult] {
        let source = PointerComparison {
            op,
            lhs: 0,
            rhs: 16,
        };
        checker()
            .recheck_dag_v2(&source, &module(op), &proof(result(source), 37))
            .unwrap_or_else(|error| panic!("actual reflected {op:?} pointer comparison: {error}"));
    }
}

#[test]
fn core_pointer_icmp_all_predicates_keep_addresses_and_entire_terminal_world() {
    for op in OPS {
        let module = module(op);
        for (lhs, rhs) in [
            (0, 0),
            (0, 16),
            (16, 0),
            (16, 16),
            (16, 24),
            (24, 16),
            (80, 16),
            (1u64 << 63, 0),
            (u64::MAX, 16),
        ] {
            let source = PointerComparison { op, lhs, rhs };
            let bytes = proof(result(source), 37);
            checker()
                .recheck_dag_v2(&source, &module, &bytes)
                .unwrap_or_else(|error| panic!("{op:?}({lhs},{rhs}): {error}"));
            for changed in [proof(!result(source), 37), proof(result(source), 38)] {
                let error = checker()
                    .recheck_dag_v2(&source, &module, &changed)
                    .unwrap_err();
                assert_eq!(error.stage(), "kernel audit", "{error}");
                assert!(error.reason().contains("TypeMismatch"), "{error}");
            }
        }
    }
}

#[test]
fn core_pointer_icmp_does_not_claim_an_unimplemented_32_bit_machine_profile() {
    let mut module = module(ICmpOp::Ult);
    let target = module.target_info.as_mut().unwrap();
    target.triple = "wasm32-unknown-unknown".into();
    target.pointer_size = 4;
    target.abi = None;
    target.struct_passing = StructPassingPolicy::Unclassified;
    assert!(module.target_has_canonical_scalar_layout());
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let error = reflect_core_module_v1(&module, &[(FuncId::new(0), 4096)]).unwrap_err();
    assert_eq!(
        error.to_string(),
        "unsupported byte-profile target layout or aggregate passing policy"
    );
}

#[test]
fn core_pointer_icmp_replay_binds_actual_opcode_operands_and_source_inputs() {
    let source = PointerComparison {
        op: ICmpOp::Ult,
        lhs: 0,
        rhs: 16,
    };
    let original = module(source.op);
    let bytes = proof(result(source), 37);
    checker()
        .recheck_dag_v2(&source, &original, &bytes)
        .unwrap();
    let changed_opcode = module(ICmpOp::Ugt);
    let mut changed_operand = original.clone();
    let Inst::ICmp { lhs, rhs, .. } = &mut changed_operand.functions[0].blocks[0].body[0].inst
    else {
        panic!("actual comparison node");
    };
    *lhs = *rhs;
    for target in [&changed_opcode, &changed_operand] {
        let error = checker()
            .recheck_dag_v2(&source, target, &bytes)
            .unwrap_err();
        assert_eq!(error.stage(), "kernel audit", "{error}");
        assert!(error.reason().contains("TypeMismatch"), "{error}");
    }
    let changed_source = PointerComparison { rhs: 0, ..source };
    let error = checker()
        .recheck_dag_v2(&changed_source, &original, &bytes)
        .unwrap_err();
    assert_eq!(error.stage(), "kernel audit", "{error}");
    assert!(error.reason().contains("TypeMismatch"), "{error}");
}

#[test]
fn core_pointer_icmp_width_helpers_and_refusals_replay_in_shared_vocabulary() {
    for bits in [32, 64] {
        let high = 1u64 << (bits - 1);
        let outside = app("IRScalar.ptr_", [Expr::nat_lit_u128(1u128 << bits)]);
        for op in OPS {
            // These are width-indexed evaluator claims, not a 32-bit machine
            // admission. The complete reflected machine is tested separately.
            let source = PointerComparison {
                op,
                lhs: high,
                rhs: 0,
            };
            let expected = if bits == 64 {
                result(source)
            } else {
                match op {
                    ICmpOp::Eq | ICmpOp::Ult | ICmpOp::Ule | ICmpOp::Sgt | ICmpOp::Sge => false,
                    ICmpOp::Ne | ICmpOp::Ugt | ICmpOp::Uge | ICmpOp::Slt | ICmpOp::Sle => true,
                }
            };
            strict_equality(
                compare_at(op, bits, pointer(high), pointer(0)),
                app("IRStepResult.value", [boolean(expected)]),
            );
            for (lhs, rhs, expected) in [
                (
                    c("IRScalar.undef_"),
                    pointer(16),
                    fault("IROutcome.ub", "IRFault.uninit"),
                ),
                (
                    pointer(16),
                    c("IRScalar.undef_"),
                    fault("IROutcome.ub", "IRFault.uninit"),
                ),
                (
                    outside.clone(),
                    pointer(16),
                    fault("IROutcome.ub", "IRFault.bad_addr"),
                ),
                (
                    pointer(16),
                    outside.clone(),
                    fault("IROutcome.ub", "IRFault.bad_addr"),
                ),
                (
                    outside.clone(),
                    c("IRScalar.undef_"),
                    fault("IROutcome.ub", "IRFault.uninit"),
                ),
                (
                    app("IRScalar.int_", [nat(16)]),
                    pointer(16),
                    fault("IROutcome.type_error", "IRFault.not_ptr"),
                ),
            ] {
                strict_equality(compare_at(op, bits, lhs, rhs), expected);
            }
        }
    }
}
