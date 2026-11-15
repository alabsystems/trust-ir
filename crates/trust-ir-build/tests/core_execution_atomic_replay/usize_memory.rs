// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Faithful scalar memory support and the separate wrapping execution case.

use super::*;

enum Claim {
    LoadStore { returned: u64, stored: u64 },
    Wrap { returned: u64, stored: u64 },
    LegacyConstant,
    LegacyArithmetic,
    UnsupportedCast,
}

fn storage_fixture() -> Module {
    let mut module = fixture();
    module.name = "usize_scalar_memory".into();
    module.functions[0].name = "store_then_load_usize".into();
    let block = &mut module.functions[0].blocks[0];
    block.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::Usize,
            value: Constant::Int(7),
        })
        .with_result(ValueId(8)),
        InstrNode::new(Inst::Store {
            ty: Ty::Usize,
            ptr: ValueId(0),
            value: ValueId(8),
            volatile: false,
            align: Some(8),
        }),
        InstrNode::new(Inst::Load {
            ty: Ty::Usize,
            ptr: ValueId(0),
            volatile: false,
            align: Some(8),
        })
        .with_result(ValueId(9)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(9)],
        }),
    ];
    module.functions[0].blocks.truncate(1);
    // A separate authored load/store fixture, with no invented atomic sites.
    module.proof_obligations.clear();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn endpoints(claim: &Claim, target: &Module) -> Result<(Expr, Expr, Expr), String> {
    let reflected =
        reflect_core_module_v1(target, &[(FuncId(0), 4096)]).map_err(|error| error.to_string())?;
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    Ok(match claim {
        Claim::LoadStore { returned, stored } => (
            model.config_type(),
            model.run(&NatTerm::literal(4), initial(&model, 16)),
            terminal(&Invocation {
                old: *returned,
                new: *stored,
                ..Invocation::default()
            }),
        ),
        Claim::Wrap { returned, stored } => {
            let incoming = memory_from(app(
                "ir_byte_write_word_v1",
                [background(77), nat(16), nat(8), nat(u64::MAX)],
            ));
            let outgoing = memory_from(app(
                "ir_byte_write_word_v1",
                [
                    app("ir_byte_mem_bytes_v1", [incoming.clone()]),
                    nat(16),
                    nat(8),
                    nat(*stored),
                ],
            ));
            (
                c("IRByteMemoryResultV1"),
                app(
                    "ir_byte_fetch_add_relaxed_usize_seq_v1",
                    [
                        nat(64),
                        model.context().clone(),
                        pointer(16),
                        scalar(1),
                        incoming,
                    ],
                ),
                app("IRByteMemoryResultV1.value", [scalar(*returned), outgoing]),
            )
        }
        Claim::LegacyConstant | Claim::LegacyArithmetic | Claim::UnsupportedCast => {
            let ty = app("IRTy.usize_", [nat(64)]);
            let (evaluation, outcome) = match claim {
                Claim::LegacyConstant => (
                    app("ir_const_eval", [ty, app("IRConst.int_", [nat(7)])]),
                    app("IROutcome.type_error", [c("IRFault.not_int")]),
                ),
                Claim::LegacyArithmetic => (
                    app(
                        "ir_binop_eval",
                        [c("IRBinOp.add"), ty, scalar(1), scalar(2)],
                    ),
                    app("IROutcome.type_error", [c("IRFault.not_int")]),
                ),
                Claim::UnsupportedCast => (
                    app(
                        "ir_byte_cast_eval_v1",
                        [
                            model.context().clone(),
                            c("IRCastOp.bitcast"),
                            ty,
                            app("IRTy.uint_", [nat(64)]),
                            scalar(7),
                        ],
                    ),
                    app("IROutcome.unmodelled", [c("IRFault.width_bounded")]),
                ),
                _ => unreachable!(),
            };
            (
                c("IRStepResult"),
                evaluation,
                app("IRStepResult.fault", [outcome]),
            )
        }
    })
}

struct MemoryModel;
impl SourceTranslationModel for MemoryModel {
    type Source = Claim;
    fn build_environment() -> Result<Environment, String> {
        SequentialAtomicModel::build_environment()
    }
    fn reconstruct(source: &Claim, target: &Module) -> Result<Expr, String> {
        let (ty, left, right) = endpoints(source, target)?;
        Ok(eq(ty, left, right))
    }
}

fn rechecker() -> &'static TranslationRechecker<MemoryModel> {
    static CHECKER: OnceLock<TranslationRechecker<MemoryModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

fn replay(claim: &Claim, module: &Module) -> Vec<u8> {
    let (ty, _, right) = endpoints(claim, module).unwrap();
    // Closed kernel conversion, not a supplied successful-evaluation premise.
    let term = refl(ty, right);
    assert!(!term.has_fvar_quick());
    let proof = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    rechecker().recheck_dag_v2(claim, module, &proof).unwrap();
    proof
}

fn refuses(claim: &Claim, module: &Module, proof: &[u8]) {
    let error = rechecker()
        .recheck_dag_v2(claim, module, proof)
        .unwrap_err();
    assert_eq!(error.stage(), "kernel audit", "{error}");
    for resource in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
    ] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(resource),
            "semantic refusal required: {error}"
        );
    }
}

#[test]
fn usize64_store_load_wrapper_replays_exact_memory_and_result() {
    let module = storage_fixture();
    let before = module.clone();
    let proof = replay(
        &Claim::LoadStore {
            returned: 7,
            stored: 7,
        },
        &module,
    );
    refuses(
        &Claim::LoadStore {
            returned: 41,
            stored: 7,
        },
        &module,
        &proof,
    );
    refuses(
        &Claim::LoadStore {
            returned: 7,
            stored: 41,
        },
        &module,
        &proof,
    );
    assert_eq!(module, before);
}

#[test]
fn usize64_wrapping_atomic_returns_max_and_writes_zero_without_frame_change() {
    let module = fixture();
    let proof = replay(
        &Claim::Wrap {
            returned: u64::MAX,
            stored: 0,
        },
        &module,
    );
    refuses(
        &Claim::Wrap {
            returned: 0,
            stored: 0,
        },
        &module,
        &proof,
    );
    refuses(
        &Claim::Wrap {
            returned: u64::MAX,
            stored: u64::MAX,
        },
        &module,
        &proof,
    );
}

#[test]
fn usize64_admission_does_not_alias_legacy_arithmetic_or_equal_width_casts() {
    let mut module = fixture();
    module.types.push(Ty::U64);
    for claim in [
        Claim::LegacyConstant,
        Claim::LegacyArithmetic,
        Claim::UnsupportedCast,
    ] {
        replay(&claim, &module);
    }
}
