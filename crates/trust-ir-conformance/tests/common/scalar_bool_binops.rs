// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Canonical Bool payloads through the typed contextual evaluator. The older
//! bare arithmetic helpers retain their separate integer-carrier contracts.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::inst::BinOp;
use trust_ir::interpret::{InterpretValue, InterpretValueKind};
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

const OPS: [BinOp; 6] = [
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
    BinOp::BAnd,
    BinOp::BOr,
    BinOp::BXor,
];

fn codeced(module: Module) -> [(&'static str, Module); 5] {
    let binary = trust_ir::binary::serialize_module(&module).unwrap();
    let text = trust_ir::format::text_checked(&module).unwrap();
    let json = serde_json::to_vec(&module).unwrap();
    let message_pack = rmp_serde::to_vec(&module).unwrap();
    [
        ("original", module),
        (
            "binary",
            trust_ir::binary::deserialize_module(&binary).unwrap(),
        ),
        ("text", trust_ir::parser::parse_module(&text).unwrap()),
        ("JSON", serde_json::from_slice(&json).unwrap()),
        ("MessagePack", rmp_serde::from_slice(&message_pack).unwrap()),
    ]
}

fn expected(op: BinOp, lhs: bool, rhs: bool) -> bool {
    match op {
        BinOp::And | BinOp::BAnd => lhs && rhs,
        BinOp::Or | BinOp::BOr => lhs || rhs,
        BinOp::Xor | BinOp::BXor => lhs ^ rhs,
        _ => unreachable!(),
    }
}

#[test]
fn scalar_bool_binops_valid_pairs_across_targets_and_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info(
            format!("scalar_bool_binops_{bits}"),
            semr_target(bits),
        );
        let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
        let mut runs = Vec::new();
        let mut values = Vec::new();
        for op in OPS {
            for lhs in [false, true] {
                for rhs in [false, true] {
                    let mut fb = mb.function(format!("{op:?}_{lhs}_{rhs}"), sig);
                    let entry = fb.create_block();
                    fb.switch_to_block(entry);
                    let lhs_id = fb.const_value(Ty::Bool, C::Bool(lhs));
                    let rhs_id = fb.const_value(Ty::Bool, C::Bool(rhs));
                    let value = fb.binop(op, Ty::Bool, lhs_id, rhs_id);
                    fb.ret(vec![value]);
                    runs.push(fb.build());
                    values.push(expected(op, lhs, rhs));
                }
            }
        }
        assert_eq!(runs.len(), 24);
        let module = mb.build().expect("valid scalar Bool operators");
        for (codec, module) in codeced(module) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((
                format!("{bits}/{codec}"),
                module,
                runs.clone(),
                values.clone(),
            ));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs, _)| Batch {
            label: label.clone(),
            module,
            runs: runs.iter().map(|id| (*id, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 240);
    let mut mismatches = Vec::new();
    for (report, &value) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, _, values)| values))
    {
        assert_eq!(
            report.rust,
            Verdict::Ok(vec![Val::Bool(value)]),
            "{report:?}"
        );
        if report.comparison != Comparison::Agree {
            mismatches.push(report);
        }
    }
    for report in mismatches.iter().take(8) {
        eprintln!("SCALAR_BOOL_BINOP_MISMATCH {report:?}");
    }
    assert!(
        mismatches.is_empty(),
        "{}/240 canonical scalar Bool comparisons disagreed",
        mismatches.len()
    );
}

#[test]
fn scalar_bool_binops_inspect_both_poison_operands_without_short_circuiting() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb =
            ModuleBuilder::new_with_target_info(format!("bool_poison_{bits}"), semr_target(bits));
        let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
        let mut runs = Vec::new();
        for op in OPS {
            for poison_left in [false, true] {
                for value in [false, true] {
                    let mut fb =
                        mb.function(format!("{op:?}_left_{poison_left}_value_{value}"), sig);
                    let entry = fb.create_block();
                    fb.switch_to_block(entry);
                    let poison = fb.undef(Ty::Bool);
                    let defined = fb.const_value(Ty::Bool, C::Bool(value));
                    let (lhs, rhs) = if poison_left {
                        (poison, defined)
                    } else {
                        (defined, poison)
                    };
                    fb.binop(op, Ty::Bool, lhs, rhs);
                    // A discarded result must still inspect both operands.
                    let result = fb.const_value(Ty::Bool, C::Bool(true));
                    fb.ret(vec![result]);
                    runs.push(fb.build());
                }
            }
        }
        let module = mb.build().expect("valid Bool poison consumers");
        for (codec, module) in codeced(module) {
            assert!(trust_ir_build::validate_module(&module).is_empty());
            modules.push((format!("{bits}/{codec}"), module, runs.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs.iter().map(|id| (*id, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 240);
    for report in reports {
        assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
        assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

#[test]
fn scalar_bool_binops_typed_context_refuses_integer_carriers() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb =
            ModuleBuilder::new_with_target_info(format!("bool_carriers_{bits}"), semr_target(bits));
        let sig = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]);
        let mut runs = Vec::new();
        for op in OPS {
            let mut fb = mb.function(format!("{op:?}"), sig);
            let entry = fb.create_block();
            let lhs = fb.add_block_param(entry, Ty::Bool);
            let rhs = fb.add_block_param(entry, Ty::Bool);
            fb.switch_to_block(entry);
            let result = fb.binop(op, Ty::Bool, lhs, rhs);
            fb.ret(vec![result]);
            let function = fb.build();
            let mut malformed_bool = InterpretValue::int_at(Ty::I8, 1, bits).unwrap();
            assert!(matches!(malformed_bool.kind, InterpretValueKind::Int(_)));
            malformed_bool.ty = Ty::Bool;
            for carrier in [
                InterpretValue::int_at(Ty::I8, 0, bits).unwrap(),
                InterpretValue::int_at(Ty::I64, 1, bits).unwrap(),
                malformed_bool,
            ] {
                for wrong_left in [false, true] {
                    let other = InterpretValue::bool(true);
                    runs.push((
                        function,
                        if wrong_left {
                            vec![carrier.clone(), other]
                        } else {
                            vec![other, carrier.clone()]
                        },
                    ));
                }
            }
        }
        let module = mb
            .build()
            .expect("valid typed Bool module for bad-input controls");
        for (codec, module) in codeced(module) {
            assert!(trust_ir_build::validate_module(&module).is_empty());
            modules.push((format!("{bits}/{codec}"), module, runs.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs.clone(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 360);
    for report in reports {
        // These deliberately invalid entry payloads are paired refusals,
        // not successful executions or new agreement/coverage credit.
        assert!(matches!(report.rust, Verdict::TypeError(_)), "{report:?}");
        assert!(matches!(report.lean, Verdict::TypeError(_)), "{report:?}");
    }
}

#[test]
fn scalar_bool_binops_invalid_operators_and_constant_carriers_stay_invalid() {
    use trust_ir_build::ValidationError;
    let mut checked = 0;
    for bits in [32, 64] {
        let mut mb =
            ModuleBuilder::new_with_target_info("bool_invalid_controls", semr_target(bits));
        let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
        let mut fb = mb.function("original", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let lhs = fb.const_value(Ty::Bool, C::Bool(true));
        let rhs = fb.const_value(Ty::Bool, C::Bool(false));
        let result = fb.binop(BinOp::BAnd, Ty::Bool, lhs, rhs);
        fb.ret(vec![result]);
        fb.build();
        let original = mb.build().expect("valid Bool control");
        for op in [
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::UDiv,
            BinOp::SDiv,
            BinOp::URem,
            BinOp::SRem,
            BinOp::Shl,
            BinOp::LShr,
            BinOp::AShr,
            BinOp::RotL,
            BinOp::RotR,
            BinOp::FAdd,
            BinOp::FSub,
            BinOp::FMul,
            BinOp::FDiv,
            BinOp::FRem,
            BinOp::FCopySign,
            BinOp::FMin,
            BinOp::FMax,
        ] {
            let mut module = original.clone();
            let trust_ir::Inst::BinOp { op: current, .. } =
                &mut module.functions[0].blocks[0].body[2].inst
            else {
                panic!("Bool operator")
            };
            *current = op;
            for (codec, module) in codeced(module) {
                let errors = trust_ir_build::validate_module(&module);
                assert!(
                    errors.iter().any(|error| matches!(
                        error,
                        ValidationError::BinOpRequiresInteger { .. }
                            | ValidationError::BinOpRequiresFloat { .. }
                    )),
                    "{bits}/{codec}/{op:?}: {errors:?}"
                );
                checked += 1;
            }
        }
        for carrier in [C::Int(1), C::Float(1.0), C::PhantomData] {
            let mut module = original.clone();
            let trust_ir::Inst::Const { value, .. } =
                &mut module.functions[0].blocks[0].body[0].inst
            else {
                panic!("Bool constant")
            };
            *value = carrier;
            for (codec, module) in codeced(module) {
                let errors = trust_ir_build::validate_module(&module);
                assert!(
                    errors
                        .iter()
                        .any(|error| matches!(error, ValidationError::ConstTypeMismatch { .. })),
                    "{bits}/{codec}: {errors:?}"
                );
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 230);
}
