// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Batch, Comparison, Oracle, Verdict, differential, oracle, semr_target};
use std::path::PathBuf;
use trust_ir::constant::Constant as C;
use trust_ir::inst::{BinOp, CastOp};
use trust_ir::value::FuncId;
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

fn cases(bits: u32) -> (Module, Vec<(FuncId, Option<BinOp>)>) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("float_minmax_{bits}"), semr_target(bits));
    let mut runs = Vec::new();
    for (ty, integer) in [(Ty::F16, Ty::U16), (Ty::F32, Ty::U32), (Ty::F64, Ty::U64)] {
        for op in [BinOp::FMin, BinOp::FMax] {
            for (phase, (left, right)) in [
                (1.5, 2.5),
                (2.5, 1.5),
                (1.5, 1.5),
                (-0.0, 0.0),
                (0.0, -0.0),
                (0.0, 0.0),
                (-0.0, -0.0),
            ]
            .into_iter()
            .enumerate()
            {
                let sig = mb.add_func_type(vec![], vec![ty.clone()]);
                let mut fb = mb.function(format!("scalar_{ty:?}_{op:?}_{phase}"), sig);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let left = fb.fconst(ty.clone(), left);
                let right = fb.fconst(ty.clone(), right);
                let result = fb.binop(op, ty.clone(), left, right);
                fb.ret(vec![result]);
                runs.push((fb.build(), Some(op)));
            }
            for phase in 0..4 {
                let sig = mb.add_func_type(vec![], vec![ty.clone()]);
                let mut fb = mb.function(format!("special_{ty:?}_{op:?}_{phase}"), sig);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let zero = fb.fconst(ty.clone(), 0.0);
                let one = fb.fconst(ty.clone(), 1.0);
                let negative_zero = fb.fconst(ty.clone(), -0.0);
                let nan = fb.binop(BinOp::FDiv, ty.clone(), zero, zero);
                let infinity = fb.binop(BinOp::FDiv, ty.clone(), one, zero);
                let (left, right) = match phase {
                    0 => (nan, negative_zero),
                    1 => (negative_zero, nan),
                    2 => (nan, nan),
                    _ => (infinity, negative_zero),
                };
                let result = fb.binop(op, ty.clone(), left, right);
                fb.ret(vec![result]);
                runs.push((fb.build(), Some(op)));
            }
            for reversed in [false, true] {
                let sig = mb.add_func_type(vec![], vec![integer.clone()]);
                let mut fb = mb.function(format!("bits_{ty:?}_{op:?}_{reversed}"), sig);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let left = fb.fconst(ty.clone(), if reversed { -0.0 } else { 0.0 });
                let right = fb.fconst(ty.clone(), if reversed { 0.0 } else { -0.0 });
                let result = fb.binop(op, ty.clone(), left, right);
                let observed = fb.cast(CastOp::Bitcast, ty.clone(), integer.clone(), result);
                fb.ret(vec![observed]);
                runs.push((fb.build(), Some(op)));
            }
            for count in [1, 3, 17] {
                for splat in [false, true] {
                    let vector = Ty::Vector(Box::new(ty.clone()), count);
                    let sig = mb.add_func_type(vec![], vec![vector.clone()]);
                    let mut fb = mb.function(format!("vector_{ty:?}_{op:?}_{count}_{splat}"), sig);
                    let entry = fb.create_block();
                    fb.switch_to_block(entry);
                    let literal = |right: bool| {
                        if splat {
                            // Splat constants belong to array types. A
                            // uniform vector literal is the admitted spelling.
                            C::Vector(vec![
                                C::Float(if right { -0.0 } else { 0.0 });
                                count as usize
                            ])
                        } else {
                            C::Vector(
                                (0..count)
                                    .map(|lane| {
                                        C::Float(match (lane % 3, right) {
                                            (0, false) | (1, true) => 0.0,
                                            (0, true) | (1, false) => -0.0,
                                            (_, false) => 1.5,
                                            (_, true) => 2.5,
                                        })
                                    })
                                    .collect(),
                            )
                        }
                    };
                    let left = fb.const_value(vector.clone(), literal(false));
                    let right = fb.const_value(vector.clone(), literal(true));
                    let result = fb.binop(op, vector, left, right);
                    fb.ret(vec![result]);
                    runs.push((fb.build(), Some(op)));
                }
            }
        }
    }
    let sig = mb.add_func_type(vec![], vec![Ty::F64]);
    let mut fb = mb.function("adjacent_fadd_control", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let left = fb.fconst(Ty::F64, 1.5);
    let right = fb.fconst(Ty::F64, 2.5);
    let result = fb.binop(BinOp::FAdd, Ty::F64, left, right);
    fb.ret(vec![result]);
    runs.push((fb.build(), None));
    assert_eq!(runs.len(), 115);
    (mb.build().expect("valid minmax cases"), runs)
}

#[test]
fn float_minmax_matches_actual_choice_witnesses_across_cold_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, runs) = cases(bits);
        let binary = trust_ir::binary::serialize_module(&module).unwrap();
        let text = trust_ir::format::text_checked(&module).unwrap();
        let json = serde_json::to_vec(&module).unwrap();
        let message_pack = rmp_serde::to_vec(&module).unwrap();
        for (codec, decoded) in [
            ("original", module),
            (
                "binary",
                trust_ir::binary::deserialize_module(&binary).unwrap(),
            ),
            ("text", trust_ir::parser::parse_module(&text).unwrap()),
            ("JSON", serde_json::from_slice(&json).unwrap()),
            ("MessagePack", rmp_serde::from_slice(&message_pack).unwrap()),
        ] {
            let errors = trust_ir_build::validate_module(&decoded);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((format!("minmax/{bits}/{codec}"), decoded, runs.clone()));
        }
    }
    let baseline = std::env::var_os("TRUST_IR_MINMAX_BASELINE_BIN").map(PathBuf::from);
    let exe = if let Some(exe) = &baseline {
        exe.clone()
    } else {
        let Oracle::Ready(exe) = oracle() else { return };
        exe.to_path_buf()
    };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs.iter().map(|(id, _)| (*id, vec![])).collect(),
        })
        .collect();
    let reports = differential(&exe, &batches);
    assert_eq!(reports.len(), 1150);
    let mut missing = 0;
    for (report, (_, expected)) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, runs)| runs))
    {
        assert!(matches!(report.rust, Verdict::Graph(_)), "{report:?}");
        if let (Some(_), Some(op)) = (&baseline, expected) {
            assert_eq!(
                report.lean,
                Verdict::Unsupported(format!("binop.{op:?}")),
                "{report:?}"
            );
            missing += 1;
        } else {
            assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
        }
    }
    if baseline.is_some() {
        assert_eq!(missing, 1140);
        eprintln!(
            "Min/max baseline:1140 valid runs refused missing constructors;10 adjacent controls agree"
        );
    } else {
        eprintln!(
            "Min/max:1150 exact agreements with actual zero-choice witnesses; all modules validate"
        );
    }
}
