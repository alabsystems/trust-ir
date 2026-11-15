// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use std::cmp::Ordering;
use trust_ir::constant::Constant;
use trust_ir::inst::ICmpOp;
use trust_ir::value::FuncId;
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

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

fn expected(op: ICmpOp, unsigned: Ordering, signed: Ordering) -> bool {
    match op {
        ICmpOp::Eq => unsigned.is_eq(),
        ICmpOp::Ne => !unsigned.is_eq(),
        ICmpOp::Ult => unsigned.is_lt(),
        ICmpOp::Ule => !unsigned.is_gt(),
        ICmpOp::Ugt => unsigned.is_gt(),
        ICmpOp::Uge => !unsigned.is_lt(),
        ICmpOp::Slt => signed.is_lt(),
        ICmpOp::Sle => !signed.is_gt(),
        ICmpOp::Sgt => signed.is_gt(),
        ICmpOp::Sge => !signed.is_lt(),
    }
}

fn bool_expected(op: ICmpOp, lhs: bool, rhs: bool) -> bool {
    // Bool is a one-bit integer: signed true is -1, signed false is zero.
    expected(op, lhs.cmp(&rhs), (-i8::from(lhs)).cmp(&-i8::from(rhs)))
}

fn integer_signed(raw: u128, width: u32) -> i128 {
    if raw & (1u128 << (width - 1)) == 0 {
        raw as i128
    } else {
        raw as i128 - (1i128 << width)
    }
}

fn add_comparison(
    mb: &mut ModuleBuilder,
    name: String,
    ty: Ty,
    op: ICmpOp,
    lhs: Constant,
    rhs: Constant,
) -> FuncId {
    let sig = mb.add_func_type(vec![], vec![ty.comparison_result_ty()]);
    let mut fb = mb.function(name, sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let lhs = fb.const_value(ty.clone(), lhs);
    let rhs = fb.const_value(ty.clone(), rhs);
    let result = fb.icmp(op, ty, lhs, rhs);
    fb.ret(vec![result]);
    fb.build()
}

fn comparison_module(bits: u32) -> (Module, Vec<(FuncId, Option<Val>)>) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("bool_vector_comparisons_{bits}"),
        semr_target(bits),
    );
    let mut runs = Vec::new();
    for lhs in [false, true] {
        for rhs in [false, true] {
            for op in OPS {
                let func = add_comparison(
                    &mut mb,
                    format!("scalar_bool_{lhs}_{rhs}_{op:?}"),
                    Ty::Bool,
                    op,
                    Constant::Bool(lhs),
                    Constant::Bool(rhs),
                );
                runs.push((func, Some(Val::Bool(bool_expected(op, lhs, rhs)))));
            }
        }
    }
    for count in [1, 2, 3, 4, 8, 16, 17] {
        // Four phases exercise all scalar Bool pairs even at count one.
        for phase in 0..4 {
            let pairs: Vec<_> = (0..count)
                .map(|lane| {
                    let pair = (lane + phase) % 4;
                    (pair & 2 != 0, pair & 1 != 0)
                })
                .collect();
            for op in OPS {
                let func = add_comparison(
                    &mut mb,
                    format!("bool_vector_{count}_{phase}_{op:?}"),
                    Ty::Vector(Box::new(Ty::Bool), count),
                    op,
                    Constant::Vector(pairs.iter().map(|(lhs, _)| Constant::Bool(*lhs)).collect()),
                    Constant::Vector(pairs.iter().map(|(_, rhs)| Constant::Bool(*rhs)).collect()),
                );
                let values = pairs
                    .iter()
                    .map(|(lhs, rhs)| Val::Bool(bool_expected(op, *lhs, *rhs)))
                    .collect();
                runs.push((func, Some(Val::Vector(values))));
            }
        }
    }
    for (elem_ty, width, signed) in [
        (Ty::I8, 8, true),
        (Ty::U8, 8, false),
        (Ty::I16, 16, true),
        (Ty::U16, 16, false),
        (Ty::I32, 32, true),
        (Ty::U32, 32, false),
        (Ty::I64, 64, true),
        (Ty::U64, 64, false),
    ] {
        let sign_bit = 1u128 << (width - 1);
        let mask = (1u128 << width) - 1;
        for count in [1, 3, 5, 17] {
            // These positive counts are independent of the backend's four
            // canonical SIMD shapes. Sign-bit lanes separate signed and
            // unsigned predicates, including for unsigned declared types.
            let pairs: Vec<_> = (0..count)
                .map(|lane| match lane % 5 {
                    0 => (sign_bit, 0),
                    1 => (0, 0),
                    2 => (mask, 1),
                    3 => (1, mask),
                    _ => (sign_bit - 1, sign_bit),
                })
                .collect();
            let literal = |raw| {
                Constant::Int(if signed {
                    integer_signed(raw, width)
                } else {
                    raw as i128
                })
            };
            for op in OPS {
                let func = add_comparison(
                    &mut mb,
                    format!("integer_vector_{elem_ty:?}_{count}_{op:?}"),
                    Ty::Vector(Box::new(elem_ty.clone()), count),
                    op,
                    Constant::Vector(pairs.iter().map(|(lhs, _)| literal(*lhs)).collect()),
                    Constant::Vector(pairs.iter().map(|(_, rhs)| literal(*rhs)).collect()),
                );
                let values = pairs
                    .iter()
                    .map(|(lhs, rhs)| {
                        Val::Bool(expected(
                            op,
                            lhs.cmp(rhs),
                            integer_signed(*lhs, width).cmp(&integer_signed(*rhs, width)),
                        ))
                    })
                    .collect();
                runs.push((func, Some(Val::Vector(values))));
            }
        }
    }
    assert_eq!(runs.len(), 640);
    for ty in [
        Ty::Bool,
        Ty::Vector(Box::new(Ty::Bool), 3),
        Ty::Vector(Box::new(Ty::I32), 3),
    ] {
        for poison_lhs in [false, true] {
            for op in OPS {
                let sig = mb.add_func_type(vec![], vec![ty.comparison_result_ty()]);
                let mut fb = mb.function(format!("poison_{ty:?}_{poison_lhs}_{op:?}"), sig);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let poison = fb.undef(ty.clone());
                let constant = match &ty {
                    Ty::Bool => Constant::Bool(false),
                    Ty::Vector(elem, count) => Constant::Vector(vec![
                        if **elem == Ty::Bool {
                            Constant::Bool(false)
                        } else {
                            Constant::Int(0)
                        };
                        *count as usize
                    ]),
                    _ => unreachable!(),
                };
                let value = fb.const_value(ty.clone(), constant);
                let (lhs, rhs) = if poison_lhs {
                    (poison, value)
                } else {
                    (value, poison)
                };
                let result = fb.icmp(op, ty.clone(), lhs, rhs);
                fb.ret(vec![result]);
                runs.push((fb.build(), None));
            }
        }
    }
    assert_eq!(runs.len(), 700);
    (mb.build().expect("Bool/vector comparison module"), runs)
}

#[test]
fn bool_and_arbitrary_positive_vector_comparisons_agree_across_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, runs) = comparison_module(bits);
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let binary = trust_ir::binary::serialize_module(&module).expect("encode binary");
        let text = trust_ir::format::text_checked(&module).expect("encode text");
        let json = serde_json::to_vec(&module).expect("encode JSON");
        let msgpack = rmp_serde::to_vec(&module).expect("encode MessagePack");
        for (format, decoded) in [
            ("original", module),
            (
                "binary",
                trust_ir::binary::deserialize_module(&binary).expect("decode binary"),
            ),
            (
                "text",
                trust_ir::parser::parse_module(&text).expect("decode text"),
            ),
            ("JSON", serde_json::from_slice(&json).expect("decode JSON")),
            (
                "MessagePack",
                rmp_serde::from_slice(&msgpack).expect("decode MessagePack"),
            ),
        ] {
            let errors = trust_ir_build::validate_module(&decoded);
            assert!(errors.is_empty(), "{bits}/{format}: {errors:?}");
            modules.push((
                format!("bool_vector_compare_{bits}_{format}"),
                decoded,
                runs.clone(),
            ));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs.iter().map(|(func, _)| (*func, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 7000);
    let mut counts = (0, 0);
    for (report, (_, expected)) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, runs)| runs))
    {
        if let Some(value) = expected {
            let verdict = Verdict::Ok(vec![value.clone()]);
            assert_eq!(report.rust, verdict, "{report:?}");
            assert_eq!(report.lean, verdict, "{report:?}");
            counts.0 += 1;
        } else {
            assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
            assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
            counts.1 += 1;
        }
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
    assert_eq!(counts, (6400, 600));
}
