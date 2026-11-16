// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::inst::{BinOp, FCmpOp, UnOp};
use trust_ir::value::FuncId;
use trust_ir::{Inst, Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy, Debug)]
enum Operation {
    Bin(BinOp),
    Un(UnOp),
    FloatCmp(FCmpOp),
    Select,
    Extract(u32),
    Insert(u32),
    UndefVector,
    PoisonIndex(bool),
    PoisonInsert,
}

struct Case {
    elem: Ty,
    lhs: Vec<C>,
    rhs: Vec<C>,
    op: Operation,
    expected: Expected,
}

enum Expected {
    Value(Val),
    Ok,
    Ub,
    UnsupportedFloat,
}

fn ints(values: &[i128]) -> Vec<C> {
    values.iter().copied().map(C::Int).collect()
}
fn floats(values: &[f64]) -> Vec<C> {
    values.iter().copied().map(C::Float).collect()
}
fn bools(values: &[bool]) -> Vec<C> {
    values.iter().copied().map(C::Bool).collect()
}
fn vi(width: u32, values: &[u128]) -> Val {
    Val::Vector(
        values
            .iter()
            .map(|raw| Val::Int { width, raw: *raw })
            .collect(),
    )
}
fn vf(values: &[f64]) -> Val {
    Val::Vector(
        values
            .iter()
            .map(|value| {
                if value.is_nan() {
                    Val::Nan
                } else {
                    Val::Float(value.to_bits())
                }
            })
            .collect(),
    )
}
fn vb(values: &[bool]) -> Val {
    Val::Vector(values.iter().copied().map(Val::Bool).collect())
}

fn add_case(mb: &mut ModuleBuilder, index: usize, case: &Case) -> FuncId {
    let ty = Ty::Vector(Box::new(case.elem.clone()), case.lhs.len() as u32);
    let result_ty = match case.op {
        Operation::UndefVector => Ty::Bool,
        Operation::FloatCmp(_) => ty.comparison_result_ty(),
        Operation::Extract(_) | Operation::PoisonIndex(false) => case.elem.clone(),
        _ => ty.clone(),
    };
    let sig = mb.add_func_type(vec![], vec![result_ty]);
    let mut fb = mb.function(format!("case_{index}_{:?}_{:?}", case.elem, case.op), sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let lhs = fb.const_value(ty.clone(), C::Vector(case.lhs.clone()));
    let result = match case.op {
        Operation::Bin(op) => {
            let rhs = fb.const_value(ty.clone(), C::Vector(case.rhs.clone()));
            fb.binop(op, ty, lhs, rhs)
        }
        Operation::FloatCmp(op) => {
            let rhs = fb.const_value(ty.clone(), C::Vector(case.rhs.clone()));
            fb.fcmp(op, ty, lhs, rhs)
        }
        Operation::Un(op) => fb.unop(op, ty, lhs),
        Operation::Select => {
            let rhs = fb.const_value(ty.clone(), C::Vector(case.rhs.clone()));
            let mask_ty = Ty::Vector(Box::new(Ty::Bool), case.lhs.len() as u32);
            let mask = fb.const_value(
                mask_ty,
                C::Vector(
                    (0..case.lhs.len())
                        .map(|index| C::Bool(index % 2 == 0))
                        .collect(),
                ),
            );
            fb.select(ty, mask, lhs, rhs)
        }
        Operation::Extract(index) => {
            let index = fb.const_value(Ty::Usize, C::Int(i128::from(index)));
            fb.extract_element(case.elem.clone(), lhs, index)
        }
        Operation::Insert(index) => {
            let index = fb.const_value(Ty::Usize, C::Int(i128::from(index)));
            let value = fb.const_value(case.elem.clone(), case.rhs[0].clone());
            fb.insert_element(ty, lhs, index, value)
        }
        Operation::UndefVector => {
            fb.undef(ty);
            fb.const_value(Ty::Bool, C::Bool(true))
        }
        Operation::PoisonIndex(insert) => {
            let index = fb.undef(Ty::Usize);
            if insert {
                let value = fb.const_value(case.elem.clone(), case.lhs[0].clone());
                fb.insert_element(ty, lhs, index, value)
            } else {
                fb.extract_element(case.elem.clone(), lhs, index)
            }
        }
        Operation::PoisonInsert => {
            let index = fb.const_value(Ty::Usize, C::Int(0));
            let value = fb.undef(case.elem.clone());
            fb.insert_element(ty, lhs, index, value)
        }
    };
    fb.ret(vec![result]);
    fb.build()
}

fn baseline_cases() -> Vec<Case> {
    vec![
        Case {
            elem: Ty::U16,
            lhs: ints(&[1, 2, 3]),
            rhs: ints(&[4, 5, 6]),
            op: Operation::Bin(BinOp::Add),
            expected: Expected::Value(vi(16, &[5, 7, 9])),
        },
        Case {
            elem: Ty::U16,
            lhs: ints(&[1, 2, 3]),
            rhs: vec![],
            op: Operation::Un(UnOp::Not),
            expected: Expected::Value(vi(16, &[65534, 65533, 65532])),
        },
        Case {
            elem: Ty::F16,
            lhs: floats(&[1.0, 2.0, 3.0]),
            rhs: floats(&[4.0, 5.0, 6.0]),
            op: Operation::Bin(BinOp::FAdd),
            expected: Expected::Value(vf(&[5.0, 7.0, 9.0])),
        },
        Case {
            elem: Ty::F32,
            lhs: floats(&[f64::NAN, -0.0, 2.0]),
            rhs: floats(&[-1.0, 1.0, 3.0]),
            op: Operation::FloatCmp(FCmpOp::OLt),
            expected: Expected::Value(vb(&[false, true, true])),
        },
        Case {
            elem: Ty::F32,
            lhs: floats(&[1.0, 2.0, 3.0]),
            rhs: floats(&[4.0, 5.0, 6.0]),
            op: Operation::Select,
            expected: Expected::Value(vf(&[1.0, 5.0, 3.0])),
        },
        Case {
            elem: Ty::F64,
            lhs: floats(&[1.0, -0.0, f64::NAN]),
            rhs: vec![],
            op: Operation::Extract(1),
            expected: Expected::Value(Val::Float((-0.0f64).to_bits())),
        },
        Case {
            elem: Ty::Bool,
            lhs: bools(&[false, false, true]),
            rhs: bools(&[true]),
            op: Operation::Insert(1),
            expected: Expected::Value(vb(&[false, true, true])),
        },
        Case {
            elem: Ty::Bool,
            lhs: bools(&[true, false, true]),
            rhs: bools(&[true, true, false]),
            op: Operation::Bin(BinOp::BXor),
            expected: Expected::Value(vb(&[false, true, true])),
        },
        Case {
            elem: Ty::F32,
            lhs: floats(&[1.0, -0.0, 2.0]),
            rhs: vec![],
            op: Operation::Un(UnOp::FNeg),
            expected: Expected::Value(vf(&[-1.0, 0.0, -2.0])),
        },
        // Existing backend-shaped arithmetic remains a positive control.
        Case {
            elem: Ty::I32,
            lhs: ints(&[1, 2, 3, 4]),
            rhs: ints(&[4, 5, 6, 7]),
            op: Operation::Bin(BinOp::Add),
            expected: Expected::Value(vi(32, &[5, 7, 9, 11])),
        },
    ]
}

const INTEGER_TYPES: [Ty; 8] = [
    Ty::I8,
    Ty::U8,
    Ty::I16,
    Ty::U16,
    Ty::I32,
    Ty::U32,
    Ty::I64,
    Ty::U64,
];
const COUNTS: [usize; 4] = [1, 3, 5, 17];

fn arithmetic_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for elem in INTEGER_TYPES {
        for count in COUNTS {
            let lhs: Vec<_> = (0..count)
                .map(|index| {
                    C::Int(if elem.is_signed() {
                        [-7, 3, -1, 17][index % 4]
                    } else {
                        [7, 3, 255, 17][index % 4]
                    })
                })
                .collect();
            for op in [
                BinOp::Add,
                BinOp::Sub,
                BinOp::Mul,
                BinOp::UDiv,
                BinOp::SDiv,
                BinOp::URem,
                BinOp::SRem,
                BinOp::And,
                BinOp::Or,
                BinOp::Xor,
                BinOp::Shl,
                BinOp::LShr,
                BinOp::AShr,
                BinOp::RotL,
                BinOp::RotR,
            ] {
                let shifts = matches!(
                    op,
                    BinOp::Shl | BinOp::LShr | BinOp::AShr | BinOp::RotL | BinOp::RotR
                );
                let rhs = (0..count)
                    .map(|index| {
                        C::Int(if shifts {
                            (index % 4) as i128
                        } else {
                            (index % 3 + 1) as i128
                        })
                    })
                    .collect();
                cases.push(Case {
                    elem: elem.clone(),
                    lhs: lhs.clone(),
                    rhs,
                    op: Operation::Bin(op),
                    expected: Expected::Ok,
                });
            }
            for op in [
                UnOp::Neg,
                UnOp::Not,
                UnOp::CtPop,
                UnOp::CtLz,
                UnOp::CtTz,
                UnOp::BSwap,
                UnOp::BitReverse,
            ] {
                cases.push(Case {
                    elem: elem.clone(),
                    lhs: lhs.clone(),
                    rhs: vec![],
                    op: Operation::Un(op),
                    expected: Expected::Ok,
                });
            }
        }
    }
    for count in COUNTS {
        for phase in 0..4 {
            let lhs = (0..count)
                .map(|index| C::Bool((index + phase) & 2 != 0))
                .collect::<Vec<_>>();
            let rhs = (0..count)
                .map(|index| C::Bool((index + phase) & 1 != 0))
                .collect::<Vec<_>>();
            for op in [
                BinOp::And,
                BinOp::Or,
                BinOp::Xor,
                BinOp::BAnd,
                BinOp::BOr,
                BinOp::BXor,
            ] {
                cases.push(Case {
                    elem: Ty::Bool,
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                    op: Operation::Bin(op),
                    expected: Expected::Ok,
                });
            }
            cases.push(Case {
                elem: Ty::Bool,
                lhs,
                rhs: vec![],
                op: Operation::Un(UnOp::Not),
                expected: Expected::Ok,
            });
        }
    }
    // Lift exactly the existing scalar IEEE operators. FMin/FMax have no
    // Lean scalar/schema/decode path yet and remain a required separate gap.
    for elem in [Ty::F16, Ty::F32, Ty::F64] {
        for count in COUNTS {
            let lhs = (0..count)
                .map(|index| C::Float([0.1, -0.0, 1.5, -2.25, f64::INFINITY, f64::NAN][index % 6]))
                .collect::<Vec<_>>();
            for op in [
                BinOp::FAdd,
                BinOp::FSub,
                BinOp::FMul,
                BinOp::FDiv,
                BinOp::FRem,
                BinOp::FCopySign,
            ] {
                let rhs = (0..count)
                    .map(|index| C::Float([0.2, 3.0, -0.0, f64::INFINITY][index % 4]))
                    .collect();
                cases.push(Case {
                    elem: elem.clone(),
                    lhs: lhs.clone(),
                    rhs,
                    op: Operation::Bin(op),
                    expected: Expected::Ok,
                });
            }
            for op in [
                UnOp::FNeg,
                UnOp::FAbs,
                UnOp::FSqrt,
                UnOp::FFloor,
                UnOp::FCeil,
                UnOp::FTrunc,
            ] {
                cases.push(Case {
                    elem: elem.clone(),
                    lhs: lhs.clone(),
                    rhs: vec![],
                    op: Operation::Un(op),
                    expected: Expected::Ok,
                });
            }
            for op in [
                FCmpOp::OEq,
                FCmpOp::ONe,
                FCmpOp::OLt,
                FCmpOp::OLe,
                FCmpOp::OGt,
                FCmpOp::OGe,
                FCmpOp::UEq,
                FCmpOp::UNe,
                FCmpOp::ULt,
                FCmpOp::ULe,
                FCmpOp::UGt,
                FCmpOp::UGe,
            ] {
                let rhs = (0..count)
                    .map(|index| C::Float([0.1, 0.0, f64::NAN, 1.0][index % 4]))
                    .collect();
                cases.push(Case {
                    elem: elem.clone(),
                    lhs: lhs.clone(),
                    rhs,
                    op: Operation::FloatCmp(op),
                    expected: Expected::Ok,
                });
            }
        }
    }
    assert_eq!(cases.len(), 1104);
    cases
}

fn lane_transport_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for elem in INTEGER_TYPES
        .into_iter()
        .chain([Ty::Bool, Ty::F16, Ty::F32, Ty::F64])
    {
        for count in COUNTS {
            let lane = |index: usize| {
                if elem == Ty::Bool {
                    C::Bool(index % 2 == 0)
                } else if elem.is_float() {
                    C::Float([0.1, -0.0, f64::NAN, f64::INFINITY][index % 4])
                } else {
                    C::Int((index % 127) as i128)
                }
            };
            let lhs = (0..count).map(lane).collect::<Vec<_>>();
            let rhs = (0..count).map(|index| lane(index + 1)).collect::<Vec<_>>();
            for op in [
                Operation::Select,
                Operation::Extract((count - 1) as u32),
                Operation::Insert((count / 2) as u32),
            ] {
                cases.push(Case {
                    elem: elem.clone(),
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                    op,
                    expected: Expected::Ok,
                });
            }
        }
    }
    assert_eq!(cases.len(), 144);
    cases
}

fn refusal_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for elem in INTEGER_TYPES {
        let width = elem.bit_width().unwrap();
        for count in [1, 3] {
            let lhs = vec![C::Int(7); count];
            for op in [BinOp::UDiv, BinOp::SDiv, BinOp::URem, BinOp::SRem] {
                cases.push(Case {
                    elem: elem.clone(),
                    lhs: lhs.clone(),
                    rhs: vec![C::Int(0); count],
                    op: Operation::Bin(op),
                    expected: Expected::Ub,
                });
            }
            for op in [BinOp::Shl, BinOp::LShr, BinOp::AShr] {
                cases.push(Case {
                    elem: elem.clone(),
                    lhs: lhs.clone(),
                    rhs: vec![C::Int(i128::from(width)); count],
                    op: Operation::Bin(op),
                    expected: Expected::Ub,
                });
            }
            let min = if elem.is_signed() {
                -(1i128 << (width - 1))
            } else {
                1i128 << (width - 1)
            };
            let minus_one = if elem.is_signed() {
                -1
            } else {
                (1i128 << width) - 1
            };
            for op in [BinOp::SDiv, BinOp::SRem] {
                cases.push(Case {
                    elem: elem.clone(),
                    lhs: vec![C::Int(min); count],
                    rhs: vec![C::Int(minus_one); count],
                    op: Operation::Bin(op),
                    expected: Expected::Ub,
                });
            }
        }
    }
    for elem in INTEGER_TYPES
        .into_iter()
        .chain([Ty::Bool, Ty::F16, Ty::F32, Ty::F64])
    {
        let lane = if elem == Ty::Bool {
            C::Bool(true)
        } else if elem.is_float() {
            C::Float(1.5)
        } else {
            C::Int(7)
        };
        for op in [
            Operation::UndefVector,
            Operation::PoisonIndex(false),
            Operation::PoisonIndex(true),
            Operation::PoisonInsert,
        ] {
            cases.push(Case {
                elem: elem.clone(),
                lhs: vec![lane.clone(); 3],
                rhs: vec![],
                op,
                expected: Expected::Ub,
            });
        }
    }
    for elem in [Ty::F16, Ty::F32, Ty::F64] {
        cases.push(Case {
            elem,
            lhs: floats(&[1.0, 2.0, 3.0]),
            rhs: floats(&[0.0, f64::NAN, 1.0]),
            op: Operation::Bin(BinOp::FCopySign),
            expected: Expected::UnsupportedFloat,
        });
    }
    assert_eq!(cases.len(), 195);
    cases
}

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

fn check_cases(cases: &[Case]) {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info(
            format!("vector_operations_{bits}"),
            semr_target(bits),
        );
        let runs: Vec<_> = cases
            .iter()
            .enumerate()
            .map(|(index, case)| add_case(&mut mb, index, case))
            .collect();
        let module = mb.build().expect("valid vector operations");
        for (codec, decoded) in codeced(module) {
            let errors = trust_ir_build::validate_module(&decoded);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((format!("{bits}/{codec}"), decoded, runs.clone()));
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
    assert_eq!(reports.len(), cases.len() * 10);
    let mut mismatches = Vec::new();
    for (report, case) in reports.iter().zip(cases.iter().cycle()) {
        let agree = match &case.expected {
            Expected::Value(value) => {
                assert_eq!(report.rust, Verdict::Ok(vec![value.clone()]), "{report:?}");
                report.comparison == Comparison::Agree
            }
            Expected::Ok => {
                assert!(matches!(report.rust, Verdict::Graph(_)), "{report:?}");
                report.comparison == Comparison::Agree
            }
            Expected::Ub => {
                assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
                matches!(report.lean, Verdict::Ub(_)) && report.comparison == Comparison::Agree
            }
            Expected::UnsupportedFloat => {
                assert!(matches!(report.rust, Verdict::Graph(_)), "{report:?}");
                report.lean == Verdict::Unsupported("float".into())
            }
        };
        if !agree {
            mismatches.push(report);
        }
    }
    for report in mismatches.iter().take(12) {
        eprintln!("VECTOR_OPERATION_MISMATCH {report:?}");
    }
    assert!(
        mismatches.is_empty(),
        "{}/{} vector operations disagreed",
        mismatches.len(),
        reports.len()
    );
    eprintln!("VECTOR_OPERATION_PASS {} runs", reports.len());
}

#[test]
fn vector_operations_valid_shapes_targets_and_codecs() {
    check_cases(&baseline_cases());
}

#[test]
fn vector_operations_modeled_arithmetic_and_float_comparisons() {
    check_cases(&arithmetic_cases());
}

#[test]
fn vector_operations_select_extract_insert_transport_ieee_values() {
    check_cases(&lane_transport_cases());
}

#[test]
fn vector_operations_integer_poison_and_nan_refusals() {
    check_cases(&refusal_cases());
}

#[test]
fn vector_operations_dynamic_indices_keep_runtime_bounds_checks() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info(
            format!("vector_indices_{bits}"),
            semr_target(bits),
        );
        let mut runs = Vec::new();
        let mut expected = Vec::new();
        for elem in INTEGER_TYPES
            .into_iter()
            .chain([Ty::Bool, Ty::F16, Ty::F32, Ty::F64])
        {
            for count in [1, 3, 17] {
                let ty = Ty::Vector(Box::new(elem.clone()), count);
                let lane = if elem == Ty::Bool {
                    C::Bool(true)
                } else if elem.is_float() {
                    C::Float(-0.0)
                } else {
                    C::Int(7)
                };
                for insert in [false, true] {
                    let sig = mb.add_func_type(
                        vec![Ty::I64],
                        vec![if insert { ty.clone() } else { elem.clone() }],
                    );
                    let mut fb = mb.function(format!("{elem:?}_{count}_insert_{insert}"), sig);
                    let entry = fb.create_block();
                    let index = fb.add_block_param(entry, Ty::I64);
                    fb.switch_to_block(entry);
                    let vector =
                        fb.const_value(ty.clone(), C::Vector(vec![lane.clone(); count as usize]));
                    let result = if insert {
                        let value = fb.const_value(elem.clone(), lane.clone());
                        fb.insert_element(ty.clone(), vector, index, value)
                    } else {
                        fb.extract_element(elem.clone(), vector, index)
                    };
                    fb.ret(vec![result]);
                    let function = fb.build();
                    for index in [
                        -1,
                        0,
                        i128::from(count) - 1,
                        i128::from(count),
                        i128::from(count) + 1,
                    ] {
                        runs.push((
                            function,
                            vec![
                                trust_ir::interpret::InterpretValue::int_at(Ty::I64, index, bits)
                                    .unwrap(),
                            ],
                        ));
                        expected.push(index >= 0 && index < i128::from(count));
                    }
                }
            }
        }
        assert_eq!(runs.len(), 360);
        let module = mb.build().expect("valid dynamic vector indices");
        for (codec, module) in codeced(module) {
            assert!(trust_ir_build::validate_module(&module).is_empty());
            modules.push((
                format!("{bits}/{codec}"),
                module,
                runs.clone(),
                expected.clone(),
            ));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs, _)| Batch {
            label: label.clone(),
            module,
            runs: runs.clone(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 3600);
    for (report, &in_bounds) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, _, expected)| expected))
    {
        if in_bounds {
            assert!(matches!(report.rust, Verdict::Graph(_)), "{report:?}");
        } else {
            assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
        }
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

#[test]
fn vector_operations_narrow_signed_indices_do_not_alias_unsigned_indices() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info(
            format!("narrow_vector_indices_{bits}"),
            semr_target(bits),
        );
        let vector_ty = Ty::Vector(Box::new(Ty::I32), 257);
        let mut runs = Vec::new();
        let mut expectations = Vec::new();
        for (index_ty, input) in [(Ty::I8, -1), (Ty::U8, 255)] {
            for insert in [false, true] {
                let sig = mb.add_func_type(
                    vec![index_ty.clone()],
                    vec![if insert { vector_ty.clone() } else { Ty::I32 }],
                );
                let mut fb = mb.function(format!("{index_ty:?}_insert_{insert}"), sig);
                let entry = fb.create_block();
                let index = fb.add_block_param(entry, index_ty.clone());
                fb.switch_to_block(entry);
                let vector =
                    fb.const_value(vector_ty.clone(), C::Vector((0..257).map(C::Int).collect()));
                let result = if insert {
                    let replacement = fb.const_value(Ty::I32, C::Int(900));
                    fb.insert_element(vector_ty.clone(), vector, index, replacement)
                } else {
                    fb.extract_element(Ty::I32, vector, index)
                };
                fb.ret(vec![result]);
                let function = fb.build();
                runs.push((
                    function,
                    vec![
                        trust_ir::interpret::InterpretValue::int_at(index_ty.clone(), input, bits)
                            .unwrap(),
                    ],
                ));
                let expected = if input < 0 {
                    Verdict::Ub("negative index".into())
                } else if insert {
                    Verdict::Ok(vec![vi(
                        32,
                        &(0..257)
                            .map(|lane| if lane == 255 { 900 } else { lane })
                            .collect::<Vec<_>>(),
                    )])
                } else {
                    Verdict::Ok(vec![Val::Int {
                        width: 32,
                        raw: 255,
                    }])
                };
                expectations.push(expected);
            }
        }
        let module = mb.build().expect("valid narrow dynamic vector indices");
        for (codec, module) in codeced(module) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((
                format!("{bits}/{codec}"),
                module,
                runs.clone(),
                expectations.clone(),
            ));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(label, module, runs, _)| Batch {
            label: label.clone(),
            module,
            runs: runs.clone(),
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 40);
    let mut disagreements = Vec::new();
    let mut unsigned_controls = 0;
    for (report, expected) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, _, expected)| expected))
    {
        if matches!(expected, Verdict::Ub(_)) {
            assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
        } else {
            assert_eq!(&report.rust, expected, "{report:?}");
            assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
            unsigned_controls += 1;
        }
        if report.comparison != Comparison::Agree {
            disagreements.push(report);
        }
    }
    assert_eq!(unsigned_controls, 20);
    for report in disagreements.iter().take(4) {
        eprintln!("NARROW_VECTOR_INDEX_MISMATCH {report:?}");
    }
    eprintln!("NARROW_VECTOR_INDEX unsigned controls: {unsigned_controls}/20");
    assert!(
        disagreements.is_empty(),
        "{}/40 narrow signed/unsigned vector index runs disagreed",
        disagreements.len()
    );
}

#[test]
fn vector_operations_indices_use_all_function_local_ssa_producers() {
    use std::collections::HashMap;
    use trust_ir::Ordering;
    use trust_ir::inst::{CastOp, OverflowOp};
    use trust_ir::value::ValueId;

    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info(
            format!("vector_index_producers_{bits}"),
            semr_target(bits),
        );
        let vector_ty = Ty::Vector(Box::new(Ty::I32), 257);
        let mut runs = Vec::new();
        let mut expected = Vec::new();
        for (index_ty, input) in [(Ty::I8, -1), (Ty::U8, 255)] {
            let helper_sig = mb.add_func_type(vec![index_ty.clone()], vec![index_ty.clone()]);
            let mut helper = mb.function(format!("{index_ty:?}_identity"), helper_sig);
            let helper_entry = helper.create_block();
            let value = helper.add_block_param(helper_entry, index_ty.clone());
            helper.switch_to_block(helper_entry);
            helper.ret(vec![value]);
            let helper = helper.build();
            let array_elem = mb.add_type(index_ty.clone());
            for producer in 0..13 {
                for insert in [false, true] {
                    let input_ty = if producer == 3 {
                        Ty::I64
                    } else {
                        index_ty.clone()
                    };
                    let sig = mb.add_func_type(
                        vec![input_ty.clone()],
                        vec![if insert { vector_ty.clone() } else { Ty::I32 }],
                    );
                    let mut fb = mb.function(
                        format!("{index_ty:?}_producer_{producer}_insert_{insert}"),
                        sig,
                    );
                    let entry = fb.create_block();
                    let input_id = fb.add_block_param(entry, input_ty.clone());
                    fb.switch_to_block(entry);
                    let index = match producer {
                        0 => input_id,
                        1 => {
                            let first = fb.copy(index_ty.clone(), input_id);
                            fb.copy(index_ty.clone(), first)
                        }
                        2 => {
                            let zero = fb.const_value(index_ty.clone(), C::Int(0));
                            fb.binop(BinOp::Add, index_ty.clone(), input_id, zero)
                        }
                        3 => fb.cast(CastOp::Trunc, Ty::I64, index_ty.clone(), input_id),
                        4 | 5 | 11 => {
                            let slot = fb.alloca(index_ty.clone());
                            fb.store(index_ty.clone(), slot, input_id);
                            match producer {
                                4 => fb.load(index_ty.clone(), slot),
                                5 => fb.atomic_load(index_ty.clone(), slot, Ordering::SeqCst),
                                _ => {
                                    fb.cmpxchg(
                                        index_ty.clone(),
                                        slot,
                                        input_id,
                                        input_id,
                                        Ordering::SeqCst,
                                        Ordering::SeqCst,
                                    )
                                    .0
                                }
                            }
                        }
                        6 => fb.call(helper, vec![input_id]),
                        7 => {
                            let callee = fb.const_value(Ty::Func(helper_sig), C::FnDef(helper));
                            fb.call_indirect(callee, helper_sig, vec![input_id])
                        }
                        8 => {
                            let next = fb.create_block();
                            let forwarded = fb.add_block_param(next, index_ty.clone());
                            fb.br(next, vec![input_id]);
                            fb.switch_to_block(next);
                            forwarded
                        }
                        9 => {
                            let cond = fb.const_value(Ty::Bool, C::Bool(true));
                            fb.select(index_ty.clone(), cond, input_id, input_id)
                        }
                        10 => {
                            let zero = fb.const_value(index_ty.clone(), C::Int(0));
                            fb.overflow(OverflowOp::AddOverflow, index_ty.clone(), input_id, zero)
                                .0
                        }
                        12 => {
                            let array = fb.const_value(
                                Ty::Array(array_elem, 1),
                                C::Array(vec![C::Int(input)]),
                            );
                            let zero = fb.const_value(Ty::Usize, C::Int(0));
                            fb.extract_element(index_ty.clone(), array, zero)
                        }
                        _ => unreachable!(),
                    };
                    let vector = fb
                        .const_value(vector_ty.clone(), C::Vector((0..257).map(C::Int).collect()));
                    let result = if insert {
                        let replacement = fb.const_value(Ty::I32, C::Int(900));
                        fb.insert_element(vector_ty.clone(), vector, index, replacement)
                    } else {
                        fb.extract_element(Ty::I32, vector, index)
                    };
                    fb.ret(vec![result]);
                    runs.push((
                        fb.build(),
                        vec![
                            trust_ir::interpret::InterpretValue::int_at(input_ty, input, bits)
                                .unwrap(),
                        ],
                    ));
                    expected.push(input >= 0);
                }
            }
        }
        let mut module = mb.build().expect("valid SSA index producer corpus");
        // Source identities are intentionally sparse, and blocks/functions are
        // serialized in the reverse of their dominance/declaration order.
        for function in &mut module.functions {
            let mut remap = HashMap::new();
            for block in &function.blocks {
                for (id, _) in &block.params {
                    remap.insert(*id, ValueId::new(id.index() * 37 + 101));
                }
                for node in &block.body {
                    for id in &node.results {
                        remap.insert(*id, ValueId::new(id.index() * 37 + 101));
                    }
                }
            }
            for block in &mut function.blocks {
                for (id, _) in &mut block.params {
                    *id = remap[id];
                }
                for node in &mut block.body {
                    trust_ir::mem2reg::rewrite_inst(&mut node.inst, &remap);
                    for id in &mut node.results {
                        *id = remap[id];
                    }
                }
            }
            function.blocks.reverse();
        }
        module.functions.reverse();
        assert_eq!(runs.len(), 52);
        let text_loss = trust_ir::format::text_checked(&module).unwrap_err();
        assert!(
            text_loss
                .losses
                .iter()
                .all(|loss| matches!(loss, trust_ir::format::TextLoss::EntryBlock { .. }))
        );
        assert!(
            text_loss
                .losses
                .iter()
                .any(|loss| matches!(loss, trust_ir::format::TextLoss::EntryBlock { .. }))
        );
        // Sparse function IDs are carried; the reordered entry block remains a loss.
        // Check its canonical source independently; the other four transports
        // exercise the original non-dominance serialization order unchanged.
        let mut canonical = module.clone();
        canonical
            .functions
            .sort_by_key(|function| function.id.index());
        for function in &mut canonical.functions {
            function
                .blocks
                .sort_by_key(|block| (block.id != function.entry, block.id.index()));
        }
        let mut transports = codeced(canonical)
            .into_iter()
            .map(|(codec, module)| (format!("canonical/{codec}"), module))
            .collect::<Vec<_>>();
        let binary = trust_ir::binary::serialize_module(&module).unwrap();
        let json = serde_json::to_vec(&module).unwrap();
        let message_pack = rmp_serde::to_vec(&module).unwrap();
        transports.extend([
            ("reordered/original".into(), module),
            (
                "reordered/binary".into(),
                trust_ir::binary::deserialize_module(&binary).unwrap(),
            ),
            (
                "reordered/JSON".into(),
                serde_json::from_slice(&json).unwrap(),
            ),
            (
                "reordered/MessagePack".into(),
                rmp_serde::from_slice(&message_pack).unwrap(),
            ),
        ]);
        for (codec, module) in transports {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((
                format!("{bits}/{codec}"),
                module,
                runs.clone(),
                expected.clone(),
            ));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(label, module, runs, _)| Batch {
            label: label.clone(),
            module,
            runs: runs.clone(),
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 936);
    for (report, &nonnegative) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, _, expected)| expected))
    {
        if nonnegative {
            assert!(matches!(report.rust, Verdict::Graph(_)), "{report:?}");
        } else {
            assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
        }
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

#[test]
fn vector_operations_zero_unadmitted_and_malformed_payloads_stay_invalid() {
    use trust_ir_build::ValidationError;
    let cases = baseline_cases();
    let mut checked = 0;
    for bits in [32, 64] {
        let mut mb =
            ModuleBuilder::new_with_target_info("vector_refusal_controls", semr_target(bits));
        add_case(&mut mb, 0, &cases[0]);
        let original = mb.build().expect("valid original vector control");
        assert!(trust_ir_build::validate_module(&original).is_empty());
        for mutation in 0..9 {
            let mut module = original.clone();
            let Inst::Const { ty, value } = &mut module.functions[0].blocks[0].body[0].inst else {
                panic!("vector constant")
            };
            match mutation {
                0 => {
                    *ty = Ty::Vector(Box::new(Ty::U16), 0);
                    *value = C::Vector(vec![]);
                }
                1 => *ty = Ty::Vector(Box::new(Ty::I128), 3),
                2 => *ty = Ty::Vector(Box::new(Ty::Usize), 3),
                3 => *ty = Ty::Vector(Box::new(Ty::Isize), 3),
                4 => *ty = Ty::Vector(Box::new(Ty::Char), 3),
                5 => *ty = Ty::Vector(Box::new(Ty::Ptr), 3),
                6 => *ty = Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::Bool), 3)), 3),
                7 => *value = C::Vector(ints(&[1, 2])),
                8 => *value = C::Vector(vec![C::Int(1), C::Bool(true), C::Int(3)]),
                _ => unreachable!(),
            }
            let binary = trust_ir::binary::serialize_module(&module).unwrap();
            let text = trust_ir::format::text_checked(&module).unwrap();
            let json = serde_json::to_vec(&module).unwrap();
            let message_pack = rmp_serde::to_vec(&module).unwrap();
            let mut decoded = vec![
                ("original", module),
                (
                    "binary",
                    trust_ir::binary::deserialize_module(&binary).unwrap(),
                ),
                ("JSON", serde_json::from_slice(&json).unwrap()),
                ("MessagePack", rmp_serde::from_slice(&message_pack).unwrap()),
            ];
            if mutation == 0 {
                // The text decoder enforces this type rule before a Module
                // exists. Preserve that earlier refusal as its own control.
                let error = trust_ir::parser::parse_module(&text).unwrap_err();
                assert_eq!(error.message, "vector lane count must be nonzero");
                checked += 1;
            } else {
                decoded.push(("text", trust_ir::parser::parse_module(&text).unwrap()));
            }
            for (codec, module) in decoded {
                let errors = trust_ir_build::validate_module(&module);
                let named_refusal = errors.iter().any(|error| {
                    if mutation <= 6 {
                        matches!(error, ValidationError::InvalidVectorType { .. })
                    } else {
                        matches!(error, ValidationError::ConstTypeMismatch { .. })
                    }
                });
                assert!(
                    named_refusal,
                    "{bits}/{codec}/mutation{mutation}: {errors:?}"
                );
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 90);
}

#[test]
fn vector_operations_dialect_extract_retains_its_declared_runtime_census() {
    use trust_ir::interpret::{
        ArrayValue, InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter,
    };
    let mut checked = 0;
    for bits in [32, 64] {
        let mut mb =
            ModuleBuilder::new_with_target_info("dialect_extract_census", semr_target(bits));
        let ty = Ty::Vector(Box::new(Ty::I32), 4);
        let sig = mb.add_func_type(vec![ty.clone()], vec![Ty::I32]);
        let mut fb = mb.function("extract", sig);
        let entry = fb.create_block();
        let vector = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let result = fb.dialect_op(trust_ir::dialect::vector::extract_lane(
            ty.clone(),
            vector,
            1,
        ))[0];
        fb.ret(vec![result]);
        let function = fb.build();
        let module = mb.build().expect("valid bounded dialect extract");
        for (codec, module) in codeced(module) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            let argument = |count| InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Vector(ArrayValue::from_vec(
                    (0..count)
                        .map(|lane| InterpretValue::int_at(Ty::I32, lane, bits).unwrap())
                        .collect(),
                )),
            };
            let interpreter = Interpreter::with_module(&module);
            let valid = interpreter.execute_func(function, [argument(4)]).unwrap();
            assert_eq!(valid.host_calls, 0);
            assert_eq!(
                valid.returns,
                vec![InterpretValue::int_at(Ty::I32, 1, bits).unwrap()]
            );
            let error = interpreter
                .execute_func(function, [argument(8)])
                .unwrap_err();
            assert_eq!(
                error.code,
                InterpretErrorCode::UnsupportedVectorShape,
                "{bits}/{codec}: {error}"
            );
            checked += 2;
        }
    }
    assert_eq!(checked, 20);
}
