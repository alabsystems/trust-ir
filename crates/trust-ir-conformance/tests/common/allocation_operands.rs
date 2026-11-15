// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use std::path::PathBuf;
use trust_ir::constant::Constant;
use trust_ir::inst::{AllocOrigin, CastOp, Inst};
use trust_ir::interpret::InterpretValue;
use trust_ir::value::{FuncId, ValueId};
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy, Debug)]
enum Operation {
    StackZero,
    HeapZero,
    GepZero,
    StackByte,
    HeapByte,
    StackWide,
    HeapWide,
    GepWide,
}
impl Operation {
    fn element(self) -> Ty {
        match self {
            Self::StackZero | Self::HeapZero | Self::GepZero => Ty::Unit,
            Self::StackByte | Self::HeapByte => Ty::U8,
            _ => Ty::I128,
        }
    }
    fn size(self) -> u128 {
        match self.element() {
            Ty::Unit => 0,
            Ty::U8 => 1,
            _ => 16,
        }
    }
    fn is_gep(self) -> bool {
        matches!(self, Self::GepZero | Self::GepWide)
    }
    fn slack(self) -> u128 {
        if matches!(self, Self::HeapZero | Self::HeapByte | Self::HeapWide) {
            16
        } else {
            0
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Expected {
    Ok,
    Ub,
    OutOfMemory,
    OutOfFuel,
    TypeError,
}
impl Expected {
    fn check(self, verdict: &Verdict, label: &str) {
        match self {
            Self::Ok => assert_eq!(
                verdict,
                &Verdict::Ok(vec![Val::Int { width: 32, raw: 7 }]),
                "{label}"
            ),
            Self::Ub => assert!(matches!(verdict, Verdict::Ub(_)), "{label}: {verdict:?}"),
            Self::OutOfFuel => assert!(
                matches!(verdict, Verdict::OutOfFuel),
                "{label}: {verdict:?}"
            ),
            Self::TypeError => assert!(
                matches!(verdict, Verdict::TypeError(_)),
                "{label}: {verdict:?}"
            ),
            Self::OutOfMemory => assert!(
                matches!(verdict, Verdict::OutOfMemory),
                "{label}: {verdict:?}"
            ),
        }
    }
}

#[derive(Clone)]
struct Case {
    id: FuncId,
    args: Vec<InterpretValue>,
    expected: Expected,
    label: String,
}

fn expected(operation: Operation, bits: u32, magnitude: Option<u128>) -> Expected {
    let Some(value) = magnitude else {
        return Expected::Ub;
    };
    let max_word = u128::from(u64::MAX);
    if value > max_word || (!operation.is_gep() && value == 0) {
        return Expected::Ub;
    }
    let bytes = value * operation.size();
    if bytes > max_word {
        return Expected::Ub;
    }
    if operation.is_gep() {
        if bits == 32 && 1024 + bytes >= (1u128 << 32) {
            Expected::Ub
        } else {
            Expected::Ok
        }
    } else {
        let footprint = (bytes + operation.slack()).max(1);
        if footprint > max_word
            || 1024 + footprint > max_word
            || (bits == 32 && 1024 + footprint > (1u128 << 32))
        {
            Expected::OutOfMemory
        } else {
            Expected::Ok
        }
    }
}

fn literal(ty: &Ty, raw: u128, width: u32) -> Constant {
    if *ty == Ty::U128 && raw > i128::MAX as u128 {
        Constant::U128(raw)
    } else if ty.is_signed() && width < 128 && raw >= (1u128 << (width - 1)) {
        Constant::Int(raw as i128 - (1i128 << width))
    } else {
        Constant::Int(raw as i128)
    }
}

fn cases(bits: u32) -> (Module, Vec<Case>) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("allocation_operands_{bits}"),
        semr_target(bits),
    );
    let mut cases = Vec::new();
    let mut patches: Vec<(FuncId, ValueId)> = Vec::new();
    let operations = [
        Operation::StackZero,
        Operation::HeapZero,
        Operation::GepZero,
        Operation::StackWide,
        Operation::HeapWide,
        Operation::GepWide,
    ];
    let integers = [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::Isize,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Usize,
    ];
    for ty in integers {
        let width = match ty {
            Ty::I8 | Ty::U8 => 8,
            Ty::I16 | Ty::U16 => 16,
            Ty::I32 | Ty::U32 => 32,
            Ty::I64 | Ty::U64 => 64,
            Ty::I128 | Ty::U128 => 128,
            _ => bits,
        };
        let sign = 1u128 << (width - 1);
        let maximum = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        let mut patterns = vec![0, 1, sign - 1, sign, maximum];
        if width == 128 {
            patterns.push(1u128 << 64);
        }
        if width == 64 {
            patterns.push(1u128 << 32);
        }
        patterns.sort_unstable();
        patterns.dedup();
        for (phase, raw) in patterns.into_iter().enumerate() {
            let magnitude = if ty.is_signed() && raw >= sign {
                None
            } else {
                Some(raw)
            };
            for parameter in [false, true] {
                for operation in operations {
                    let label = format!("{ty:?}/{phase}/{parameter}/{operation:?}");
                    let signature = mb.add_func_type(
                        if parameter { vec![ty.clone()] } else { vec![] },
                        vec![Ty::I32],
                    );
                    let mut fb = mb.function(label.clone(), signature);
                    let entry = fb.create_block();
                    let param = if parameter {
                        Some(fb.add_block_param(entry, ty.clone()))
                    } else {
                        None
                    };
                    fb.switch_to_block(entry);
                    let count = param
                        .unwrap_or_else(|| fb.const_value(ty.clone(), literal(&ty, raw, width)));
                    match operation {
                        Operation::StackZero | Operation::StackByte | Operation::StackWide => {
                            fb.alloca(operation.element());
                        }
                        Operation::HeapZero | Operation::HeapByte | Operation::HeapWide => {
                            fb.heap_alloc(
                                operation.element(),
                                Some(count),
                                None,
                                AllocOrigin::RustHeap,
                            );
                        }
                        Operation::GepZero | Operation::GepWide => {
                            let base = fb.alloca(operation.element());
                            fb.gep(operation.element(), base, vec![count]);
                        }
                    }
                    let answer = fb.iconst(Ty::I32, 7);
                    fb.ret(vec![answer]);
                    let id = fb.build();
                    if matches!(
                        operation,
                        Operation::StackZero | Operation::StackByte | Operation::StackWide
                    ) {
                        patches.push((id, count));
                    }
                    cases.push(Case {
                        id,
                        args: if parameter {
                            vec![InterpretValue::int_at(ty.clone(), raw as i128, bits).unwrap()]
                        } else {
                            vec![]
                        },
                        expected: expected(operation, bits, magnitude),
                        label,
                    });
                }
            }
        }
        for operation in operations {
            let label = format!("poison/{ty:?}/{operation:?}");
            let signature = mb.add_func_type(vec![], vec![Ty::I32]);
            let mut fb = mb.function(label.clone(), signature);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let count = fb.undef(ty.clone());
            match operation {
                Operation::StackZero | Operation::StackByte | Operation::StackWide => {
                    fb.alloca(operation.element());
                }
                Operation::HeapZero | Operation::HeapByte | Operation::HeapWide => {
                    fb.heap_alloc(
                        operation.element(),
                        Some(count),
                        None,
                        AllocOrigin::RustHeap,
                    );
                }
                Operation::GepZero | Operation::GepWide => {
                    let base = fb.alloca(operation.element());
                    fb.gep(operation.element(), base, vec![count]);
                }
            }
            let answer = fb.iconst(Ty::I32, 7);
            fb.ret(vec![answer]);
            let id = fb.build();
            if matches!(
                operation,
                Operation::StackZero | Operation::StackByte | Operation::StackWide
            ) {
                patches.push((id, count));
            }
            cases.push(Case {
                id,
                args: vec![],
                expected: Expected::Ub,
                label,
            });
        }
    }
    // Valid Char carriers are integer-kind allocation counts in the actual
    // interpreter. Unicode validity itself belongs to the separate SSA guard.
    for raw in [0, 127, 0x10ffff] {
        for operation in [Operation::StackZero, Operation::HeapZero] {
            let label = format!("Char/{raw}/{operation:?}");
            let signature = mb.add_func_type(vec![Ty::Char], vec![Ty::I32]);
            let mut fb = mb.function(label.clone(), signature);
            let entry = fb.create_block();
            let count = fb.add_block_param(entry, Ty::Char);
            fb.switch_to_block(entry);
            if matches!(operation, Operation::StackZero) {
                fb.alloca(Ty::Unit);
            } else {
                fb.heap_alloc(Ty::Unit, Some(count), None, AllocOrigin::RustHeap);
            }
            let answer = fb.iconst(Ty::I32, 7);
            fb.ret(vec![answer]);
            let id = fb.build();
            if matches!(operation, Operation::StackZero) {
                patches.push((id, count));
            }
            cases.push(Case {
                id,
                args: vec![InterpretValue::int_at(Ty::Char, raw, bits).unwrap()],
                expected: expected(operation, bits, Some(raw as u128)),
                label,
            });
        }
    }
    // Two GEPs must check the provenance-relative u64 offset, while a
    // dangling base checks its absolute word. No target-width count narrowing.
    for (label, dangling, second) in [
        ("real-offset-max", false, false),
        ("real-offset-overflow", false, true),
        ("dangling-address-overflow", true, false),
    ] {
        let signature = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function(label, signature);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let base = if dangling {
            let one = fb.iconst(Ty::U64, 1);
            fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, one)
        } else {
            fb.alloca(Ty::U8)
        };
        let index = fb.const_value(Ty::U128, literal(&Ty::U128, u128::from(u64::MAX), 128));
        let first = fb.gep(Ty::U8, base, vec![index]);
        if second {
            let one = fb.iconst(Ty::U64, 1);
            fb.gep(Ty::U8, first, vec![one]);
        }
        let answer = fb.iconst(Ty::I32, 7);
        fb.ret(vec![answer]);
        cases.push(Case {
            id: fb.build(),
            args: vec![],
            expected: if bits == 64 && !dangling && !second {
                Expected::Ok
            } else {
                Expected::Ub
            },
            label: label.into(),
        });
    }
    for ty in [Ty::I128, Ty::U128, Ty::U64] {
        for raw in [
            u128::from(u64::MAX),
            u128::from(u64::MAX) - 1024,
            u128::from(u64::MAX) - 1023,
            u128::from(u64::MAX) - 1040,
            (1u128 << 32) - 1024,
        ] {
            for operation in [Operation::StackByte, Operation::HeapByte] {
                let label = format!("capacity/{ty:?}/{raw}/{operation:?}");
                let signature = mb.add_func_type(vec![], vec![Ty::I32]);
                let mut fb = mb.function(label.clone(), signature);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let count = fb.const_value(
                    ty.clone(),
                    literal(&ty, raw, if ty == Ty::U64 { 64 } else { 128 }),
                );
                if matches!(operation, Operation::StackByte) {
                    fb.alloca(Ty::U8);
                } else {
                    fb.heap_alloc(Ty::U8, Some(count), None, AllocOrigin::RustHeap);
                }
                let answer = fb.iconst(Ty::I32, 7);
                fb.ret(vec![answer]);
                let id = fb.build();
                if matches!(operation, Operation::StackByte) {
                    patches.push((id, count));
                }
                cases.push(Case {
                    id,
                    args: vec![],
                    expected: expected(operation, bits, Some(raw)),
                    label,
                });
            }
        }
    }
    for ty in [Ty::Bool, Ty::F64, Ty::Ptr] {
        for poison in [false, true] {
            for operation in [Operation::StackZero, Operation::HeapZero] {
                let label = format!("kind/{ty:?}/{poison}/{operation:?}");
                let signature = mb.add_func_type(vec![], vec![Ty::I32]);
                let mut fb = mb.function(label.clone(), signature);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let count = if poison {
                    fb.undef(ty.clone())
                } else {
                    match ty {
                        Ty::Bool => fb.const_value(Ty::Bool, Constant::Bool(true)),
                        Ty::F64 => fb.fconst(Ty::F64, 1.0),
                        _ => fb.null_ptr(),
                    }
                };
                if matches!(operation, Operation::StackZero) {
                    fb.alloca(Ty::Unit);
                } else {
                    fb.heap_alloc(Ty::Unit, Some(count), None, AllocOrigin::RustHeap);
                }
                let answer = fb.iconst(Ty::I32, 7);
                fb.ret(vec![answer]);
                let id = fb.build();
                if matches!(operation, Operation::StackZero) {
                    patches.push((id, count));
                }
                cases.push(Case {
                    id,
                    args: vec![],
                    expected: if poison {
                        Expected::Ub
                    } else {
                        Expected::TypeError
                    },
                    label,
                });
            }
        }
    }
    let signature = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("instruction_budget_control", signature);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.br(entry, vec![]);
    cases.push(Case {
        id: fb.build(),
        args: vec![],
        expected: Expected::OutOfFuel,
        label: "instruction_budget_control".into(),
    });
    let mut module = mb.build().expect("allocation operands source");
    for (id, count) in patches {
        let function = module.functions.iter_mut().find(|f| f.id == id).unwrap();
        let allocation = function.blocks[0]
            .body
            .iter_mut()
            .find(|node| matches!(node.inst, Inst::Alloca { .. }))
            .unwrap();
        match &mut allocation.inst {
            Inst::Alloca { count: slot, .. } => {
                assert!(slot.is_none());
                *slot = Some(count);
            }
            _ => unreachable!(),
        }
    }
    assert!(
        module.functions.len() < 1024,
        "independent address expectations assume initial base 1024"
    );
    (module, cases)
}

#[test]
fn allocation_and_gep_operands_keep_declared_magnitudes_and_word_bounds() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, runs) = cases(bits);
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{bits}: {errors:#?}");
        let binary = trust_ir::binary::serialize_module(&module).unwrap();
        let text = trust_ir::format::text_checked(&module).unwrap();
        let json = serde_json::to_vec(&module).unwrap();
        let message_pack = rmp_serde::to_vec(&module).unwrap();
        if let Some(directory) = std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR") {
            let directory = PathBuf::from(directory);
            std::fs::create_dir_all(&directory).unwrap();
            for (extension, bytes) in [
                ("binary", binary.as_slice()),
                ("text", text.as_bytes()),
                ("json", json.as_slice()),
                ("msgpack", message_pack.as_slice()),
            ] {
                std::fs::write(
                    directory.join(format!("allocation-{bits}.{extension}")),
                    bytes,
                )
                .unwrap();
            }
        }
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
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:#?}");
            modules.push((format!("allocation/{bits}/{codec}"), decoded, runs.clone()));
        }
    }
    let baseline = std::env::var_os("TRUST_IR_ALLOCATION_BASELINE_BIN").map(PathBuf::from);
    let exe = if let Some(path) = &baseline {
        path.clone()
    } else {
        let Oracle::Ready(exe) = oracle() else { return };
        exe.to_path_buf()
    };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs
                .iter()
                .map(|case| (case.id, case.args.clone()))
                .collect(),
        })
        .collect();
    let reports = differential(&exe, &batches);
    if let Some(directory) = std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR") {
        use std::io::Write;
        let mut output = std::io::BufWriter::new(
            std::fs::File::create(PathBuf::from(directory).join("allocation-reports.txt")).unwrap(),
        );
        for (report, case) in reports
            .iter()
            .zip(modules.iter().flat_map(|(_, _, cases)| cases))
        {
            writeln!(
                output,
                "{} expected {:?}: {report:?}",
                case.label, case.expected
            )
            .unwrap();
        }
        output.flush().unwrap();
    }
    let mut disagreements = 0;
    let mut paired_type_errors = 0;
    let mut kinds = std::collections::BTreeMap::new();
    for (report, case) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, cases)| cases))
    {
        case.expected.check(&report.rust, &case.label);
        if matches!(case.expected, Expected::TypeError) {
            case.expected.check(&report.lean, &case.label);
            paired_type_errors += 1;
            continue;
        }
        if report.comparison != Comparison::Agree {
            disagreements += 1;
            *kinds
                .entry(format!("{:?}/{}", case.expected, report.lean.class()))
                .or_insert(0usize) += 1;
            if disagreements <= 8 {
                eprintln!("COUNT_GAP {} {report:?}", case.label);
            }
        }
    }
    eprintln!(
        "COUNT_OPERANDS {} valid runs, {disagreements} disagreements, {paired_type_errors} paired TypeError controls, {kinds:?}",
        reports.len()
    );
    if baseline.is_some() {
        assert!(
            disagreements > 0,
            "genuine before executable no longer exposes gaps"
        );
    } else {
        assert_eq!(disagreements, 0);
    }
}
