// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pointer transport is distinct from numeric/image observation. Narrow
//! results are zero-extended before returning, so renderer normalization
//! cannot hide a noncanonical PtrToInt producer. All ordinary modules validate
//! before and after each cold codec, including target-layout Transmute.
//! Standalone-function validation has a different layout-evidence boundary.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use std::collections::BTreeMap;
use std::path::PathBuf;
use trust_ir::constant::Constant as C;
use trust_ir::inst::{CastOp, ICmpOp};
use trust_ir::value::{FuncId, ValueId};
use trust_ir::{FatPtrKind, Module, Ty};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

#[derive(Clone, Copy, Debug)]
enum Pointer {
    Gep(u64),
    Dangling(u64),
    Dead,
    Poison,
}

impl Pointer {
    fn label(self) -> String {
        match self {
            Self::Gep(offset) => format!("gep_{offset}"),
            Self::Dangling(address) => format!("dangling_{address}"),
            Self::Dead => "dead".into(),
            Self::Poison => "poison".into(),
        }
    }
    fn address(self) -> Option<u128> {
        match self {
            Self::Gep(offset) => Some(1024 + u128::from(offset)),
            Self::Dangling(address) => Some(u128::from(address)),
            Self::Dead => Some(1024),
            Self::Poison => None,
        }
    }
    fn early_ub(self, bits: u32) -> bool {
        matches!(self, Self::Gep(_)) && bits == 32 && self.address().unwrap() >= 1u128 << 32
    }
    fn emit(self, fb: &mut FunctionBuilder<'_>) -> ValueId {
        match self {
            Self::Gep(offset) => {
                let base = fb.alloca(Ty::U8);
                let index = fb.const_value(Ty::U64, C::Int(i128::from(offset)));
                fb.gep(Ty::U8, base, vec![index])
            }
            Self::Dangling(address) => {
                let integer = fb.const_value(Ty::U64, C::Int(i128::from(address)));
                fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, integer)
            }
            Self::Dead => {
                let pointer = fb.alloca(Ty::U8);
                fb.dealloc(pointer);
                pointer
            }
            Self::Poison => fb.undef(Ty::Ptr),
        }
    }
    fn exposed(self, bits: u32, width: u32) -> Expected {
        if self.early_ub(bits)
            || self
                .address()
                .is_none_or(|address| address > u128::from(u64::MAX))
        {
            Expected::Ub
        } else {
            let address = self.address().unwrap();
            Expected::Int(if width == 128 {
                address
            } else {
                address & ((1u128 << width) - 1)
            })
        }
    }
    fn transported(self, bits: u32, inspect_poison: bool) -> Expected {
        if self.early_ub(bits) || (inspect_poison && matches!(self, Self::Poison)) {
            Expected::Ub
        } else {
            Expected::Int(7)
        }
    }
}

fn pointers(bits: u32) -> Vec<Pointer> {
    let mut values = [0, 1, u64::MAX - 1024, u64::MAX - 1023, u64::MAX]
        .into_iter()
        .map(Pointer::Gep)
        .collect::<Vec<_>>();
    values.extend(
        [
            0,
            1,
            127,
            128,
            255,
            1024,
            1u64 << (bits - 1),
            if bits == 32 {
                u64::from(u32::MAX)
            } else {
                u64::MAX
            },
        ]
        .into_iter()
        .map(Pointer::Dangling),
    );
    values.extend([Pointer::Dead, Pointer::Poison]);
    values
}

#[derive(Clone, Debug)]
enum Expected {
    Int(u128),
    Bool(bool),
    Ub,
    TypeError,
    // The first integer->float reinterpretation can retain an existing
    // named NaN-payload boundary. It earns no agreement or admission credit.
    TypeErrorOrFloatBoundary,
}

impl Expected {
    fn rust_matches(&self, verdict: &Verdict) -> bool {
        match (self, verdict) {
            (Self::Int(expected), Verdict::Ok(_) | Verdict::Graph(_)) => {
                verdict
                    == &Verdict::Ok(vec![Val::Int {
                        width: 128,
                        raw: *expected,
                    }])
            }
            (Self::Bool(expected), Verdict::Ok(_) | Verdict::Graph(_)) => {
                verdict == &Verdict::Ok(vec![Val::Bool(*expected)])
            }
            (Self::Ub, Verdict::Ub(_)) => true,
            (Self::TypeError | Self::TypeErrorOrFloatBoundary, Verdict::TypeError(_)) => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
struct Case {
    id: FuncId,
    label: String,
    expected: Expected,
}

fn width(ty: &Ty, bits: u32) -> u32 {
    match ty {
        Ty::I8 | Ty::U8 => 8,
        Ty::I16 | Ty::U16 => 16,
        Ty::I32 | Ty::U32 | Ty::Char => 32,
        Ty::I64 | Ty::U64 => 64,
        Ty::I128 | Ty::U128 => 128,
        Ty::Isize | Ty::Usize => bits,
        _ => unreachable!(),
    }
}

fn integer_types() -> [Ty; 12] {
    [
        Ty::I8,
        Ty::U8,
        Ty::I16,
        Ty::U16,
        Ty::I32,
        Ty::U32,
        Ty::I64,
        Ty::U64,
        Ty::I128,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
    ]
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum CastObservation {
    Direct,
    Memory,
    Char,
}

fn observed_cast(
    mb: &mut ModuleBuilder,
    cases: &mut Vec<Case>,
    bits: u32,
    pointer: Pointer,
    op: CastOp,
    destination: Ty,
    observation: CastObservation,
) {
    let memory = observation == CastObservation::Memory;
    let via_char = observation == CastObservation::Char;
    let label = format!(
        "{}_{op:?}_{destination:?}_memory{memory}_char{via_char}",
        pointer.label()
    );
    let result_ty = if destination == Ty::I128 {
        Ty::I128
    } else {
        Ty::U128
    };
    let sig = mb.add_func_type(vec![], vec![result_ty]);
    let mut fb = mb.function(label.clone(), sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let mut value = pointer.emit(&mut fb);
    if memory {
        let cell = fb.alloca(Ty::Ptr);
        fb.store(Ty::Ptr, cell, value);
        value = fb.load(Ty::Ptr, cell);
    }
    let mut result = fb.cast(op, Ty::Ptr, destination.clone(), value);
    let destination_width = width(&destination, bits);
    if via_char {
        assert!(destination_width < 32);
        result = fb.cast(CastOp::ZExt, destination.clone(), Ty::Char, result);
        result = fb.cast(CastOp::ZExt, Ty::Char, Ty::U128, result);
    } else if destination_width < 128 {
        result = fb.cast(CastOp::ZExt, destination.clone(), Ty::U128, result);
    }
    fb.ret(vec![result]);
    let expected = if pointer.early_ub(bits) || matches!(pointer, Pointer::Poison) {
        Expected::Ub
    } else if op == CastOp::Bitcast && destination_width != bits {
        Expected::TypeError
    } else {
        pointer.exposed(bits, destination_width)
    };
    cases.push(Case {
        id: fb.build(),
        label,
        expected,
    });
}

fn ordinary_cases(bits: u32) -> (Module, Vec<Case>) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("pointer_observations_{bits}"),
        semr_target(bits),
    );
    let mut cases = Vec::new();
    for pointer in pointers(bits) {
        for ty in integer_types() {
            for memory in [false, true] {
                observed_cast(
                    &mut mb,
                    &mut cases,
                    bits,
                    pointer,
                    CastOp::PtrToInt,
                    ty.clone(),
                    if memory {
                        CastObservation::Memory
                    } else {
                        CastObservation::Direct
                    },
                );
            }
        }
        // PtrToInt->Char itself is not validator-admitted. This actual
        // admitted resize chain exercises the strict Char boundary instead.
        for ty in [Ty::I8, Ty::U8, Ty::I16, Ty::U16] {
            observed_cast(
                &mut mb,
                &mut cases,
                bits,
                pointer,
                CastOp::PtrToInt,
                ty,
                CastObservation::Char,
            );
        }
        // Module validation supplies actual-target layout evidence, unlike
        // the standalone function validator default-width check.
        let fixed_words = if bits == 32 {
            [Ty::I32, Ty::U32]
        } else {
            [Ty::I64, Ty::U64]
        };
        for ty in [Ty::Isize, Ty::Usize].into_iter().chain(fixed_words) {
            observed_cast(
                &mut mb,
                &mut cases,
                bits,
                pointer,
                CastOp::Bitcast,
                ty,
                CastObservation::Direct,
            );
        }
        for op in [
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
        ] {
            let label = format!("{}_icmp_{op:?}", pointer.label());
            let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
            let mut fb = mb.function(label.clone(), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let value = pointer.emit(&mut fb);
            let result = fb.icmp(op, Ty::Ptr, value, value);
            fb.ret(vec![result]);
            let expected = match pointer.exposed(bits, bits) {
                Expected::Ub => Expected::Ub,
                _ => Expected::Bool(matches!(
                    op,
                    ICmpOp::Eq | ICmpOp::Ule | ICmpOp::Uge | ICmpOp::Sle | ICmpOp::Sge
                )),
            };
            cases.push(Case {
                id: fb.build(),
                label,
                expected,
            });
        }
        for operation in [
            "copy",
            "select",
            "ptr_to_ptr",
            "thin_parts",
            "fat_parts",
            "fat_store",
            "store_no_reload",
        ] {
            let label = format!("{}_{operation}", pointer.label());
            let sig = mb.add_func_type(vec![], vec![Ty::U128]);
            let mut fb = mb.function(label.clone(), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let value = pointer.emit(&mut fb);
            let expected = match operation {
                "copy" => {
                    fb.copy(Ty::Ptr, value);
                    pointer.transported(bits, false)
                }
                "select" => {
                    let condition = fb.const_value(Ty::Bool, C::Bool(true));
                    let null = fb.null_ptr();
                    fb.select(Ty::Ptr, condition, value, null);
                    pointer.transported(bits, false)
                }
                "ptr_to_ptr" => {
                    fb.cast(CastOp::PtrToPtr, Ty::Ptr, Ty::Ptr, value);
                    pointer.transported(bits, true)
                }
                "thin_parts" => {
                    let unit = fb.const_value(Ty::Unit, C::PhantomData);
                    fb.ptr_from_parts(Ty::Ptr, Ty::Unit, value, unit);
                    pointer.transported(bits, true)
                }
                "fat_parts" | "fat_store" => {
                    let metadata_ty = if bits == 32 { Ty::U32 } else { Ty::U64 };
                    let metadata = fb.const_value(metadata_ty.clone(), C::Int(0));
                    let fat_ty = Ty::FatPtr(FatPtrKind::Str);
                    let fat = fb.ptr_from_parts(fat_ty.clone(), metadata_ty, value, metadata);
                    if operation == "fat_store" {
                        let cell = fb.alloca(fat_ty.clone());
                        fb.store(fat_ty, cell, fat);
                        match pointer.exposed(bits, bits) {
                            Expected::Ub => Expected::Ub,
                            _ => Expected::Int(7),
                        }
                    } else {
                        pointer.transported(bits, true)
                    }
                }
                "store_no_reload" => {
                    let cell = fb.alloca(Ty::Ptr);
                    fb.store(Ty::Ptr, cell, value);
                    if matches!(pointer, Pointer::Poison) {
                        // Nonstrict poison Store transports its None bytes.
                        Expected::Int(7)
                    } else {
                        // Defined pointer Store observes the address even
                        // when no later instruction reads the image.
                        match pointer.exposed(bits, bits) {
                            Expected::Ub => Expected::Ub,
                            _ => Expected::Int(7),
                        }
                    }
                }
                _ => unreachable!(),
            };
            let seven = fb.const_value(Ty::U128, C::Int(7));
            fb.ret(vec![seven]);
            cases.push(Case {
                id: fb.build(),
                label,
                expected,
            });
        }
        let label = format!("{}_pointer_to_float_discarded", pointer.label());
        let sig = mb.add_func_type(vec![], vec![Ty::U128]);
        let mut fb = mb.function(label.clone(), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = pointer.emit(&mut fb);
        let float_ty = if bits == 32 { Ty::F32 } else { Ty::F64 };
        fb.cast(CastOp::Bitcast, Ty::Ptr, float_ty, value);
        let seven = fb.const_value(Ty::U128, C::Int(7));
        fb.ret(vec![seven]);
        let expected = if pointer.early_ub(bits) || matches!(pointer, Pointer::Poison) {
            Expected::Ub
        } else {
            Expected::TypeError
        };
        cases.push(Case {
            id: fb.build(),
            label,
            expected,
        });
    }
    for number in [0.0, -0.0, 1.0, -1.0] {
        let label = format!("finite_float_to_pointer_{:016x}", f64::to_bits(number));
        let sig = mb.add_func_type(vec![], vec![Ty::U128]);
        let mut fb = mb.function(label.clone(), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let float_ty = if bits == 32 { Ty::F32 } else { Ty::F64 };
        let float = fb.const_value(float_ty.clone(), C::Float(number));
        fb.cast(CastOp::Bitcast, float_ty, Ty::Ptr, float);
        let seven = fb.const_value(Ty::U128, C::Int(7));
        fb.ret(vec![seven]);
        cases.push(Case {
            id: fb.build(),
            label,
            expected: Expected::TypeError,
        });
    }
    let nan_words = if bits == 32 {
        [0x7fc0_0001u64, 0x7f80_0001]
    } else {
        [0x7ff8_0000_0000_0001, 0x7ff0_0000_0000_0001]
    };
    for raw in nan_words {
        let label = format!("nan_payload_boundary_{raw:016x}");
        let sig = mb.add_func_type(vec![], vec![Ty::U128]);
        let mut fb = mb.function(label.clone(), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let word_ty = if bits == 32 { Ty::U32 } else { Ty::U64 };
        let float_ty = if bits == 32 { Ty::F32 } else { Ty::F64 };
        let integer = fb.const_value(word_ty.clone(), C::Int(i128::from(raw)));
        let float = fb.cast(CastOp::Bitcast, word_ty, float_ty.clone(), integer);
        fb.cast(CastOp::Bitcast, float_ty, Ty::Ptr, float);
        let seven = fb.const_value(Ty::U128, C::Int(7));
        fb.ret(vec![seven]);
        cases.push(Case {
            id: fb.build(),
            label,
            expected: Expected::TypeErrorOrFloatBoundary,
        });
    }
    let module = mb.build().expect("pointer observation module");
    assert!(
        module.functions.len() < 1024,
        "address arithmetic assumes initial1024"
    );
    (module, cases)
}

fn codecs(module: Module) -> Vec<(&'static str, Module)> {
    let binary = trust_ir::binary::serialize_module(&module).unwrap();
    let text = trust_ir::format::text_checked(&module).unwrap();
    let json = serde_json::to_vec(&module).unwrap();
    let message_pack = rmp_serde::to_vec(&module).unwrap();
    vec![
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

fn run_cohort(modules: Vec<(String, Module, Vec<Case>)>, name: &str) {
    let baseline = std::env::var_os("TRUST_IR_POINTER_OBSERVATION_BASELINE_BIN").map(PathBuf::from);
    let executable = if let Some(path) = &baseline {
        path.clone()
    } else {
        let Oracle::Ready(exe) = oracle() else { return };
        exe.to_path_buf()
    };
    let batches = modules
        .iter()
        .map(|(label, module, cases)| Batch {
            label: label.clone(),
            module,
            runs: cases.iter().map(|case| (case.id, vec![])).collect(),
        })
        .collect::<Vec<_>>();
    let reports = differential(&executable, &batches);
    assert_eq!(
        reports.len(),
        modules
            .iter()
            .map(|(_, _, cases)| cases.len())
            .sum::<usize>()
    );
    let mut gaps = 0usize;
    let mut paired_type_errors = 0usize;
    let mut boundaries = BTreeMap::new();
    let mut kinds = BTreeMap::new();
    let mut expected_counts = BTreeMap::new();
    let mut gap_cases = BTreeMap::new();
    let mut exact_agreements = 0usize;
    let mut evidence = String::new();
    for (report, case) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, cases)| cases))
    {
        assert!(
            case.expected.rust_matches(&report.rust),
            "independent Rust expectation {name}/{}: expected {:?}; {report:?}",
            case.label,
            case.expected
        );
        *expected_counts
            .entry(match case.expected {
                Expected::Int(_) | Expected::Bool(_) => "ok",
                Expected::Ub => "ub",
                Expected::TypeError => "type_error",
                Expected::TypeErrorOrFloatBoundary => "type_error_or_float_boundary",
            })
            .or_insert(0usize) += 1;
        let boundary = matches!(case.expected, Expected::TypeErrorOrFloatBoundary)
            && matches!(&report.lean, Verdict::Unsupported(feature) if feature == "float");
        let accepted = if boundary {
            *boundaries.entry("float NaN payload").or_insert(0usize) += 1;
            true
        } else if matches!(
            case.expected,
            Expected::TypeError | Expected::TypeErrorOrFloatBoundary
        ) {
            let paired = matches!(report.lean, Verdict::TypeError(_));
            paired_type_errors += usize::from(paired);
            paired
        } else {
            case.expected.rust_matches(&report.lean) && report.comparison == Comparison::Agree
        };
        if accepted
            && !boundary
            && matches!(
                case.expected,
                Expected::Int(_) | Expected::Bool(_) | Expected::Ub
            )
        {
            exact_agreements += 1;
        }
        if !accepted {
            gaps += 1;
            *gap_cases
                .entry(format!("{}/{}", report.label, case.label))
                .or_insert(0usize) += 1;
            *kinds
                .entry(format!(
                    "{} -> {}",
                    report.rust.class(),
                    report.lean.class()
                ))
                .or_insert(0usize) += 1;
            if gaps <= 16 {
                eprintln!("POINTER_GAP {name}/{} {report:?}", case.label);
            }
        }
        evidence.push_str(&format!(
            "{} expected {:?}: {report:?}\n",
            case.label, case.expected
        ));
    }
    eprintln!(
        "POINTER_OBSERVATIONS {name}: {} runs; {gaps} gaps; {paired_type_errors} paired TypeError; boundaries {boundaries:?}; {kinds:?}",
        reports.len()
    );
    if let Some(directory) = std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR") {
        let directory = PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            directory.join(format!("pointer-{name}-reports.txt")),
            evidence,
        )
        .unwrap();
        std::fs::write(directory.join(format!("pointer-{name}-summary.json")), serde_json::to_vec_pretty(&serde_json::json!({"cohort":name,"runs":reports.len(),"gaps":gaps,"paired_type_errors":paired_type_errors,"exact_agreements":exact_agreements,"expected_counts":expected_counts,"boundaries":boundaries,"gap_kinds":kinds,"gap_cases":gap_cases})).unwrap()).unwrap();
    }
    if baseline.is_some() {
        assert!(gaps > 0, "baseline no longer exposes a genuine gap");
    } else {
        assert_eq!(gaps, 0, "pointer observer parity");
    }
}

#[test]
fn validated_pointer_observations_preserve_target_words_and_transport() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, cases) = ordinary_cases(bits);
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{bits}/original: {errors:#?}");
        for (codec, decoded) in codecs(module) {
            let errors = trust_ir_build::validate_module(&decoded);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:#?}");
            modules.push((format!("pointer/{bits}/{codec}"), decoded, cases.clone()));
        }
    }
    run_cohort(modules, "validated");
}

#[test]
fn validated_transmute_pointer_words_observe_actual_target_layout() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb =
            ModuleBuilder::new_with_target_info(format!("transmute_{bits}"), semr_target(bits));
        let mut cases = Vec::new();
        for pointer in pointers(bits) {
            for ty in if bits == 32 {
                [Ty::I32, Ty::U32]
            } else {
                [Ty::I64, Ty::U64]
            } {
                observed_cast(
                    &mut mb,
                    &mut cases,
                    bits,
                    pointer,
                    CastOp::Transmute,
                    ty,
                    CastObservation::Direct,
                );
            }
        }
        let module = mb.build().unwrap();
        for (codec, decoded) in codecs(module) {
            let errors = trust_ir_build::validate_module(&decoded);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:#?}");
            modules.push((format!("transmute/{bits}/{codec}"), decoded, cases.clone()));
        }
    }
    run_cohort(modules, "transmute");
}

#[test]
fn pointer_to_char_is_a_validator_refusal_not_an_admitted_case() {
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info(
            format!("ptr_to_char_admission_{bits}"),
            semr_target(bits),
        );
        let sig = mb.add_func_type(vec![], vec![Ty::Char]);
        let mut fb = mb.function("refused", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let pointer = fb.null_ptr();
        let value = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Char, pointer);
        fb.ret(vec![value]);
        fb.build();
        let module = mb.build().unwrap();
        let errors = trust_ir_build::validate_module(&module);
        assert_eq!(errors.len(), 1, "{errors:#?}");
        assert!(matches!(
            errors[0],
            trust_ir_build::ValidationError::CastIncompatible { .. }
        ));
    }
}
