// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Scalar leaf memory at both canonical target widths. Invalid Char images
//! come from U32 stores, so validation never admits an invalid Char constant.
//! This tests typed memory results, not every possible SSA Char producer.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::inst::{AtomicRMWOp, Ordering};
use trust_ir::value::{FuncId, GlobalId};
use trust_ir::{Global, Linkage, Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy, Debug)]
enum Access {
    Plain,
    Strict,
    Atomic,
    Copy,
    Global,
    Exchange,
    Rmw,
}

const ACCESSES: [Access; 7] = [
    Access::Plain,
    Access::Strict,
    Access::Atomic,
    Access::Copy,
    Access::Global,
    Access::Exchange,
    Access::Rmw,
];

struct Cases {
    module: Module,
    runs: Vec<(FuncId, Option<Val>)>,
}

fn global(mb: &mut ModuleBuilder, count: &mut u32, ty: Ty, literal: C) -> GlobalId {
    let id = GlobalId::new(*count);
    *count += 1;
    mb.add_global(Global {
        name: format!("scalar_{ty:?}_{literal:?}"),
        ty,
        mutable: false,
        initializer: Some(literal),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    id
}

fn valid_cases(bits: u32) -> Cases {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("scalar_memory_{bits}"), semr_target(bits));
    let mut runs = Vec::new();
    let mut globals = 0;
    let mask = (1u128 << bits) - 1;
    for ty in [Ty::Usize, Ty::Isize, Ty::Char] {
        let values: Vec<i128> = if ty == Ty::Char {
            vec![0, 0x41, 0xD7FF, 0xE000, 0x10FFFF, 0x1F600]
        } else if ty == Ty::Isize {
            vec![-1, -(1i128 << (bits - 1)), 0, (1i128 << (bits - 1)) - 1]
        } else {
            vec![0, 1, mask as i128, 1i128 << (bits - 1)]
        };
        let width = if ty == Ty::Char { 32 } else { bits };
        for raw in values {
            let literal = C::Int(raw);
            for access in ACCESSES {
                let global = matches!(access, Access::Global)
                    .then(|| global(&mut mb, &mut globals, ty.clone(), literal.clone()));
                let sig = mb.add_func_type(vec![], vec![ty.clone()]);
                let mut fb = mb.function(format!("{ty:?}_{raw}_{access:?}"), sig);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let pointer = if let Some(id) = global {
                    fb.global_addr(id)
                } else {
                    fb.alloca(ty.clone())
                };
                let value = fb.const_value(ty.clone(), literal.clone());
                match access {
                    Access::Atomic => fb.atomic_store(ty.clone(), pointer, value, Ordering::SeqCst),
                    Access::Strict => fb.store_volatile(ty.clone(), pointer, value),
                    Access::Global => {}
                    _ => fb.store(ty.clone(), pointer, value),
                }
                let result = match access {
                    Access::Atomic => fb.atomic_load(ty.clone(), pointer, Ordering::SeqCst),
                    Access::Strict => fb.load_volatile(ty.clone(), pointer),
                    Access::Exchange => {
                        fb.cmpxchg(
                            ty.clone(),
                            pointer,
                            value,
                            value,
                            Ordering::SeqCst,
                            Ordering::SeqCst,
                        )
                        .0
                    }
                    Access::Rmw => {
                        let zero = fb.const_value(ty.clone(), C::Int(0));
                        fb.atomic_rmw(
                            AtomicRMWOp::Add,
                            ty.clone(),
                            pointer,
                            zero,
                            Ordering::SeqCst,
                        )
                    }
                    Access::Copy => {
                        let destination = fb.alloca(ty.clone());
                        let count = fb.const_value(Ty::Usize, C::Int(i128::from(width / 8)));
                        fb.memcopy(destination, pointer, count, false);
                        fb.load(ty.clone(), destination)
                    }
                    _ => fb.load(ty.clone(), pointer),
                };
                fb.ret(vec![result]);
                runs.push((
                    fb.build(),
                    Some(Val::Int {
                        width,
                        raw: (raw as u128)
                            & if width == bits {
                                mask
                            } else {
                                (1u128 << width) - 1
                            },
                    }),
                ));
            }
        }
    }
    assert_eq!(runs.len(), 98);
    Cases {
        module: mb.build().expect("valid scalar leaf memory"),
        runs,
    }
}

fn invalid_char_cases(bits: u32) -> Cases {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("invalid_char_memory_{bits}"),
        semr_target(bits),
    );
    let mut runs = Vec::new();
    let mut globals = 0;
    let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
    for raw in [0xD800, 0xDFFF, 0x110000, 0xFFFF_FFFF] {
        for access in ACCESSES {
            let global = matches!(access, Access::Global)
                .then(|| global(&mut mb, &mut globals, Ty::U32, C::Int(raw)));
            let mut fb = mb.function(format!("invalid_{raw}_{access:?}"), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let pointer = if let Some(id) = global {
                fb.global_addr(id)
            } else {
                fb.alloca(Ty::U32)
            };
            if !matches!(access, Access::Global) {
                let raw = fb.const_value(Ty::U32, C::Int(raw));
                fb.store(Ty::U32, pointer, raw);
            }
            // Discard the loaded Char: validity must fail at the memory
            // result boundary rather than only at Return or inspection.
            match access {
                Access::Strict => {
                    fb.load_volatile(Ty::Char, pointer);
                }
                Access::Atomic => {
                    fb.atomic_load(Ty::Char, pointer, Ordering::SeqCst);
                }
                Access::Exchange => {
                    let zero = fb.const_value(Ty::Char, C::Int(0));
                    fb.cmpxchg(
                        Ty::Char,
                        pointer,
                        zero,
                        zero,
                        Ordering::SeqCst,
                        Ordering::SeqCst,
                    );
                }
                Access::Rmw => {
                    let zero = fb.const_value(Ty::Char, C::Int(0));
                    fb.atomic_rmw(AtomicRMWOp::Add, Ty::Char, pointer, zero, Ordering::SeqCst);
                }
                Access::Copy => {
                    let destination = fb.alloca(Ty::U32);
                    let count = fb.const_value(Ty::Usize, C::Int(4));
                    fb.memcopy(destination, pointer, count, false);
                    fb.load(Ty::Char, destination);
                }
                _ => {
                    fb.load(Ty::Char, pointer);
                }
            }
            let yes = fb.const_value(Ty::Bool, C::Bool(true));
            fb.ret(vec![yes]);
            runs.push((fb.build(), None));
        }
    }
    assert_eq!(runs.len(), 28);
    Cases {
        module: mb.build().expect("valid IR with invalid raw Char images"),
        runs,
    }
}

fn uninitialized_cases(bits: u32) -> Cases {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("uninitialized_scalar_memory_{bits}"),
        semr_target(bits),
    );
    let mut runs = Vec::new();
    let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
    for ty in [Ty::Usize, Ty::Isize, Ty::Char] {
        for access in [Access::Plain, Access::Strict, Access::Atomic] {
            for inspect in [false, true] {
                let mut fb = mb.function(format!("{ty:?}_{access:?}_inspect_{inspect}"), sig);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let pointer = fb.alloca(ty.clone());
                let value = match access {
                    Access::Plain => fb.load(ty.clone(), pointer),
                    Access::Strict => fb.load_volatile(ty.clone(), pointer),
                    Access::Atomic => fb.atomic_load(ty.clone(), pointer, Ordering::SeqCst),
                    _ => unreachable!(),
                };
                let result = if inspect {
                    fb.icmp(trust_ir::ICmpOp::Eq, ty.clone(), value, value)
                } else {
                    fb.const_value(Ty::Bool, C::Bool(true))
                };
                fb.ret(vec![result]);
                runs.push((
                    fb.build(),
                    if matches!(access, Access::Plain) && !inspect {
                        Some(Val::Bool(true))
                    } else {
                        None
                    },
                ));
            }
        }
    }
    assert_eq!(runs.len(), 18);
    Cases {
        module: mb.build().expect("valid uninitialized scalar memory"),
        runs,
    }
}

fn poison_store_cases(bits: u32) -> Cases {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("scalar_poison_store_{bits}"),
        semr_target(bits),
    );
    let mut runs = Vec::new();
    let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
    for ty in [Ty::Usize, Ty::Isize, Ty::Char] {
        for partial in [false, true] {
            for access in [Access::Plain, Access::Strict, Access::Atomic] {
                let mut fb = mb.function(format!("{ty:?}_partial_{partial}_{access:?}"), sig);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let destination = fb.alloca(ty.clone());
                let value = if partial {
                    let source = fb.alloca(ty.clone());
                    let byte = fb.const_value(Ty::U8, C::Int(65));
                    fb.store(Ty::U8, source, byte);
                    fb.load(ty.clone(), source)
                } else {
                    fb.undef(ty.clone())
                };
                match access {
                    Access::Plain => {
                        fb.store(ty.clone(), destination, value);
                        // A plain reload of the transported image remains
                        // inert until inspected; Char must not pre-validate it.
                        fb.load(ty.clone(), destination);
                    }
                    Access::Strict => fb.store_volatile(ty.clone(), destination, value),
                    Access::Atomic => {
                        fb.atomic_store(ty.clone(), destination, value, Ordering::SeqCst)
                    }
                    _ => unreachable!(),
                }
                let result = fb.const_value(Ty::Bool, C::Bool(true));
                fb.ret(vec![result]);
                runs.push((
                    fb.build(),
                    matches!(access, Access::Plain).then_some(Val::Bool(true)),
                ));
            }
        }
    }
    assert_eq!(runs.len(), 18);
    Cases {
        module: mb.build().expect("valid scalar poison transports"),
        runs,
    }
}

fn check_cases(make: fn(u32) -> Cases, count: usize) {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let Cases { module, runs } = make(bits);
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
            modules.push((format!("{bits}/{codec}"), decoded, runs.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs.iter().map(|(id, _)| (*id, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), count);
    let mut failures = Vec::new();
    for (report, (_, expected)) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, runs)| runs))
    {
        let rust_ok = expected.as_ref().map_or_else(
            || matches!(report.rust, Verdict::Ub(_)),
            |value| report.rust == Verdict::Ok(vec![value.clone()]),
        );
        assert!(rust_ok, "unexpected reference answer: {report:?}");
        if report.comparison != Comparison::Agree {
            failures.push(report);
        }
    }
    for report in failures.iter().take(8) {
        eprintln!("SCALAR_MEMORY_MISMATCH {report:?}");
    }
    assert!(
        failures.is_empty(),
        "{}/{} scalar memory comparisons disagreed",
        failures.len(),
        reports.len()
    );
    eprintln!("SCALAR_MEMORY_PASS {} runs", reports.len());
}

#[test]
fn scalar_memory_valid_target_widths_and_codecs() {
    check_cases(valid_cases, 980);
}

#[test]
fn scalar_memory_invalid_char_images_are_ub() {
    check_cases(invalid_char_cases, 280);
}

#[test]
fn scalar_memory_uninitialized_strict_and_atomic_paths() {
    check_cases(uninitialized_cases, 180);
}

#[test]
fn scalar_memory_poison_store_transport_and_strict_refusals() {
    check_cases(poison_store_cases, 180);
}
