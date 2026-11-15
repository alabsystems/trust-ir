// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Entry pointers are constructed by the public interpreter API, without an
//! integer-to-pointer instruction that would first check target width.
use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::inst::{CastOp, ICmpOp};
use trust_ir::interpret::{InterpretValue, InterpretValueKind};
use trust_ir::value::FuncId;
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy, Debug)]
enum Action {
    Return,
    Copy,
    Retype,
    Integer(u32),
    Bitcast,
    Transmute,
    BitcastIdentity,
    TransmuteIdentity,
    Compare,
    Gep(u64),
    Store,
}

impl Action {
    fn result(self) -> Ty {
        match self {
            Self::Return
            | Self::Copy
            | Self::Retype
            | Self::BitcastIdentity
            | Self::TransmuteIdentity => Ty::Ptr,
            Self::Compare => Ty::Bool,
            _ => Ty::U128,
        }
    }
    fn expected(self, bits: u32, address: Option<u64>) -> Verdict {
        let raw = u128::from(address.unwrap_or(0));
        let limit = 1u128 << bits;
        let integer = |raw| Verdict::Ok(vec![Val::Int { width: 128, raw }]);
        let ub = || Verdict::Ub(String::new());
        match self {
            Self::Return
            | Self::Copy
            | Self::Retype
            | Self::BitcastIdentity
            | Self::TransmuteIdentity => Verdict::Ok(vec![Val::Ptr {
                null: address.is_none(),
            }]),
            Self::Integer(width) => integer(if width == 128 {
                raw
            } else {
                raw & ((1u128 << width) - 1)
            }),
            Self::Bitcast | Self::Transmute => integer(raw & (limit - 1)),
            Self::Compare => {
                if raw < limit {
                    Verdict::Ok(vec![Val::Bool(true)])
                } else {
                    ub()
                }
            }
            Self::Gep(offset) => {
                if address.is_none() || raw + u128::from(offset) >= limit {
                    ub()
                } else {
                    integer(raw + u128::from(offset))
                }
            }
            Self::Store => {
                if raw < limit {
                    integer(0)
                } else {
                    ub()
                }
            }
        }
    }
}

fn cases(bits: u32) -> (Module, Vec<(FuncId, Action)>) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("host_pointer_{bits}"), semr_target(bits));
    let word = if bits == 32 { Ty::U32 } else { Ty::U64 };
    let mut cases = Vec::new();
    for action in [
        Action::Return,
        Action::Copy,
        Action::Retype,
        Action::Integer(8),
        Action::Integer(32),
        Action::Integer(64),
        Action::Integer(128),
        Action::Bitcast,
        Action::Transmute,
        Action::BitcastIdentity,
        Action::TransmuteIdentity,
        Action::Compare,
        Action::Gep(0),
        Action::Gep(1),
        Action::Store,
    ] {
        let sig = mb.add_func_type(vec![Ty::Ptr], vec![action.result()]);
        let mut fb = mb.function(format!("{action:?}"), sig);
        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let result = match action {
            Action::Return => ptr,
            Action::Copy => fb.copy(Ty::Ptr, ptr),
            Action::Retype => {
                let ty = Ty::PtrConst(Box::new(Ty::U8));
                let value = fb.cast(CastOp::PtrToPtr, Ty::Ptr, ty.clone(), ptr);
                fb.cast(CastOp::PtrToPtr, ty, Ty::Ptr, value)
            }
            Action::Integer(width) => {
                let ty = match width {
                    8 => Ty::U8,
                    32 => Ty::U32,
                    64 => Ty::U64,
                    128 => Ty::U128,
                    _ => unreachable!(),
                };
                let value = fb.cast(CastOp::PtrToInt, Ty::Ptr, ty.clone(), ptr);
                if width == 128 {
                    value
                } else {
                    fb.cast(CastOp::ZExt, ty, Ty::U128, value)
                }
            }
            Action::Bitcast | Action::Transmute => {
                let op = if matches!(action, Action::Bitcast) {
                    CastOp::Bitcast
                } else {
                    CastOp::Transmute
                };
                let value = fb.cast(op, Ty::Ptr, word.clone(), ptr);
                fb.cast(CastOp::ZExt, word.clone(), Ty::U128, value)
            }
            Action::BitcastIdentity => fb.cast(CastOp::Bitcast, Ty::Ptr, Ty::Ptr, ptr),
            Action::TransmuteIdentity => fb.cast(CastOp::Transmute, Ty::Ptr, Ty::Ptr, ptr),
            Action::Compare => fb.icmp(ICmpOp::Eq, Ty::Ptr, ptr, ptr),
            Action::Gep(offset) => {
                let index = fb.iconst(Ty::U64, i128::from(offset));
                let value = fb.gep(Ty::U8, ptr, vec![index]);
                fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U128, value)
            }
            Action::Store => {
                let cell = fb.alloca(Ty::Ptr);
                fb.store(Ty::Ptr, cell, ptr);
                fb.iconst(Ty::U128, 0)
            }
        };
        fb.ret(vec![result]);
        cases.push((fb.build(), action));
    }
    (mb.build().expect("host pointer module"), cases)
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

#[test]
fn host_pointer_arguments_preserve_transport_and_operation_specific_observation() {
    let addresses = [
        None,
        Some(0),
        Some(1),
        Some(255),
        Some(u64::from(u32::MAX)),
        Some(1u64 << 32),
        Some((1u64 << 32) + 1),
        Some(1u64 << 63),
        Some(u64::MAX),
    ];
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, cases) = cases(bits);
        for (codec, module) in codeced(module) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            let runs = cases
                .iter()
                .flat_map(|(id, action)| {
                    addresses
                        .iter()
                        .map(move |address| (*id, *action, *address))
                })
                .collect::<Vec<_>>();
            modules.push((format!("{bits}/{codec}"), module, runs, bits));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(label, module, cases, _)| Batch {
            label: label.clone(),
            module,
            runs: cases
                .iter()
                .map(|(id, _, address)| {
                    (
                        *id,
                        vec![InterpretValue {
                            ty: Ty::Ptr,
                            kind: address.map_or(
                                InterpretValueKind::NullPtr,
                                InterpretValueKind::DanglingPtr,
                            ),
                        }],
                    )
                })
                .collect(),
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    let mut gaps = 0;
    for (report, (_, action, address, bits)) in
        reports
            .iter()
            .zip(modules.iter().flat_map(|(_, _, cases, bits)| {
                cases
                    .iter()
                    .map(move |(id, action, address)| (*id, *action, *address, *bits))
            }))
    {
        let expected = action.expected(bits, address);
        assert!(
            match (&expected, &report.rust) {
                (Verdict::Ub(_), Verdict::Ub(_)) => true,
                _ => expected == report.rust,
            },
            "reference expectation {bits}/{action:?}/{address:?}: {report:?}"
        );
        if report.comparison != Comparison::Agree {
            eprintln!("host_pointer_gap {bits}/{action:?}/{address:?}: {report:?}");
            gaps += 1;
        }
    }
    eprintln!("host_pointer_total={} gaps={gaps}", reports.len());
    assert_eq!(gaps, 0);
}

#[test]
fn host_pointer_argument_decoder_checks_u64_carriers_without_target_clamping() {
    use serde_json::json;
    use std::process::Command;
    let Oracle::Ready(exe) = oracle() else { return };
    for bits in [32, 64] {
        let (module, cases) = cases(bits);
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let controls = [
            (json!({"null_ptr": true}), Ok("null")),
            (json!({"dangling_ptr": "0"}), Ok("nonnull")),
            (json!({"dangling_ptr": "4294967296"}), Ok("nonnull")),
            (
                json!({"dangling_ptr": "18446744073709551615"}),
                Ok("nonnull"),
            ),
            (
                json!({"null_ptr": false}),
                Err("null_ptr argument must be true"),
            ),
            (
                json!({"dangling_ptr": "-1"}),
                Err("dangling_ptr argument outside u64"),
            ),
            (
                json!({"dangling_ptr": "18446744073709551616"}),
                Err("dangling_ptr argument outside u64"),
            ),
        ];
        for (index, (arg, expected)) in controls.into_iter().enumerate() {
            let request = json!({"fuel": super::FUEL, "call_depth": super::CALL_DEPTH,
                "batches": [{"module": module, "runs": [{"function": cases[0].0.index(), "args": [arg]}]}]});
            let path = std::env::temp_dir().join(format!(
                "trust-ir-host-pointer-grammar-{}-{bits}-{index}.json",
                std::process::id()
            ));
            std::fs::write(&path, serde_json::to_vec(&request).unwrap()).unwrap();
            let output = Command::new(exe).arg(&path).output().unwrap();
            std::fs::remove_file(path).unwrap();
            assert!(
                output.status.success(),
                "{bits}/{index}: {:?}",
                output.stderr
            );
            let actual: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            match expected {
                Ok(kind) => {
                    let is_null = kind == "null";
                    assert_eq!(
                        actual,
                        json!([[{"ok": {"graph": {
                            "version": 2, "nodes": [["ptr", is_null]], "roots": [0]
                        }}}]]),
                        "{bits}/{index}"
                    )
                }
                Err(message) => assert_eq!(actual, json!({"error": message}), "{bits}/{index}"),
            }
        }
    }
}

#[test]
fn host_pointer_aliasing_a_live_address_keeps_provenance_until_explicit_resolution() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info(
            format!("host_pointer_provenance_{bits}"),
            semr_target(bits),
        );
        let mut cases = Vec::new();
        for phase in 0..7 {
            let result_ty = if phase == 6 { Ty::Bool } else { Ty::U8 };
            let sig = mb.add_func_type(vec![Ty::Ptr], vec![result_ty]);
            let mut fb = mb.function(format!("phase_{phase}"), sig);
            let entry = fb.create_block();
            let ptr = fb.add_block_param(entry, Ty::Ptr);
            fb.switch_to_block(entry);
            let cell = fb.alloca(Ty::U8);
            let initial = fb.iconst(Ty::U8, 37);
            fb.store(Ty::U8, cell, initial);
            let held = match phase {
                0 | 6 => ptr,
                1 => fb.copy(Ty::Ptr, ptr),
                2 => {
                    let ty = Ty::PtrConst(Box::new(Ty::U8));
                    let held = fb.cast(CastOp::PtrToPtr, Ty::Ptr, ty.clone(), ptr);
                    fb.cast(CastOp::PtrToPtr, ty, Ty::Ptr, held)
                }
                3 => fb.cast(CastOp::Bitcast, Ty::Ptr, Ty::Ptr, ptr),
                4 => fb.cast(CastOp::Transmute, Ty::Ptr, Ty::Ptr, ptr),
                5 => {
                    let address = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, ptr);
                    fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, address)
                }
                _ => unreachable!(),
            };
            let result = if phase == 6 {
                let null = fb.null_ptr();
                fb.icmp(ICmpOp::Eq, Ty::Ptr, held, null)
            } else {
                fb.load(Ty::U8, held)
            };
            fb.ret(vec![result]);
            cases.push((fb.build(), phase));
        }
        let module = mb.build().expect("host provenance module");
        for (codec, module) in codeced(module) {
            assert!(
                trust_ir_build::validate_module(&module).is_empty(),
                "{bits}/{codec}"
            );
            modules.push((format!("{bits}/{codec}"), module, cases.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(label, module, cases)| Batch {
            label: label.clone(),
            module,
            runs: cases
                .iter()
                .map(|(id, phase)| {
                    (
                        *id,
                        vec![InterpretValue {
                            ty: Ty::Ptr,
                            kind: InterpretValueKind::DanglingPtr(if *phase == 6 {
                                0
                            } else {
                                1024
                            }),
                        }],
                    )
                })
                .collect(),
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    for (report, (_, phase)) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, cases)| cases))
    {
        match phase {
            5 => assert_eq!(
                report.rust,
                Verdict::Ok(vec![Val::Int { width: 8, raw: 37 }])
            ),
            6 => assert_eq!(report.rust, Verdict::Ok(vec![Val::Bool(true)])),
            _ => assert!(matches!(report.rust, Verdict::Ub(_))),
        }
        assert_eq!(report.comparison, Comparison::Agree, "{phase}: {report:?}");
    }
    assert_eq!(reports.len(), 70);
}
