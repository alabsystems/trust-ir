// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Valid, self-described pointer-sized entry carriers. Nominal type and the
//! signed flag are erased by the current IPC, so malformed carriers are not
//! coverage claims of this corpus.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::inst::CastOp;
use trust_ir::interpret::InterpretValue;
use trust_ir::value::FuncId;
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy, Debug)]
struct Case {
    signed: bool,
    source_bits: u32,
    value: i128,
    fits32: bool,
    fits64: bool,
}

fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for (bits, values) in [
        (
            8,
            vec![
                (0, true, true),
                (127, true, true),
                (128, true, true),
                (255, true, true),
            ],
        ),
        (
            32,
            vec![
                (0, true, true),
                (1, true, true),
                (1 << 31, true, true),
                (i128::from(u32::MAX), true, true),
            ],
        ),
        (
            64,
            vec![
                (i128::from(u32::MAX), true, true),
                (1 << 32, false, true),
                (i128::from(u64::MAX), false, true),
            ],
        ),
        (
            128,
            vec![
                (i128::from(u64::MAX), false, true),
                (i128::from(u64::MAX) + 1, false, false),
            ],
        ),
    ] {
        for (value, fits32, fits64) in values {
            cases.push(Case {
                signed: false,
                source_bits: bits,
                value,
                fits32,
                fits64,
            });
        }
    }
    for (bits, values) in [
        (
            8,
            vec![
                (-128, true, true),
                (-7, true, true),
                (0, true, true),
                (127, true, true),
            ],
        ),
        (
            32,
            vec![
                (i128::from(i32::MIN), true, true),
                (-7, true, true),
                (0, true, true),
                (i128::from(i32::MAX), true, true),
            ],
        ),
        (
            64,
            vec![
                (i128::from(i64::MIN), false, true),
                (i128::from(i32::MIN) - 1, false, true),
                (i128::from(i32::MIN), true, true),
                (-7, true, true),
                (i128::from(i32::MAX), true, true),
                (i128::from(i32::MAX) + 1, false, true),
                (i128::from(i64::MAX), false, true),
            ],
        ),
        (
            128,
            vec![
                (i128::from(i64::MIN) - 1, false, false),
                (i128::from(i64::MIN), false, true),
                (i128::from(i64::MAX), false, true),
                (i128::from(i64::MAX) + 1, false, false),
            ],
        ),
    ] {
        for (value, fits32, fits64) in values {
            cases.push(Case {
                signed: true,
                source_bits: bits,
                value,
                fits32,
                fits64,
            });
        }
    }
    assert_eq!(cases.len(), 32);
    cases
}

fn module(bits: u32) -> (Module, [FuncId; 2]) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("entry_integer_{bits}"), semr_target(bits));
    let mut functions = Vec::new();
    for signed in [false, true] {
        let ty = if signed { Ty::Isize } else { Ty::Usize };
        let wide = if signed { Ty::I128 } else { Ty::U128 };
        let sig = mb.add_func_type(vec![ty.clone()], vec![ty.clone(), wide.clone()]);
        let mut fb = mb.function(format!("entry_{signed}"), sig);
        let entry = fb.create_block();
        let input = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let copied = fb.copy(ty.clone(), input);
        let extended = fb.cast(
            if signed { CastOp::SExt } else { CastOp::ZExt },
            ty,
            wide,
            copied,
        );
        fb.ret(vec![copied, extended]);
        functions.push(fb.build());
    }
    (
        mb.build().expect("valid pointer-sized entry functions"),
        functions.try_into().unwrap(),
    )
}

fn codeced(module: Module, directory: &std::path::Path, bits: u32) -> [(&'static str, Module); 5] {
    let binary = trust_ir::binary::serialize_module(&module).unwrap();
    let text = trust_ir::format::text_checked(&module).unwrap();
    let json = serde_json::to_vec(&module).unwrap();
    let message_pack = rmp_serde::to_vec(&module).unwrap();
    for (extension, bytes) in [
        ("bin", binary.as_slice()),
        ("txt", text.as_bytes()),
        ("json", json.as_slice()),
        ("msgpack", message_pack.as_slice()),
    ] {
        std::fs::write(directory.join(format!("entry-{bits}.{extension}")), bytes).unwrap();
    }
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
fn valid_pointer_integer_entry_carriers_preserve_source_math_across_targets_and_codecs() {
    let directory = std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir().join(format!("entry-integers-{}", std::process::id()))
        })
        .join("entry-integer-arguments");
    std::fs::create_dir_all(&directory).unwrap();
    let cases = cases();
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, functions) = module(bits);
        for (codec, module) in codeced(module, &directory, bits) {
            assert!(trust_ir_build::validate_module(&module).is_empty());
            let runs = cases
                .iter()
                .map(|case| {
                    let ty = if case.signed { Ty::Isize } else { Ty::Usize };
                    (
                        functions[usize::from(case.signed)],
                        vec![InterpretValue::int_at(ty, case.value, case.source_bits).unwrap()],
                    )
                })
                .collect::<Vec<_>>();
            modules.push((format!("entry_integer_{bits}_{codec}"), module, bits, runs));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(label, module, _, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs.clone(),
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 320);
    let (groups, remainder) = reports.as_chunks::<32>();
    assert!(remainder.is_empty());
    let mut ok = 0;
    let mut type_errors = 0;
    for ((label, _, bits, _), reports) in modules.iter().zip(groups) {
        for (case, report) in cases.iter().zip(reports) {
            let fits = if *bits == 32 {
                case.fits32
            } else {
                case.fits64
            };
            if fits {
                let expected = Verdict::Ok(vec![
                    Val::Int {
                        width: *bits,
                        raw: (case.value as u128) & ((1u128 << bits) - 1),
                    },
                    Val::Int {
                        width: 128,
                        raw: case.value as u128,
                    },
                ]);
                assert_eq!(report.rust, expected, "{label}/{case:?}: {report:?}");
                assert_eq!(report.lean, expected, "{label}/{case:?}: {report:?}");
                assert_eq!(
                    report.comparison,
                    Comparison::Agree,
                    "{label}/{case:?}: {report:?}"
                );
                ok += 1;
            } else {
                assert!(
                    matches!(report.rust, Verdict::TypeError(_)),
                    "{label}/{case:?}: {report:?}"
                );
                assert!(
                    matches!(report.lean, Verdict::TypeError(_)),
                    "{label}/{case:?}: {report:?}"
                );
                // TypeError remains fail-closed in the shared comparator.
                assert!(
                    matches!(report.comparison, Comparison::Mismatch(_)),
                    "{report:?}"
                );
                type_errors += 1;
            }
        }
    }
    assert_eq!((ok, type_errors), (245, 75));
    println!(
        "entry integer carriers: 320 checked runs, 245 exact Ok, 75 paired TypeError controls; 2 targets x 5 cold codecs; source widths 8/32/64/128; no malformed nominal/signedness/raw IPC coverage claim"
    );
}
