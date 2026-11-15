// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::value::{FuncId, GlobalId};
use trust_ir::{Global, Linkage, Module, Ty};
use trust_ir_build::ModuleBuilder;

fn vector_memory_module(bits: u32) -> (Module, Vec<(FuncId, Option<Val>)>) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("vector_memory_{bits}"), semr_target(bits));
    let mut cases = Vec::new();
    for (ty, width, signed) in [
        (Ty::I8, 8, true),
        (Ty::I16, 16, true),
        (Ty::I32, 32, true),
        (Ty::I64, 64, true),
        (Ty::U8, 8, false),
        (Ty::U16, 16, false),
        (Ty::U32, 32, false),
        (Ty::U64, 64, false),
    ] {
        let literals: [i128; 4] = if signed {
            [-1, 0, 7, -128]
        } else {
            [0, 1, 127, 255]
        };
        cases.push((
            ty,
            C::Vector(literals.iter().copied().map(C::Int).collect()),
            Val::Vector(
                literals
                    .iter()
                    .map(|raw| Val::Int {
                        width,
                        raw: (*raw as u128) & ((1u128 << width) - 1),
                    })
                    .collect(),
            ),
        ));
    }
    for ty in [Ty::F16, Ty::F32, Ty::F64] {
        let literals = [1.5, -0.0, 0.1, f64::INFINITY];
        let values = literals
            .iter()
            .map(|raw| {
                if raw.is_nan() {
                    Val::Nan
                } else {
                    let rounded = match ty {
                        Ty::F16 => trust_ir::interpret::f16_bits_to_f64(
                            trust_ir::interpret::f64_to_f16_bits(*raw),
                        ),
                        Ty::F32 => *raw as f32 as f64,
                        Ty::F64 => *raw,
                        _ => unreachable!(),
                    };
                    Val::Float(rounded.to_bits())
                }
            })
            .collect();
        cases.push((
            ty,
            C::Vector(literals.into_iter().map(C::Float).collect()),
            Val::Vector(values),
        ));
    }
    cases.push((
        Ty::Bool,
        C::Vector(vec![
            C::Bool(true),
            C::Bool(false),
            C::Bool(true),
            C::Bool(false),
        ]),
        Val::Vector(vec![
            Val::Bool(true),
            Val::Bool(false),
            Val::Bool(true),
            Val::Bool(false),
        ]),
    ));
    let mut runs = Vec::new();
    for (index, (elem, constant, expected)) in cases.into_iter().enumerate() {
        let ty = Ty::Vector(Box::new(elem), 4);
        mb.add_global(Global {
            name: format!("V{index}"),
            ty: ty.clone(),
            mutable: false,
            initializer: Some(constant.clone()),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let sig = mb.add_func_type(vec![], vec![ty.clone()]);
        for global in [true, false] {
            let mut fb = mb.function(format!("v{index}_global_{global}"), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let address = if global {
                fb.global_addr(GlobalId::new(index as u32))
            } else {
                let address = fb.alloca(ty.clone());
                let value = fb.const_value(ty.clone(), constant.clone());
                fb.store(ty.clone(), address, value);
                address
            };
            let result = fb.load(ty.clone(), address);
            fb.ret(vec![result]);
            runs.push((fb.build(), Some(expected.clone())));
        }
    }
    // A logical mask has an all-ones physical image for each true lane.
    let bytes_ty = Ty::Vector(Box::new(Ty::U8), 4);
    let sig = mb.add_func_type(vec![], vec![bytes_ty.clone()]);
    let mut fb = mb.function("mask_physical_bytes", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let mask_ty = Ty::Vector(Box::new(Ty::Bool), 4);
    let address = fb.alloca(mask_ty.clone());
    let mask = fb.const_value(
        mask_ty.clone(),
        C::Vector(vec![
            C::Bool(true),
            C::Bool(false),
            C::Bool(true),
            C::Bool(false),
        ]),
    );
    fb.store(mask_ty, address, mask);
    let bytes = fb.load(bytes_ty.clone(), address);
    fb.ret(vec![bytes]);
    runs.push((
        fb.build(),
        Some(Val::Vector(
            [255, 0, 255, 0]
                .into_iter()
                .map(|raw| Val::Int { width: 8, raw })
                .collect(),
        )),
    ));
    let mut fb = mb.function("uninitialized_vector_is_ub", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let address = fb.alloca(bytes_ty.clone());
    let value = fb.load(bytes_ty, address);
    fb.ret(vec![value]);
    runs.push((fb.build(), None));
    let module = mb.build().expect("vector memory module");
    assert_eq!(runs.len(), 26);
    (module, runs)
}

#[test]
fn vector_memory_globals_stores_and_masks_agree_across_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, runs) = vector_memory_module(bits);
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
                format!("vector_memory_{bits}_{format}"),
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
    assert_eq!(reports.len(), 260);
    let mut counts = (0, 0);
    for (report, (_, value)) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, runs)| runs))
    {
        if let Some(value) = value {
            let expected = Verdict::Ok(vec![value.clone()]);
            assert_eq!(report.rust, expected, "{report:?}");
            assert_eq!(report.lean, expected, "{report:?}");
            counts.0 += 1;
        } else {
            assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
            assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
            counts.1 += 1;
        }
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
    assert_eq!(counts, (250, 10));
}

// NaN images retain the float codec's explicit payload-observation boundary.
#[test]
fn vector_memory_nan_images_keep_the_float_refusal() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb =
            ModuleBuilder::new_with_target_info(format!("vector_nan_{bits}"), semr_target(bits));
        let sig = mb.add_func_type(vec![], vec![]);
        let mut runs = Vec::new();
        for elem in [Ty::F16, Ty::F32, Ty::F64] {
            let ty = Ty::Vector(Box::new(elem.clone()), 1);
            let mut fb = mb.function(format!("nan_{elem:?}"), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let address = fb.alloca(ty.clone());
            let value = fb.const_value(ty.clone(), C::Vector(vec![C::Float(f64::NAN)]));
            fb.store(ty, address, value);
            fb.ret(vec![]);
            runs.push((fb.build(), vec![]));
        }
        let module = mb.build().expect("NaN vector image module");
        assert!(trust_ir_build::validate_module(&module).is_empty());
        modules.push((module, runs));
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(module, runs)| Batch {
            label: module.name.clone(),
            module,
            runs: runs.clone(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 6);
    for report in reports {
        assert_eq!(report.rust, Verdict::Ok(vec![]), "{report:?}");
        assert_eq!(
            report.lean,
            Verdict::Unsupported("float".into()),
            "{report:?}"
        );
    }
}
