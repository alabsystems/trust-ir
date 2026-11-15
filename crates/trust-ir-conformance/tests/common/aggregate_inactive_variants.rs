// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! An impossible variant needs a source layout, but no executable payload.
//! Byte mutations select it without constructing an invalid source constant.
//! Paired dynamic TypeError controls are kept separate from Ok/UB agreement.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant};
use trust_ir::value::{EnumId, FuncId, GlobalId, ValueId};
use trust_ir::{Global, Linkage, Module, Ty};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

#[derive(Clone)]
enum Expected {
    Value(Val),
    Ub,
    TypeError,
}

#[derive(Clone)]
struct Case {
    name: String,
    function: FuncId,
    expected: Expected,
}

fn int(width: u32, raw: u128) -> Val {
    Val::Int { width, raw }
}

fn good(raw: u128) -> Val {
    Val::Aggregate(vec![int(8, 0), int(64, raw)])
}

fn good_constant() -> C {
    C::Aggregate(vec![C::Int(0), C::Int(42)])
}

fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: name.into(),
        fields,
        field_names: vec![],
    }
}

fn definition(
    id: u32,
    name: &str,
    variants: Vec<EnumVariant>,
    layout: EnumLayoutDescriptor,
) -> EnumDef {
    let mut value = EnumDef::new(EnumId::new(id), name, variants);
    value.layout = Some(layout);
    value
}

fn direct(size: u64, align: u64, offsets: Vec<Vec<u64>>) -> EnumLayoutDescriptor {
    EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
        size,
        align,
        variant_field_offsets: offsets,
    }
}

fn slot(fb: &mut FunctionBuilder<'_>) -> ValueId {
    fb.alloca_aligned(Ty::Vector(Box::new(Ty::U8), 64), 16)
}

fn add(
    mb: &mut ModuleBuilder,
    name: impl Into<String>,
    result: Ty,
    expected: Expected,
    body: impl FnOnce(&mut FunctionBuilder<'_>) -> ValueId,
) -> Case {
    let name = name.into();
    let signature = mb.add_func_type(vec![], vec![result]);
    let mut fb = mb.function(&name, signature);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let value = body(&mut fb);
    fb.ret(vec![value]);
    Case {
        name,
        function: fb.build(),
        expected,
    }
}

fn mutate_tag(
    fb: &mut FunctionBuilder<'_>,
    ty: &Ty,
    tag: u128,
    image: &str,
    strict: bool,
) -> ValueId {
    let pointer = slot(fb);
    match image {
        "padding" => {
            let value = fb.const_value(ty.clone(), good_constant());
            fb.store(ty.clone(), pointer, value);
        }
        "full" => {
            let zero = fb.uconst(Ty::U8, 0);
            let count = fb.uconst(Ty::Usize, 16);
            fb.memset(pointer, zero, count);
        }
        "tag_only" => (),
        _ => unreachable!("fixture image mode"),
    }
    let byte = fb.uconst(Ty::U8, tag);
    fb.store(Ty::U8, pointer, byte);
    if strict {
        fb.load_volatile(ty.clone(), pointer)
    } else {
        fb.load(ty.clone(), pointer)
    }
}

fn corpus(bits: u32) -> (Module, Vec<Case>) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("inactive_never_{bits}"), semr_target(bits));
    let eid = mb.add_enum(definition(
        0,
        "HasImpossible",
        vec![
            variant("Good", vec![Ty::U64]),
            variant("Bad", vec![Ty::Never]),
        ],
        direct(16, 8, vec![vec![8], vec![8]]),
    ));
    let inhabited = mb.add_enum(definition(
        1,
        "AllInhabited",
        vec![
            variant("Good", vec![Ty::U64]),
            variant("Other", vec![Ty::U64]),
        ],
        direct(16, 8, vec![vec![8], vec![8]]),
    ));
    let mut niches = Vec::new();
    for (id, end) in [(2, 2), (3, 1)] {
        niches.push(mb.add_enum(definition(
            id,
            if end == 2 {
                "DeadInsideNiche"
            } else {
                "DeadOutsideNiche"
            },
            vec![
                variant("Live", vec![Ty::U64]),
                variant("Empty", vec![]),
                variant("Dead", vec![Ty::Never]),
            ],
            EnumLayoutDescriptor {
                encoding: EnumTagEncoding::Niche {
                    untagged_variant: 0,
                    niche_variants_start: 1,
                    niche_variants_end: end,
                    niche_start: 0,
                    niche_offset: 0,
                    niche_ty: EnumTagRepr::U64,
                },
                size: 8,
                align: 8,
                variant_field_offsets: vec![vec![0], vec![], vec![0]],
            },
        )));
    }
    let all_dead = mb.add_enum(definition(
        4,
        "AllDead",
        vec![variant("A", vec![Ty::Never]), variant("B", vec![Ty::Never])],
        direct(1, 1, vec![vec![0], vec![0]]),
    ));
    let zero_dead = mb.add_enum(definition(
        5,
        "ZeroByteDead",
        vec![variant("Dead", vec![Ty::Never])],
        EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size: 0,
            align: 1,
            variant_field_offsets: vec![vec![0]],
        },
    ));
    let nested_dead = mb.add_enum(definition(
        6,
        "NestedImpossible",
        vec![
            variant("Good", vec![Ty::U64]),
            variant("Bad", vec![Ty::Enum(all_dead)]),
        ],
        direct(16, 8, vec![vec![8], vec![8]]),
    ));
    let ty = Ty::Enum(eid);
    let element = mb.add_type(ty.clone());
    let mut cases = Vec::new();
    for strict in [false, true] {
        cases.push(add(
            &mut mb,
            format!("good_store_load_{strict}"),
            ty.clone(),
            Expected::Value(good(42)),
            |fb| {
                let pointer = slot(fb);
                let value = fb.const_value(ty.clone(), good_constant());
                if strict {
                    fb.store_volatile(ty.clone(), pointer, value);
                    fb.load_volatile(ty.clone(), pointer)
                } else {
                    fb.store(ty.clone(), pointer, value);
                    fb.load(ty.clone(), pointer)
                }
            },
        ));
    }
    for initialized in [false, true] {
        let id = GlobalId::new(u32::from(initialized));
        mb.add_global(Global {
            name: format!("global_{initialized}"),
            ty: ty.clone(),
            mutable: false,
            initializer: initialized.then(good_constant),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        cases.push(add(
            &mut mb,
            format!("good_global_{initialized}"),
            ty.clone(),
            Expected::Value(good(if initialized { 42 } else { 0 })),
            |fb| {
                let pointer = fb.global_addr(id);
                fb.load(ty.clone(), pointer)
            },
        ));
    }
    let tuple = Ty::Tuple(vec![ty.clone(), Ty::U8]);
    let array = Ty::Array(element, 2);
    for mutate in [false, true] {
        cases.push(add(
            &mut mb,
            format!("nested_tuple_dead_{mutate}"),
            tuple.clone(),
            if mutate {
                Expected::TypeError
            } else {
                Expected::Value(Val::Aggregate(vec![good(42), int(8, 7)]))
            },
            |fb| {
                let pointer = slot(fb);
                let value = fb.const_value(
                    tuple.clone(),
                    C::Aggregate(vec![good_constant(), C::Int(7)]),
                );
                fb.store(tuple.clone(), pointer, value);
                if mutate {
                    let tag = fb.uconst(Ty::U8, 1);
                    fb.store(Ty::U8, pointer, tag);
                }
                fb.load(tuple.clone(), pointer)
            },
        ));
        cases.push(add(
            &mut mb,
            format!("nested_array_dead_{mutate}"),
            array.clone(),
            if mutate {
                Expected::TypeError
            } else {
                Expected::Value(Val::Aggregate(vec![good(42), good(42)]))
            },
            |fb| {
                let pointer = slot(fb);
                let value = fb.const_value(
                    array.clone(),
                    C::Splat {
                        elem: Box::new(good_constant()),
                        len: 2,
                    },
                );
                fb.store(array.clone(), pointer, value);
                if mutate {
                    let second = fb.gep_byte_offset(pointer, 16);
                    let tag = fb.uconst(Ty::U8, 1);
                    fb.store(Ty::U8, second, tag);
                }
                fb.load(array.clone(), pointer)
            },
        ));
    }
    for strict in [false, true] {
        for image in ["padding", "full", "tag_only"] {
            cases.push(add(
                &mut mb,
                format!("selected_never_{image}_{strict}"),
                ty.clone(),
                Expected::TypeError,
                |fb| mutate_tag(fb, &ty, 1, image, strict),
            ));
        }
    }
    // This independent error has no Never field and must already be TypeError.
    let inhabited_ty = Ty::Enum(inhabited);
    for image in ["padding", "full", "tag_only"] {
        cases.push(add(
            &mut mb,
            format!("inhabited_unknown_tag_{image}"),
            inhabited_ty.clone(),
            Expected::TypeError,
            |fb| mutate_tag(fb, &inhabited_ty, 2, image, false),
        ));
    }
    for pointer in ["uninitialized_tag", "undef_pointer", "partial_pointer"] {
        cases.push(add(&mut mb, pointer, ty.clone(), Expected::Ub, |fb| {
            let address = match pointer {
                "uninitialized_tag" => slot(fb),
                "undef_pointer" => fb.undef(Ty::Ptr),
                "partial_pointer" => {
                    let cell = fb.alloca(Ty::Ptr);
                    let byte = fb.uconst(Ty::U8, 1);
                    fb.store(Ty::U8, cell, byte);
                    fb.load(Ty::Ptr, cell)
                }
                _ => unreachable!("fixture pointer mode"),
            };
            fb.load(ty.clone(), address)
        }));
    }
    for (index, niche) in niches.into_iter().enumerate() {
        let niche_ty = Ty::Enum(niche);
        cases.push(add(
            &mut mb,
            format!("niche_live_store_{index}"),
            niche_ty.clone(),
            Expected::Value(good(42)),
            |fb| {
                let pointer = slot(fb);
                let value = fb.const_value(niche_ty.clone(), good_constant());
                fb.store(niche_ty.clone(), pointer, value);
                fb.load(niche_ty.clone(), pointer)
            },
        ));
        for raw in [0, 1, 2] {
            let expected = if raw == 0 {
                Expected::Value(Val::Aggregate(vec![int(8, 1)]))
            } else if index == 0 && raw == 1 {
                Expected::TypeError
            } else {
                Expected::Value(good(raw))
            };
            cases.push(add(
                &mut mb,
                format!("niche_raw_{index}_{raw}"),
                niche_ty.clone(),
                expected,
                |fb| {
                    let pointer = slot(fb);
                    let word = fb.uconst(Ty::U64, raw);
                    fb.store(Ty::U64, pointer, word);
                    fb.load(niche_ty.clone(), pointer)
                },
            ));
        }
    }
    for raw in [0, 1, 2] {
        cases.push(add(
            &mut mb,
            format!("all_dead_tag_{raw}"),
            Ty::Enum(all_dead),
            Expected::TypeError,
            |fb| {
                let pointer = slot(fb);
                let byte = fb.uconst(Ty::U8, raw);
                fb.store(Ty::U8, pointer, byte);
                fb.load(Ty::Enum(all_dead), pointer)
            },
        ));
    }
    cases.push(add(
        &mut mb,
        "all_dead_uninitialized",
        Ty::Enum(all_dead),
        Expected::Ub,
        |fb| {
            let pointer = slot(fb);
            fb.load(Ty::Enum(all_dead), pointer)
        },
    ));
    cases.push(add(
        &mut mb,
        "zero_byte_dead",
        Ty::Enum(zero_dead),
        Expected::TypeError,
        |fb| {
            let pointer = slot(fb);
            fb.load(Ty::Enum(zero_dead), pointer)
        },
    ));
    for mutate in [false, true] {
        let outer = Ty::Enum(nested_dead);
        cases.push(add(
            &mut mb,
            format!("nested_uninhabited_enum_{mutate}"),
            outer.clone(),
            if mutate {
                Expected::TypeError
            } else {
                Expected::Value(good(42))
            },
            |fb| mutate_tag(fb, &outer, u128::from(mutate), "padding", false),
        ));
    }
    (mb.build().unwrap(), cases)
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
fn inhabited_enum_images_ignore_the_impossible_never_variant() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, cases) = corpus(bits);
        let census = cases.iter().fold([0; 3], |mut counts, case| {
            counts[match case.expected {
                Expected::Value(_) => 0,
                Expected::Ub => 1,
                Expected::TypeError => 2,
            }] += 1;
            counts
        });
        assert_eq!(census, [14, 4, 17], "{bits}: exact fixture census");
        for (codec, module) in codeced(module) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((
                format!("inactive-never/{bits}/{codec}"),
                module,
                cases.clone(),
            ));
        }
    }
    // The preserved pre-fix executable is an explicit diagnostic input. The
    // ordinary test still builds/selects the current oracle through oracle().
    let exe = if let Some(path) = std::env::var_os("TRUST_IR_AGGREGATE_ENUM_BASELINE") {
        let path = std::path::PathBuf::from(path);
        assert!(path.is_file(), "baseline executable is absent: {path:?}");
        path
    } else {
        let Oracle::Ready(exe) = oracle() else { return };
        exe.clone()
    };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, cases)| Batch {
            label: label.clone(),
            module,
            runs: cases.iter().map(|case| (case.function, vec![])).collect(),
        })
        .collect();
    let reports = differential(&exe, &batches);
    assert_eq!(reports.len(), 350, "both targets and all five carriers");
    let mut failures = Vec::new();
    let mut ok_agreement = 0;
    let mut ub_agreement = 0;
    let mut paired_type_error = 0;
    for (report, case) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, cases)| cases))
    {
        let accepted = match &case.expected {
            Expected::Value(value) => {
                assert_eq!(
                    report.rust,
                    Verdict::Ok(vec![value.clone()]),
                    "{}: {report:?}",
                    case.name
                );
                let same = report.comparison == Comparison::Agree;
                ok_agreement += usize::from(same);
                same
            }
            Expected::Ub => {
                assert!(
                    matches!(report.rust, Verdict::Ub(_)),
                    "{}: {report:?}",
                    case.name
                );
                let same = report.comparison == Comparison::Agree;
                ub_agreement += usize::from(same);
                same
            }
            Expected::TypeError => {
                assert!(
                    matches!(report.rust, Verdict::TypeError(_)),
                    "{}: {report:?}",
                    case.name
                );
                let paired = matches!(report.lean, Verdict::TypeError(_));
                paired_type_error += usize::from(paired);
                paired
            }
        };
        if !accepted {
            eprintln!("inactive_never_gap {}: {report:?}", case.name);
            failures.push(&case.name);
        }
    }
    eprintln!(
        "inactive_never_total={} ok_agreement={ok_agreement} ub_agreement={ub_agreement} paired_type_error={paired_type_error} uncovered={}",
        reports.len(),
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "{} inactive-Never image gaps",
        failures.len()
    );
}

#[test]
fn inactive_variant_marker_does_not_legalize_refined_never_layouts() {
    for bits in [32, 64] {
        let (mut module, _) = corpus(bits);
        let never = module.add_type(Ty::Never).unwrap();
        let bottom = module.intern_pred(trust_ir::Pred::Bottom).unwrap().unwrap();
        module.enums[0].variants[1].fields[0] = Ty::Refine(never, bottom);
        for (codec, module) in codeced(module) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(
                errors.iter().any(|error| matches!(
                    error,
                    trust_ir_build::ValidationError::ConstTypeMismatch { location, expected, .. }
                        if location.contains("enum.0") && expected.contains("byte alignment")
                )),
                "{bits}/{codec}: refined Never must retain the descriptor refusal: {errors:?}"
            );
        }
    }
}
