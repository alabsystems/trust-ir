// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole typed images, including producer layouts, covered bytes and source
//! function identities. Vector memory is a control, not an aggregate waiver.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::inst::CastOp;
use trust_ir::ty::{
    EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant, FieldDef, StructDef,
};
use trust_ir::value::{EnumId, FuncId, GlobalId, StructId};
use trust_ir::{Global, Linkage, Module, TupleLayoutDescriptor, Ty};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

#[test]
fn aggregate_memory_descriptor_schema_retains_source_layouts() {
    let Oracle::Ready(_) = oracle() else { return };
    let output = super::lake_run_command(
        &super::find_lake().expect("oracle found lake"),
        &super::lean_dir(),
        "TrustIrEval/DescriptorSchema.lean",
    )
    .output()
    .expect("run exact descriptor decoder controls");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    // Pin the actual subjects, not an independently maintained summary count.
    let expected = [
        "Rust",
        "C",
        "Transparent",
        "Packed1",
        "Packed2",
        "Packed4",
        "Packed0 retained for refusal",
        "Packed3 retained for refusal",
        "absent serde default",
        "direct",
        "untagged",
        "single-inhabited retained selector and rows",
        "empty nominal has no fabricated tag or layout",
        "original variant field names retained",
        "selected Never exact full query refusal",
        "wide niche",
        "negative niche refuses",
        "unknown representation refuses",
        "tuple",
        "context",
    ];
    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut actual: Vec<_> = stdout
        .lines()
        .filter_map(|line| line.strip_prefix("descriptor-schema: control PASS "))
        .collect();
    let mut expected = expected.to_vec();
    actual.sort_unstable();
    expected.sort_unstable();
    assert_eq!(
        actual, expected,
        "descriptor control roster changed: {stdout}"
    );
    assert!(
        stdout.lines().any(|line| line
            == format!(
                "descriptor-schema: {} source-field controls PASS",
                actual.len()
            )),
        "summary must count executed controls: {stdout}"
    );
}

#[derive(Clone, Debug)]
enum Expected {
    Value(Val),
    Ub,
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

fn slot(fb: &mut FunctionBuilder<'_>) -> trust_ir::ValueId {
    // Separate allocation from aggregate layout. A missing codec must fail
    // at the typed access, rather than only at an aggregate Alloca.
    fb.alloca_aligned(Ty::Vector(Box::new(Ty::U8), 64), 16)
}

fn function(
    mb: &mut ModuleBuilder,
    name: impl Into<String>,
    result: Ty,
    expected: Expected,
    body: impl FnOnce(&mut FunctionBuilder<'_>) -> trust_ir::ValueId,
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

fn roundtrip(
    mb: &mut ModuleBuilder,
    name: &str,
    ty: Ty,
    literal: C,
    expected: Val,
    strict: bool,
) -> Case {
    function(
        mb,
        format!("{name}_{strict}"),
        ty.clone(),
        Expected::Value(expected),
        |fb| {
            let pointer = slot(fb);
            let value = fb.const_value(ty.clone(), literal);
            if strict {
                fb.store_volatile(ty.clone(), pointer, value);
                fb.load_volatile(ty, pointer)
            } else {
                fb.store(ty.clone(), pointer, value);
                fb.load(ty, pointer)
            }
        },
    )
}

fn struct_def(id: u32, declared: bool) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::U8,
                offset: declared.then_some(8),
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::U64,
                offset: declared.then_some(0),
            },
        ],
        size: declared.then_some(16),
        align: declared.then_some(8),
        repr: Default::default(),
        origin: None,
    }
}

fn enumeration(id: u32, declared: bool, untagged: bool) -> EnumDef {
    let variants = if untagged {
        vec![EnumVariant {
            name: "Only".into(),
            fields: vec![Ty::U64],
            field_names: vec![],
        }]
    } else {
        vec![
            EnumVariant {
                name: "None".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Some".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            },
        ]
    };
    let mut definition = EnumDef::new(EnumId::new(id), format!("E{id}"), variants);
    if declared || untagged {
        definition.layout = Some(EnumLayoutDescriptor {
            encoding: if untagged {
                EnumTagEncoding::Untagged
            } else {
                EnumTagEncoding::Direct { tag_offset: 4 }
            },
            size: if untagged { 8 } else { 24 },
            align: 8,
            variant_field_offsets: if untagged {
                vec![vec![0]]
            } else {
                vec![vec![], vec![8]]
            },
        });
    }
    definition
}

fn cases(bits: u32) -> (Module, Vec<Case>) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("aggregate_memory_{bits}"), semr_target(bits));
    mb.add_struct(struct_def(0, false));
    mb.add_struct(struct_def(1, true));
    mb.add_enum(enumeration(0, false, false));
    mb.add_enum(enumeration(1, true, false));
    mb.add_enum(enumeration(2, false, true));
    let scalar = mb.add_type(Ty::U64);
    let tuple = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    let nested = mb.add_type(tuple.clone());
    let declared_tuple = Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U8]);
    let declared_id = mb.add_type(declared_tuple.clone());
    let values = vec![int(8, 7), int(64, 42)];
    let families = vec![
        (
            "tuple",
            tuple.clone(),
            C::Aggregate(vec![C::Int(7), C::Int(42)]),
            Val::Aggregate(values.clone()),
        ),
        (
            "tuple_declared",
            declared_tuple.clone(),
            C::Aggregate(vec![C::Int(7), C::Int(42), C::Int(9)]),
            Val::Aggregate(vec![int(8, 7), int(64, 42), int(8, 9)]),
        ),
        (
            "struct",
            Ty::Struct(StructId::new(0)),
            C::Aggregate(vec![C::Int(7), C::Int(42)]),
            Val::Aggregate(values.clone()),
        ),
        (
            "struct_declared",
            Ty::Struct(StructId::new(1)),
            C::Aggregate(vec![C::Int(7), C::Int(42)]),
            Val::Aggregate(values.clone()),
        ),
        (
            "array",
            Ty::Array(scalar, 3),
            C::Array(vec![C::Int(1), C::Int(42), C::Int(3)]),
            Val::Aggregate(vec![int(64, 1), int(64, 42), int(64, 3)]),
        ),
        (
            "array_nested",
            Ty::Array(nested, 2),
            C::Splat {
                elem: Box::new(C::Aggregate(vec![C::Int(7), C::Int(42)])),
                len: 2,
            },
            Val::Aggregate(vec![Val::Aggregate(values.clone()); 2]),
        ),
        (
            "enum_none",
            Ty::Enum(EnumId::new(0)),
            C::Aggregate(vec![C::Int(0)]),
            Val::Aggregate(vec![int(8, 0)]),
        ),
        (
            "enum_some",
            Ty::Enum(EnumId::new(0)),
            C::Aggregate(vec![C::Int(1), C::Int(42)]),
            Val::Aggregate(vec![int(8, 1), int(64, 42)]),
        ),
        (
            "enum_declared",
            Ty::Enum(EnumId::new(1)),
            C::Aggregate(vec![C::Int(1), C::Int(42)]),
            Val::Aggregate(vec![int(8, 1), int(64, 42)]),
        ),
        (
            "enum_untagged",
            Ty::Enum(EnumId::new(2)),
            C::Aggregate(vec![C::Int(0), C::Int(42)]),
            Val::Aggregate(vec![int(8, 0), int(64, 42)]),
        ),
        (
            "vector_control",
            Ty::Vector(Box::new(Ty::Bool), 5),
            C::Vector(vec![
                C::Bool(true),
                C::Bool(false),
                C::Bool(true),
                C::Bool(false),
                C::Bool(true),
            ]),
            Val::Vector(vec![
                Val::Bool(true),
                Val::Bool(false),
                Val::Bool(true),
                Val::Bool(false),
                Val::Bool(true),
            ]),
        ),
    ];
    let mut runs = Vec::new();
    for (name, ty, literal, expected) in families {
        for strict in [false, true] {
            runs.push(roundtrip(
                &mut mb,
                name,
                ty.clone(),
                literal.clone(),
                expected.clone(),
                strict,
            ));
        }
    }
    // Padding may remain missing on either plain or volatile aggregate loads.
    for strict in [false, true] {
        for write_live_field in [false, true] {
            runs.push(function(
                &mut mb,
                format!("tuple_covered_{strict}_{write_live_field}"),
                Ty::U64,
                if write_live_field {
                    Expected::Value(int(64, 42))
                } else {
                    Expected::Ub
                },
                |fb| {
                    let pointer = slot(fb);
                    let first = fb.uconst(Ty::U8, 7);
                    fb.store(Ty::U8, pointer, first);
                    if write_live_field {
                        let second_pointer = fb.gep_byte_offset(pointer, 8);
                        let second = fb.uconst(Ty::U64, 42);
                        fb.store(Ty::U64, second_pointer, second);
                    }
                    let aggregate = if strict {
                        fb.load_volatile(tuple.clone(), pointer)
                    } else {
                        fb.load(tuple.clone(), pointer)
                    };
                    fb.extract_field(Ty::U64, aggregate, 1)
                },
            ));
        }
    }
    runs.push(function(
        &mut mb,
        "tuple_store_clears_padding",
        Ty::U8,
        Expected::Ub,
        |fb| {
            let pointer = slot(fb);
            let fill = fb.uconst(Ty::U8, 255);
            let count = fb.uconst(Ty::Usize, 16);
            fb.memset(pointer, fill, count);
            let value = fb.const_value(tuple.clone(), C::Aggregate(vec![C::Int(7), C::Int(42)]));
            fb.store(tuple.clone(), pointer, value);
            let padding = fb.gep_byte_offset(pointer, 1);
            fb.load(Ty::U8, padding)
        },
    ));
    runs.push(roundtrip(
        &mut mb,
        "tuple_unwritten_lane",
        Ty::Tuple(vec![Ty::U64, Ty::U64]),
        C::Aggregate(vec![C::Uninit, C::Int(42)]),
        Val::Aggregate(vec![Val::Uninit, int(64, 42)]),
        false,
    ));
    runs.push(function(
        &mut mb,
        "tuple_unwritten_volatile_store",
        Ty::U64,
        Expected::Ub,
        |fb| {
            let pointer = slot(fb);
            let ty = Ty::Tuple(vec![Ty::U64, Ty::U64]);
            let value = fb.const_value(ty.clone(), C::Aggregate(vec![C::Uninit, C::Int(42)]));
            fb.store_volatile(ty, pointer, value);
            fb.uconst(Ty::U64, 0)
        },
    ));
    // Direct calls transport the whole typed result before its image is read.
    let signature = mb.add_func_type(vec![tuple.clone()], vec![tuple.clone()]);
    let identity = {
        let mut fb = mb.function("tuple_identity", signature);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, tuple.clone());
        fb.switch_to_block(entry);
        fb.ret(vec![value]);
        fb.build()
    };
    runs.push(function(
        &mut mb,
        "tuple_call_store_load",
        tuple.clone(),
        Expected::Value(Val::Aggregate(values)),
        |fb| {
            let value = fb.const_value(tuple.clone(), C::Aggregate(vec![C::Int(7), C::Int(42)]));
            let called = fb.call(identity, vec![value]);
            let pointer = slot(fb);
            fb.store(tuple.clone(), pointer, called);
            fb.load(tuple.clone(), pointer)
        },
    ));
    // An uncalled declaration still occupies a source code word; executable bodies
    // alone do not determine the table.
    let code_sig = mb.add_func_type(vec![], vec![Ty::U64]);
    mb.declare_function("unused_code_word", code_sig);
    let leaf = {
        let mut fb = mb.function("called_code_word", code_sig);
        let block = fb.create_block();
        fb.switch_to_block(block);
        let value = fb.uconst(Ty::U64, 42);
        fb.ret(vec![value]);
        fb.build()
    };
    runs.push(function(
        &mut mb,
        "tuple_function_identity",
        Ty::U64,
        Expected::Value(int(64, 42)),
        |fb| {
            let code_ty = Ty::Func(code_sig);
            let ty = Ty::Tuple(vec![code_ty.clone(), Ty::U8]);
            let code = fb.fn_addr(code_sig, leaf);
            let marker = fb.uconst(Ty::U8, 7);
            let value = fb.make_aggregate(ty.clone(), vec![code, marker]);
            let pointer = slot(fb);
            fb.store(ty.clone(), pointer, value);
            let value = fb.load(ty, pointer);
            let loaded_code = fb.extract_field(code_ty, value, 0);
            fb.call_indirect(loaded_code, code_sig, vec![])
        },
    ));
    let reference = Ty::Ref(Box::new(Ty::U64));
    let mut niche = EnumDef::new(
        EnumId::new(3),
        "Niche",
        vec![
            EnumVariant {
                name: "Some".into(),
                fields: vec![reference.clone()],
                field_names: vec![],
            },
            EnumVariant {
                name: "None".into(),
                fields: vec![],
                field_names: vec![],
            },
        ],
    );
    niche.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 1,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: if bits == 32 {
                EnumTagRepr::U32
            } else {
                EnumTagRepr::U64
            },
        },
        size: u64::from(bits / 8),
        align: u64::from(bits / 8),
        variant_field_offsets: vec![vec![0], vec![]],
    });
    mb.add_enum(niche);
    runs.push(function(
        &mut mb,
        "niche_live_pointer",
        Ty::U64,
        Expected::Value(int(64, 42)),
        |fb| {
            let data = fb.alloca(Ty::U64);
            let value = fb.uconst(Ty::U64, 42);
            fb.store(Ty::U64, data, value);
            let reference_value = fb.cast(CastOp::PtrToPtr, Ty::Ptr, reference.clone(), data);
            let ty = Ty::Enum(EnumId::new(3));
            let value = fb.make_enum_variant(ty.clone(), 0, vec![reference_value]);
            let pointer = slot(fb);
            fb.store(ty.clone(), pointer, value);
            let loaded = fb.load(ty, pointer);
            let reference_value = fb.extract_field(reference.clone(), loaded, 1);
            let data = fb.cast(CastOp::PtrToPtr, reference, Ty::Ptr, reference_value);
            fb.load(Ty::U64, data)
        },
    ));
    runs.push(roundtrip(
        &mut mb,
        "niche_none",
        Ty::Enum(EnumId::new(3)),
        C::Aggregate(vec![C::Int(1)]),
        Val::Aggregate(vec![int(8, 1)]),
        false,
    ));
    mb.add_global(Global {
        name: "aggregate_global".into(),
        ty: tuple.clone(),
        mutable: false,
        initializer: Some(C::Aggregate(vec![C::Int(7), C::Int(42)])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    runs.push(function(
        &mut mb,
        "tuple_global",
        tuple.clone(),
        Expected::Value(Val::Aggregate(vec![int(8, 7), int(64, 42)])),
        |fb| {
            let pointer = fb.global_addr(GlobalId::new(0));
            fb.load(tuple, pointer)
        },
    ));
    // A constructor inspects its immediate lanes, not the contents of a
    // transported aggregate lane. The Uninit originated at its permitted
    // direct Const tuple field, rather than at a nested constant spelling.
    let inner = Ty::Tuple(vec![Ty::U64, Ty::U64]);
    let nested_enum = mb.add_enum(EnumDef::new(
        EnumId::new(4),
        "CarriesTuple",
        vec![EnumVariant {
            name: "Only".into(),
            fields: vec![inner.clone()],
            field_names: vec![],
        }],
    ));
    runs.push(function(
        &mut mb,
        "enum_transports_unwritten_tuple",
        Ty::Enum(nested_enum),
        Expected::Value(Val::Aggregate(vec![
            int(8, 0),
            Val::Aggregate(vec![Val::Uninit, int(64, 42)]),
        ])),
        |fb| {
            let value = fb.const_value(inner, C::Aggregate(vec![C::Uninit, C::Int(42)]));
            fb.make_enum_variant(Ty::Enum(nested_enum), 0, vec![value])
        },
    ));
    // Non-partial Undef is UB at construction, including discarded results.
    // Vector/Func controls already have this contextual rule at the base cut.
    for (name, ty) in [
        ("tuple", Ty::Tuple(vec![Ty::U64])),
        ("struct", Ty::Struct(StructId::new(0))),
        ("array", Ty::Array(scalar, 3)),
        ("enum", Ty::Enum(EnumId::new(0))),
        ("unit", Ty::Unit),
        ("fat_pointer", Ty::FatPtr(trust_ir::ty::FatPtrKind::Str)),
        ("vector_control", Ty::Vector(Box::new(Ty::Bool), 5)),
        ("function_control", Ty::Func(code_sig)),
    ] {
        runs.push(function(
            &mut mb,
            format!("ignored_undef_{name}"),
            Ty::U64,
            Expected::Ub,
            |fb| {
                fb.undef(ty);
                fb.uconst(Ty::U64, 42)
            },
        ));
    }
    let mut module = mb.build().expect("aggregate memory source module");
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: declared_id,
        size: 16,
        align: 8,
        field_offsets: vec![8, 0, 9],
    });
    (module, runs)
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
fn aggregate_memory_source_layout_images_and_function_identities_agree() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, cases) = cases(bits);
        for (codec, module) in codeced(module) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((format!("{bits}/{codec}"), module, cases.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, cases)| Batch {
            label: label.clone(),
            module,
            runs: cases.iter().map(|case| (case.function, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    let mut failures = Vec::new();
    for (report, case) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, cases)| cases))
    {
        match &case.expected {
            Expected::Value(expected) => assert_eq!(
                report.rust,
                Verdict::Ok(vec![expected.clone()]),
                "{}: {report:?}",
                case.name
            ),
            Expected::Ub => assert!(
                matches!(report.rust, Verdict::Ub(_)),
                "{}: {report:?}",
                case.name
            ),
        }
        if report.comparison != Comparison::Agree {
            eprintln!("aggregate_memory_before {}: {report:?}", case.name);
            failures.push(&case.name);
        }
    }
    eprintln!(
        "aggregate_memory_total={} agreement={} uncovered={}",
        reports.len(),
        reports.len() - failures.len(),
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "{} aggregate memory runs did not agree",
        failures.len()
    );
}

// The record belongs to the allocation, not to the byte image. These controls
// distinguish padding, unwritten lanes, writes that clip the record, and a
// copied image that deliberately carries no unwritten-lane record.
fn coverage_cases(bits: u32) -> (Module, Vec<Case>) {
    use trust_ir::inst::Ordering;
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("aggregate_coverage_{bits}"),
        semr_target(bits),
    );
    let ty = Ty::Tuple(vec![Ty::U64, Ty::U64]);
    let unwritten = Val::Aggregate(vec![Val::Uninit, int(64, 42)]);
    let mut runs = Vec::new();
    for (label, action) in [
        ("unchanged", 0),
        ("volatile_load", 1),
        ("whole_lane_write", 2),
        ("clip_first_byte", 3),
        ("clip_last_byte", 4),
        ("copy_loses_record", 5),
        ("partial_copy_clips_record", 6),
        ("zero_copy_preserves_record", 7),
        ("zero_fill_preserves_record", 8),
    ] {
        let expected = match action {
            2 => Expected::Value(Val::Aggregate(vec![int(64, 7), int(64, 42)])),
            3..=6 => Expected::Ub,
            _ => Expected::Value(unwritten.clone()),
        };
        runs.push(function(
            &mut mb,
            format!("unwritten_{label}"),
            ty.clone(),
            expected,
            |fb| {
                let pointer = slot(fb);
                let value = fb.const_value(ty.clone(), C::Aggregate(vec![C::Uninit, C::Int(42)]));
                fb.store(ty.clone(), pointer, value);
                let loaded_from = match action {
                    2 => {
                        let value = fb.uconst(Ty::U64, 7);
                        fb.store(Ty::U64, pointer, value);
                        pointer
                    }
                    3 | 4 => {
                        let address = if action == 3 {
                            pointer
                        } else {
                            fb.gep_byte_offset(pointer, 7)
                        };
                        let value = fb.uconst(Ty::U8, 7);
                        fb.store(Ty::U8, address, value);
                        pointer
                    }
                    5 => {
                        let destination = slot(fb);
                        let count = fb.uconst(Ty::Usize, 16);
                        fb.memcopy(destination, pointer, count, false);
                        destination
                    }
                    6 => {
                        let source = slot(fb);
                        let destination = fb.gep_byte_offset(pointer, 3);
                        let count = fb.uconst(Ty::Usize, 1);
                        fb.memcopy(destination, source, count, false);
                        pointer
                    }
                    7 => {
                        let source = slot(fb);
                        let count = fb.uconst(Ty::Usize, 0);
                        fb.memcopy(pointer, source, count, false);
                        pointer
                    }
                    8 => {
                        let value = fb.uconst(Ty::U8, 7);
                        let count = fb.uconst(Ty::Usize, 0);
                        fb.memset(pointer, value, count);
                        pointer
                    }
                    _ => pointer,
                };
                if action == 1 {
                    fb.load_volatile(ty.clone(), loaded_from)
                } else {
                    fb.load(ty.clone(), loaded_from)
                }
            },
        ));
    }
    let nested = Ty::Tuple(vec![ty.clone(), Ty::U8]);
    runs.push(function(
        &mut mb,
        "unwritten_nested_tuple",
        nested.clone(),
        Expected::Value(Val::Aggregate(vec![unwritten, int(8, 7)])),
        |fb| {
            let pointer = slot(fb);
            let inner = fb.const_value(ty.clone(), C::Aggregate(vec![C::Uninit, C::Int(42)]));
            let marker = fb.uconst(Ty::U8, 7);
            let value = fb.make_aggregate(nested.clone(), vec![inner, marker]);
            fb.store(nested.clone(), pointer, value);
            fb.load(nested.clone(), pointer)
        },
    ));
    let padded = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    for observe_padding in [false, true] {
        runs.push(function(
            &mut mb,
            format!("store_padding_{observe_padding}"),
            if observe_padding {
                Ty::U8
            } else {
                padded.clone()
            },
            if observe_padding {
                Expected::Ub
            } else {
                Expected::Value(Val::Aggregate(vec![int(8, 7), int(64, 42)]))
            },
            |fb| {
                let pointer = slot(fb);
                let fill = fb.uconst(Ty::U8, 255);
                let count = fb.uconst(Ty::Usize, 16);
                fb.memset(pointer, fill, count);
                let value =
                    fb.const_value(padded.clone(), C::Aggregate(vec![C::Int(7), C::Int(42)]));
                fb.store(padded.clone(), pointer, value);
                if observe_padding {
                    let padding = fb.gep_byte_offset(pointer, 1);
                    fb.load_volatile(Ty::U8, padding)
                } else {
                    fb.load_volatile(padded.clone(), pointer)
                }
            },
        ));
    }
    mb.add_enum(enumeration(0, false, false));
    for observe_inactive in [false, true] {
        runs.push(function(
            &mut mb,
            format!("enum_inactive_{observe_inactive}"),
            if observe_inactive {
                Ty::U64
            } else {
                Ty::Enum(EnumId::new(0))
            },
            if observe_inactive {
                Expected::Ub
            } else {
                Expected::Value(Val::Aggregate(vec![int(8, 0)]))
            },
            |fb| {
                let pointer = slot(fb);
                let value = fb.const_value(Ty::Enum(EnumId::new(0)), C::Aggregate(vec![C::Int(0)]));
                fb.store(Ty::Enum(EnumId::new(0)), pointer, value);
                if observe_inactive {
                    let inactive = fb.gep_byte_offset(pointer, 8);
                    fb.load_volatile(Ty::U64, inactive)
                } else {
                    fb.load_volatile(Ty::Enum(EnumId::new(0)), pointer)
                }
            },
        ));
    }
    runs.push(function(
        &mut mb,
        "atomic_load_covered_fields",
        padded.clone(),
        Expected::Value(Val::Aggregate(vec![int(8, 7), int(64, 42)])),
        |fb| {
            let pointer = slot(fb);
            let first = fb.uconst(Ty::U8, 7);
            fb.store(Ty::U8, pointer, first);
            let second_pointer = fb.gep_byte_offset(pointer, 8);
            let second = fb.uconst(Ty::U64, 42);
            fb.store(Ty::U64, second_pointer, second);
            fb.atomic_load(padded.clone(), pointer, Ordering::SeqCst)
        },
    ));
    runs.push(function(
        &mut mb,
        "atomic_store_clears_padding",
        Ty::U8,
        Expected::Ub,
        |fb| {
            let pointer = slot(fb);
            let fill = fb.uconst(Ty::U8, 255);
            let count = fb.uconst(Ty::Usize, 16);
            fb.memset(pointer, fill, count);
            let value = fb.const_value(padded.clone(), C::Aggregate(vec![C::Int(7), C::Int(42)]));
            fb.atomic_store(padded.clone(), pointer, value, Ordering::SeqCst);
            let padding = fb.gep_byte_offset(pointer, 1);
            fb.load_volatile(Ty::U8, padding)
        },
    ));
    for equal in [false, true] {
        runs.push(function(
            &mut mb,
            format!("cmpxchg_tuple_{equal}"),
            Ty::U64,
            Expected::Value(int(64, if equal { 99 } else { 42 })),
            |fb| {
                let pointer = slot(fb);
                let current =
                    fb.const_value(padded.clone(), C::Aggregate(vec![C::Int(7), C::Int(42)]));
                fb.store(padded.clone(), pointer, current);
                let expected = fb.const_value(
                    padded.clone(),
                    C::Aggregate(vec![C::Int(7), C::Int(if equal { 42 } else { 41 })]),
                );
                let desired =
                    fb.const_value(padded.clone(), C::Aggregate(vec![C::Int(9), C::Int(99)]));
                let _ = fb.cmpxchg(
                    padded.clone(),
                    pointer,
                    expected,
                    desired,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                );
                let loaded = fb.load(padded.clone(), pointer);
                fb.extract_field(Ty::U64, loaded, 1)
            },
        ));
    }
    for initialized in [false, true] {
        let global = GlobalId::new(u32::from(initialized));
        mb.add_global(Global {
            name: format!("global_padding_{initialized}"),
            ty: padded.clone(),
            mutable: false,
            initializer: initialized.then_some(C::Aggregate(vec![C::Int(7), C::Int(42)])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        runs.push(function(
            &mut mb,
            format!("global_padding_defined_{initialized}"),
            Ty::U8,
            Expected::Value(int(8, 0)),
            |fb| {
                let pointer = fb.global_addr(global);
                let padding = fb.gep_byte_offset(pointer, 1);
                fb.load_volatile(Ty::U8, padding)
            },
        ));
    }
    (mb.build().unwrap(), runs)
}

#[test]
fn aggregate_memory_covered_bytes_and_unwritten_records_agree() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, cases) = coverage_cases(bits);
        for (codec, module) in codeced(module) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((format!("coverage/{bits}/{codec}"), module, cases.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, cases)| Batch {
            label: label.clone(),
            module,
            runs: cases.iter().map(|case| (case.function, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    let mut failures = Vec::new();
    for (report, case) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, cases)| cases))
    {
        match &case.expected {
            Expected::Value(expected) => assert_eq!(
                report.rust,
                Verdict::Ok(vec![expected.clone()]),
                "{}: {report:?}",
                case.name
            ),
            Expected::Ub => assert!(
                matches!(report.rust, Verdict::Ub(_)),
                "{}: {report:?}",
                case.name
            ),
        }
        if report.comparison != Comparison::Agree {
            eprintln!("aggregate_coverage_before {}: {report:?}", case.name);
            failures.push(&case.name);
        }
    }
    eprintln!(
        "aggregate_coverage_total={} agreement={} uncovered={}",
        reports.len(),
        reports.len() - failures.len(),
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "{} aggregate coverage runs did not agree",
        failures.len()
    );
}

fn seqmap_cases(bits: u32) -> (Module, Vec<Case>) {
    use trust_ir::Inst;
    use trust_ir::ty::ClosureTy;
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("aggregate_seqmap_{bits}"), semr_target(bits));
    let tuple = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    let scalar_id = mb.add_type(Ty::U64);
    let array = Ty::Array(scalar_id, 3);
    mb.add_enum(enumeration(0, false, false));
    let callable = mb.add_func_type(vec![], vec![]);
    let closure = mb.add_closure_type(ClosureTy {
        func: callable,
        captures: vec![],
    });
    let mut roots = Vec::new();
    let mut maps = Vec::new();
    let tuple_constants = [
        C::Aggregate(vec![C::Int(7), C::Int(42)]),
        C::Aggregate(vec![C::Int(9), C::Int(99)]),
        C::Aggregate(vec![C::Int(1), C::Int(2)]),
    ];
    let tuple_values = [
        Val::Aggregate(vec![int(8, 7), int(64, 42)]),
        Val::Aggregate(vec![int(8, 9), int(64, 99)]),
        Val::Aggregate(vec![int(8, 1), int(64, 2)]),
    ];
    let mut specifications = Vec::new();
    for count in [0, 1, 3] {
        specifications.push((
            format!("tuple_identity_{count}"),
            tuple.clone(),
            tuple_constants[..count].to_vec(),
            Expected::Value(Val::Sequence(tuple_values[..count].to_vec())),
            0,
            false,
        ));
    }
    specifications.push((
        "tuple_replace".into(),
        tuple.clone(),
        tuple_constants[..2].to_vec(),
        Expected::Value(Val::Sequence(vec![
            Val::Aggregate(vec![
                int(8, 9),
                int(64, 99)
            ]);
            2
        ])),
        1,
        false,
    ));
    specifications.push((
        "tuple_unwritten".into(),
        tuple.clone(),
        tuple_constants[..1].to_vec(),
        Expected::Value(Val::Sequence(vec![Val::Aggregate(vec![
            Val::Uninit,
            int(64, 42),
        ])])),
        2,
        false,
    ));
    specifications.push((
        "tuple_clipped_unwritten".into(),
        tuple.clone(),
        tuple_constants[..1].to_vec(),
        Expected::Ub,
        3,
        false,
    ));
    specifications.push((
        "tuple_unexplained_hole".into(),
        tuple.clone(),
        tuple_constants[..1].to_vec(),
        Expected::Ub,
        4,
        false,
    ));
    specifications.push((
        "array_identity".into(),
        array.clone(),
        vec![
            C::Array(vec![C::Int(1), C::Int(2), C::Int(3)]),
            C::Array(vec![C::Int(4), C::Int(5), C::Int(6)]),
        ],
        Expected::Value(Val::Sequence(vec![
            Val::Aggregate(vec![int(64, 1), int(64, 2), int(64, 3)]),
            Val::Aggregate(vec![int(64, 4), int(64, 5), int(64, 6)]),
        ])),
        0,
        false,
    ));
    specifications.push((
        "enum_identity".into(),
        Ty::Enum(EnumId::new(0)),
        vec![
            C::Aggregate(vec![C::Int(0)]),
            C::Aggregate(vec![C::Int(1), C::Int(42)]),
        ],
        Expected::Value(Val::Sequence(vec![
            Val::Aggregate(vec![int(8, 0)]),
            Val::Aggregate(vec![int(8, 1), int(64, 42)]),
        ])),
        0,
        false,
    ));
    specifications.push((
        "closure_empty_no_layout".into(),
        Ty::Closure(closure),
        vec![],
        Expected::Value(Val::Sequence(vec![])),
        0,
        false,
    ));
    specifications.push((
        "declared_tuple_empty_no_call".into(),
        tuple.clone(),
        vec![],
        Expected::Value(Val::Sequence(vec![])),
        0,
        true,
    ));
    for (name, element, constants, expected, mode, declaration) in specifications {
        let element_id = mb.add_type(element.clone());
        let sequence = Ty::Sequence(element_id);
        let signature = mb.add_func_type(vec![Ty::RefMut(Box::new(element.clone()))], vec![]);
        let fwd = if declaration {
            mb.declare_function(format!("{name}_forward"), signature)
        } else {
            let mut fb = mb.function(format!("{name}_forward"), signature);
            let block = fb.create_block();
            let pointer = fb.add_block_param(block, Ty::RefMut(Box::new(element.clone())));
            fb.switch_to_block(block);
            match mode {
                1 => {
                    let value =
                        fb.const_value(element.clone(), C::Aggregate(vec![C::Int(9), C::Int(99)]));
                    fb.store(element.clone(), pointer, value);
                }
                2 => {
                    let value =
                        fb.const_value(element.clone(), C::Aggregate(vec![C::Uninit, C::Int(42)]));
                    fb.store(element.clone(), pointer, value);
                }
                3 => {
                    let value =
                        fb.const_value(element.clone(), C::Aggregate(vec![C::Int(7), C::Uninit]));
                    fb.store(element.clone(), pointer, value);
                    let address = fb.gep_byte_offset(pointer, 11);
                    let byte = fb.uconst(Ty::U8, 1);
                    fb.store(Ty::U8, address, byte);
                }
                4 => {
                    let address = fb.gep_byte_offset(pointer, 8);
                    let poison = fb.undef(Ty::U64);
                    fb.store(Ty::U64, address, poison);
                }
                _ => (),
            }
            fb.ret(vec![]);
            fb.build()
        };
        let root = function(
            &mut mb,
            format!("seqmap_{name}"),
            sequence.clone(),
            expected,
            |fb| {
                let value = fb.const_value(sequence.clone(), C::Sequence(constants));
                fb.copy(sequence.clone(), value)
            },
        );
        maps.push((root.function, fwd));
        roots.push(root);
    }
    let mut module = mb.build().unwrap();
    for (root, fwd) in maps {
        let function = module.function_by_id_mut(root).unwrap();
        let mut replaced = 0;
        for node in &mut function.blocks[0].body {
            if let Inst::Copy { ty, operand } = &node.inst {
                node.inst = Inst::SeqMap {
                    ty: ty.clone(),
                    seq: *operand,
                    fwd,
                };
                replaced += 1;
            }
        }
        assert_eq!(replaced, 1, "preserve the real source result destination");
    }
    (module, roots)
}

#[test]
fn aggregate_memory_seqmap_uses_typed_images_and_empty_map_headers() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, cases) = seqmap_cases(bits);
        for (codec, module) in codeced(module) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((format!("seqmap/{bits}/{codec}"), module, cases.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, cases)| Batch {
            label: label.clone(),
            module,
            runs: cases.iter().map(|case| (case.function, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    let mut failures = Vec::new();
    for (report, case) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, cases)| cases))
    {
        match &case.expected {
            Expected::Value(expected) => assert_eq!(
                report.rust,
                Verdict::Ok(vec![expected.clone()]),
                "{}: {report:?}",
                case.name
            ),
            Expected::Ub => assert!(
                matches!(report.rust, Verdict::Ub(_)),
                "{}: {report:?}",
                case.name
            ),
        }
        if report.comparison != Comparison::Agree {
            eprintln!("aggregate_seqmap_before {}: {report:?}", case.name);
            failures.push(&case.name);
        }
    }
    eprintln!(
        "aggregate_seqmap_total={} agreement={} uncovered={}",
        reports.len(),
        reports.len() - failures.len(),
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "{} aggregate SeqMap runs did not agree",
        failures.len()
    );
}

fn physical_cases(bits: u32) -> (Module, Vec<Case>) {
    use trust_ir::ty::{ClosureTy, StructRepr};
    use trust_ir::{BinOp, ClosureLayoutDescriptor};
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("aggregate_physical_boundaries_{bits}"),
        semr_target(bits),
    );
    let packed = mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Packed9".into(),
        fields: vec![
            FieldDef {
                name: "tag".into(),
                ty: Ty::U8,
                offset: Some(0),
            },
            FieldDef {
                name: "word".into(),
                ty: Ty::U64,
                offset: Some(1),
            },
        ],
        size: Some(9),
        align: Some(1),
        repr: StructRepr::Packed(1),
        origin: None,
    });
    let transparent = mb.add_struct(StructDef {
        id: StructId::new(1),
        name: "Transparent".into(),
        fields: vec![
            FieldDef {
                name: "marker".into(),
                ty: Ty::Unit,
                offset: Some(0),
            },
            FieldDef {
                name: "word".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
        ],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::Transparent,
        origin: None,
    });
    let mut roots = Vec::new();
    for strict in [false, true] {
        roots.push(roundtrip(
            &mut mb,
            "physical_packed",
            Ty::Struct(packed),
            C::Aggregate(vec![C::Int(7), C::Int(42)]),
            Val::Aggregate(vec![int(8, 7), int(64, 42)]),
            strict,
        ));
        roots.push(roundtrip(
            &mut mb,
            "physical_transparent",
            Ty::Struct(transparent),
            C::Aggregate(vec![C::PhantomData, C::Int(42)]),
            Val::Aggregate(vec![Val::Aggregate(vec![]), int(64, 42)]),
            strict,
        ));
    }
    roots.push(function(
        &mut mb,
        "packed_source_offset_one",
        Ty::U64,
        Expected::Value(int(64, 42)),
        |fb| {
            let pointer = slot(fb);
            let ty = Ty::Struct(packed);
            let value = fb.const_value(ty.clone(), C::Aggregate(vec![C::Int(7), C::Int(42)]));
            fb.store(ty, pointer, value);
            let word = fb.gep_byte_offset(pointer, 1);
            fb.load_aligned(Ty::U64, word, 1)
        },
    ));
    // A raw Char leaf is transport inside a typed aggregate. Only a true
    // top-level Char binding applies Unicode validity; no recursive policy.
    let char_tuple = Ty::Tuple(vec![Ty::Char, Ty::U8]);
    for inspect in [false, true] {
        roots.push(function(
            &mut mb,
            format!("nested_raw_char_{inspect}"),
            if inspect {
                Ty::Char
            } else {
                char_tuple.clone()
            },
            if inspect {
                Expected::Ub
            } else {
                Expected::Value(Val::Aggregate(vec![int(32, 0xd800), int(8, 7)]))
            },
            |fb| {
                let pointer = slot(fb);
                let raw = fb.uconst(Ty::U32, 0xd800);
                fb.store(Ty::U32, pointer, raw);
                let marker_pointer = fb.gep_byte_offset(pointer, 4);
                let marker = fb.uconst(Ty::U8, 7);
                fb.store(Ty::U8, marker_pointer, marker);
                let value = fb.load(char_tuple.clone(), pointer);
                if inspect {
                    fb.extract_field(Ty::Char, value, 0)
                } else {
                    value
                }
            },
        ));
    }
    roots.push(roundtrip(
        &mut mb,
        "zero_sized_unwritten_field",
        Ty::Tuple(vec![Ty::Unit, Ty::U64]),
        C::Aggregate(vec![C::Uninit, C::Int(42)]),
        Val::Aggregate(vec![Val::Aggregate(vec![]), int(64, 42)]),
        false,
    ));
    // This tuple has an authoritative layout but no admitted Closure byte
    // image. Allocation, pointer stride and BSS must not demand that codec.
    let closure_sig = mb.add_func_type(vec![], vec![]);
    let closure = mb.add_closure_type(ClosureTy {
        func: closure_sig,
        captures: vec![Ty::U64],
    });
    let declared_tuple = Ty::Tuple(vec![Ty::Closure(closure), Ty::U8]);
    let tuple_id = mb.add_type(declared_tuple.clone());
    roots.push(function(
        &mut mb,
        "layout_only_closure_tuple_stride",
        Ty::U64,
        Expected::Value(int(64, 16)),
        |fb| {
            let base = fb.alloca(declared_tuple.clone());
            let one = fb.uconst(Ty::U64, 1);
            let end = fb.gep(declared_tuple.clone(), base, vec![one]);
            let a = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, base);
            let b = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, end);
            fb.binop(BinOp::Sub, Ty::U64, b, a)
        },
    ));
    mb.add_global(Global {
        name: "layout_only_bss".into(),
        ty: declared_tuple,
        mutable: false,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    roots.push(function(
        &mut mb,
        "layout_only_closure_tuple_bss",
        Ty::U8,
        Expected::Value(int(8, 0)),
        |fb| {
            let pointer = fb.global_addr(GlobalId::new(0));
            let marker = fb.gep_byte_offset(pointer, 8);
            fb.load(Ty::U8, marker)
        },
    ));
    let mut module = mb.build().unwrap();
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure,
        size: 8,
        align: 8,
        capture_offsets: vec![0],
    });
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: tuple_id,
        size: 16,
        align: 8,
        field_offsets: vec![0, 8],
    });
    (module, roots)
}

#[test]
fn aggregate_memory_physical_layout_and_leaf_boundaries_agree() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, cases) = physical_cases(bits);
        for (codec, module) in codeced(module) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((format!("physical/{bits}/{codec}"), module, cases.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, cases)| Batch {
            label: label.clone(),
            module,
            runs: cases.iter().map(|case| (case.function, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    let mut failures = Vec::new();
    for (report, case) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, cases)| cases))
    {
        match &case.expected {
            Expected::Value(expected) => assert_eq!(
                report.rust,
                Verdict::Ok(vec![expected.clone()]),
                "{}: {report:?}",
                case.name
            ),
            Expected::Ub => assert!(
                matches!(report.rust, Verdict::Ub(_)),
                "{}: {report:?}",
                case.name
            ),
        }
        if report.comparison != Comparison::Agree {
            eprintln!("aggregate_physical_gap {}: {report:?}", case.name);
            failures.push(&case.name);
        }
    }
    eprintln!(
        "aggregate_physical_total={} agreement={} uncovered={}",
        reports.len(),
        reports.len() - failures.len(),
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "{} aggregate physical-boundary gaps",
        failures.len()
    );
}

#[test]
fn aggregate_memory_poison_pointer_operands_are_inspection_ub() {
    use trust_ir::inst::Ordering;
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info(
            format!("poison_pointer_memory_{bits}"),
            semr_target(bits),
        );
        let mut cases = Vec::new();
        for partial in [false, true] {
            for operation in 0..9 {
                cases.push(function(
                    &mut mb,
                    format!("poison_pointer_memory_{partial}_{operation}"),
                    Ty::U64,
                    Expected::Ub,
                    |fb| {
                        let pointer = if partial {
                            let slot = fb.alloca(Ty::Ptr);
                            fb.load(Ty::Ptr, slot)
                        } else {
                            fb.undef(Ty::Ptr)
                        };
                        match operation {
                            0 => {
                                fb.load(Ty::U64, pointer);
                            }
                            1 => {
                                fb.atomic_load(Ty::U64, pointer, Ordering::SeqCst);
                            }
                            2 => {
                                fb.load(Ty::Tuple(vec![Ty::U64]), pointer);
                            }
                            3 => {
                                let value = fb.uconst(Ty::U64, 42);
                                fb.store(Ty::U64, pointer, value);
                            }
                            4 => {
                                let fill = fb.uconst(Ty::U8, 7);
                                let count = fb.uconst(Ty::Usize, 1);
                                fb.memset(pointer, fill, count);
                            }
                            5 => {
                                let destination = slot(fb);
                                let count = fb.uconst(Ty::Usize, 1);
                                fb.memcopy(destination, pointer, count, false);
                            }
                            6 => {
                                let value = fb.uconst(Ty::U64, 42);
                                fb.atomic_store(Ty::U64, pointer, value, Ordering::SeqCst);
                            }
                            7 => {
                                let value = fb.uconst(Ty::U64, 42);
                                fb.atomic_rmw(
                                    trust_ir::inst::AtomicRMWOp::Add,
                                    Ty::U64,
                                    pointer,
                                    value,
                                    Ordering::SeqCst,
                                );
                            }
                            8 => {
                                let expected = fb.uconst(Ty::U64, 42);
                                let desired = fb.uconst(Ty::U64, 43);
                                fb.cmpxchg(
                                    Ty::U64,
                                    pointer,
                                    expected,
                                    desired,
                                    Ordering::SeqCst,
                                    Ordering::SeqCst,
                                );
                            }
                            _ => unreachable!(),
                        }
                        fb.uconst(Ty::U64, 7)
                    },
                ));
            }
        }
        for (codec, module) in codeced(mb.build().unwrap()) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((
                format!("poison-pointer/{bits}/{codec}"),
                module,
                cases.clone(),
            ));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, cases)| Batch {
            label: label.clone(),
            module,
            runs: cases.iter().map(|case| (case.function, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    let mut failures = Vec::new();
    for (report, case) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, cases)| cases))
    {
        assert!(
            matches!(report.rust, Verdict::Ub(_)),
            "{}: {report:?}",
            case.name
        );
        if report.comparison != Comparison::Agree {
            eprintln!("poison_pointer_gap {}: {report:?}", case.name);
            failures.push(&case.name);
        }
    }
    eprintln!(
        "poison_pointer_total={} agreement={} uncovered={}",
        reports.len(),
        reports.len() - failures.len(),
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "{} poison-pointer memory gaps",
        failures.len()
    );
}
