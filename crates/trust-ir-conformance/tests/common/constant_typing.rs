// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::ty::{
    ClosureTy, EnumDef, EnumTagRepr, EnumVariant, FatPtrKind, FieldDef, RecordDef, SetRepr,
    StructDef,
};
use trust_ir::value::{EnumId, FuncId, RecordId, StructId};
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

struct TypeCase {
    name: String,
    ty: Ty,
    accepts: &'static [&'static str],
}
#[derive(Clone)]
struct Run {
    func: FuncId,
    label: String,
    expected: Verdict,
}

fn definitions(bits: u32) -> (ModuleBuilder, Vec<TypeCase>, Vec<(&'static str, C)>) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("constant_typing_{bits}"), semr_target(bits));
    let byte = mb.add_type(Ty::U8);
    let i8_id = mb.add_type(Ty::I8);
    let void = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("function_item", void);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    let function = fb.build();
    let physical = mb.add_func_type(vec![Ty::I8, Ty::Bool], vec![]);
    let mut fb = mb.function("closure_target", physical);
    let entry = fb.create_block();
    fb.add_block_param(entry, Ty::I8);
    fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    let closure_target = fb.build();
    let cid = mb.add_closure_type(ClosureTy {
        func: void,
        captures: vec![Ty::I8, Ty::Bool],
    });
    let fields = vec![
        FieldDef {
            name: "a".into(),
            ty: Ty::I8,
            offset: None,
        },
        FieldDef {
            name: "b".into(),
            ty: Ty::Bool,
            offset: None,
        },
    ];
    let sid = mb.add_struct(StructDef {
        id: StructId::new(8),
        name: "S".into(),
        fields: fields.clone(),
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    let rid = mb.add_record(RecordDef {
        id: RecordId::new(8),
        name: "R".into(),
        fields,
    });
    let pointer_struct = mb.add_struct(StructDef {
        id: StructId::new(9),
        name: "P".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::Ptr,
                offset: None,
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::Bool,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    let eid = mb.add_enum(
        EnumDef::new(
            EnumId::new(8),
            "E",
            vec![EnumVariant {
                name: "V".into(),
                fields: vec![Ty::I8, Ty::Bool],
                field_names: vec![],
            }],
        )
        .with_repr(EnumTagRepr::I8)
        .with_discriminants(vec![Some(3)]),
    );
    let mut types = Vec::new();
    for ty in [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
    ] {
        types.push(TypeCase {
            name: format!("{ty:?}"),
            ty,
            accepts: &["int", "zero"],
        });
    }
    types.push(TypeCase {
        name: "U128".into(),
        ty: Ty::U128,
        accepts: &["int", "zero", "u128"],
    });
    for ty in [Ty::F16, Ty::F32, Ty::F64] {
        types.push(TypeCase {
            name: format!("{ty:?}"),
            ty,
            accepts: &["float"],
        });
    }
    for (name, ty, accepts) in [
        ("Bool", Ty::Bool, &["bool"][..]),
        ("Ptr", Ty::Ptr, &["zero"][..]),
        ("Unit", Ty::Unit, &["phantom"][..]),
        ("Never", Ty::Never, &[][..]),
        ("Ref", Ty::Ref(Box::new(Ty::U8)), &[][..]),
        ("RefMut", Ty::RefMut(Box::new(Ty::U8)), &[][..]),
        ("PtrConst", Ty::PtrConst(Box::new(Ty::U8)), &[][..]),
        ("PtrMut", Ty::PtrMut(Box::new(Ty::U8)), &[][..]),
        ("Rc", Ty::Rc(Box::new(Ty::U8)), &[][..]),
        (
            "Tuple",
            Ty::Tuple(vec![Ty::I8, Ty::Bool]),
            &["fields", "pointer_fields", "unwritten_fields"][..],
        ),
        (
            "TuplePtr",
            Ty::Tuple(vec![Ty::Ptr, Ty::Bool]),
            &["pointer_fields", "unwritten_fields"][..],
        ),
        (
            "StructPtr",
            Ty::Struct(pointer_struct),
            &["pointer_fields", "unwritten_fields"][..],
        ),
        ("EmptyTuple", Ty::Tuple(vec![]), &["empty_aggregate"][..]),
        (
            "Struct",
            Ty::Struct(sid),
            &["fields", "pointer_fields", "unwritten_fields"][..],
        ),
        ("Enum", Ty::Enum(eid), &["enum_fields"][..]),
        (
            "Record",
            Ty::Record(rid),
            &["record", "fields", "pointer_fields"][..],
        ),
        (
            "ArrayI8",
            Ty::Array(i8_id, 2),
            &["array", "pos_array", "splat", "null_pair"][..],
        ),
        (
            "ArrayU8",
            Ty::Array(byte, 2),
            &["array", "pos_array", "splat", "bytes", "null_pair"][..],
        ),
        (
            "EmptyArrayU8",
            Ty::Array(byte, 0),
            &["empty_array", "empty_aggregate", "empty_bytes"][..],
        ),
        ("Sequence", Ty::Sequence(i8_id), &["sequence"][..]),
        ("Set", Ty::Set(i8_id, SetRepr::Boxed), &["set"][..]),
        ("Closure", Ty::Closure(cid), &["closure"][..]),
        ("Function", Ty::Func(void), &["function"][..]),
        (
            "VectorI8",
            Ty::Vector(Box::new(Ty::I8), 2),
            &["vector_int", "vector_zero"][..],
        ),
        (
            "VectorBool",
            Ty::Vector(Box::new(Ty::Bool), 2),
            &["vector_bool"][..],
        ),
        (
            "VectorF32",
            Ty::Vector(Box::new(Ty::F32), 2),
            &["vector_float"][..],
        ),
        (
            "VectorI8One",
            Ty::Vector(Box::new(Ty::I8), 1),
            &["short_vector"][..],
        ),
        ("VectorI8Zero", Ty::Vector(Box::new(Ty::I8), 0), &[][..]),
        ("VectorI128", Ty::Vector(Box::new(Ty::I128), 2), &[][..]),
        ("VectorPtr", Ty::Vector(Box::new(Ty::Ptr), 2), &[][..]),
        ("VectorChar", Ty::Vector(Box::new(Ty::Char), 2), &[][..]),
        ("VectorIsize", Ty::Vector(Box::new(Ty::Isize), 2), &[][..]),
    ] {
        types.push(TypeCase {
            name: name.into(),
            ty,
            accepts,
        });
    }
    for (name, kind) in [
        ("Slice", FatPtrKind::Slice(byte)),
        ("Str", FatPtrKind::Str),
        ("TraitObject", FatPtrKind::TraitObject { trait_id: 7 }),
        ("ContainerLen", FatPtrKind::ContainerLen),
        ("ContainerVtable", FatPtrKind::ContainerVtable),
    ] {
        types.push(TypeCase {
            name: name.into(),
            ty: Ty::FatPtr(kind),
            accepts: &["null_pair"],
        });
    }
    let ints = || vec![C::Int(7), C::Int(9)];
    let families = vec![
        ("int", C::Int(7)),
        ("zero", C::Int(0)),
        ("u128", C::U128((1u128 << 127) + 7)),
        ("float", C::Float(0.1)),
        ("bool", C::Bool(true)),
        (
            "bytes",
            C::Bytes {
                data: vec![3, 9],
                utf8: false,
            },
        ),
        (
            "empty_bytes",
            C::Bytes {
                data: vec![],
                utf8: false,
            },
        ),
        ("empty_aggregate", C::Aggregate(vec![])),
        ("fields", C::Aggregate(vec![C::Int(7), C::Bool(true)])),
        (
            "pointer_fields",
            C::Aggregate(vec![C::Int(0), C::Bool(true)]),
        ),
        ("null_pair", C::Aggregate(vec![C::Int(0), C::Int(0)])),
        (
            "enum_fields",
            C::Aggregate(vec![C::Int(3), C::Int(7), C::Bool(true)]),
        ),
        ("pos_array", C::Aggregate(ints())),
        ("array", C::Array(ints())),
        ("empty_array", C::Array(vec![])),
        (
            "splat",
            C::Splat {
                elem: Box::new(C::Int(7)),
                len: 2,
            },
        ),
        ("vector_int", C::Vector(ints())),
        ("vector_zero", C::Vector(vec![C::Int(0), C::Int(0)])),
        (
            "vector_bool",
            C::Vector(vec![C::Bool(true), C::Bool(false)]),
        ),
        (
            "vector_float",
            C::Vector(vec![C::Float(0.1), C::Float(1.0006)]),
        ),
        ("short_vector", C::Vector(vec![C::Int(7)])),
        ("empty_vector", C::Vector(vec![])),
        ("sequence", C::Sequence(ints())),
        ("set", C::Set(ints())),
        (
            "record",
            C::Record(vec![("a".into(), C::Int(7)), ("b".into(), C::Bool(true))]),
        ),
        (
            "duplicate_record",
            C::Record(vec![("a".into(), C::Int(7)), ("a".into(), C::Int(9))]),
        ),
        (
            "closure",
            C::Closure {
                func: closure_target,
                captures: vec![C::Int(7), C::Bool(true)],
            },
        ),
        ("function", C::FnDef(function)),
        ("phantom", C::PhantomData),
        ("uninit", C::Uninit),
        (
            "unwritten_fields",
            C::Aggregate(vec![C::Uninit, C::Bool(true)]),
        ),
        ("short_array", C::Array(vec![C::Int(7)])),
    ];
    assert_eq!(types.len(), 53);
    assert_eq!(families.len(), 32);
    (mb, types, families)
}

fn matrix_module(bits: u32) -> (Module, Vec<Run>) {
    let (mut mb, types, families) = definitions(bits);
    let sig = mb.add_func_type(vec![], vec![]);
    let mut runs = Vec::new();
    for case in &types {
        for (family, value) in &families {
            let mut fb = mb.function(format!("{}_{}", case.name, family), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.const_value(case.ty.clone(), value.clone());
            fb.ret(vec![]);
            let expected = if case.accepts.contains(family) {
                Verdict::Ok(vec![])
            } else if let (Ty::Vector(_, count), C::Vector(values)) = (&case.ty, value) {
                if !matches!(
                    case.name.as_str(),
                    "VectorI128" | "VectorPtr" | "VectorChar" | "VectorIsize"
                ) && (*count == 0 || values.len() != *count as usize)
                {
                    Verdict::Unsupported("vector_shape".into())
                } else {
                    Verdict::TypeError(String::new())
                }
            } else {
                Verdict::TypeError(String::new())
            };
            runs.push(Run {
                func: fb.build(),
                label: format!("{bits}/{}:{family}", case.name),
                expected,
            });
        }
    }
    let module = mb.build().expect("typed constant cross product");
    assert!(
        !trust_ir_build::validate_module(&module).is_empty(),
        "the matrix intentionally includes invalid constants"
    );
    assert_eq!(runs.len(), 1696);
    (module, runs)
}

#[test]
fn constant_family_type_cross_product_checks_unused_values() {
    let modules: Vec<_> = [32, 64].into_iter().map(matrix_module).collect();
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(module, runs)| Batch {
            label: module.name.clone(),
            module,
            runs: runs.iter().map(|run| (run.func, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 3392);
    let mut counts = (0, 0, 0);
    for (report, run) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, runs)| runs))
    {
        match &run.expected {
            Verdict::Ok(values) => {
                assert_eq!(
                    report.rust,
                    Verdict::Ok(values.clone()),
                    "{}: {report:?}",
                    run.label
                );
                assert_eq!(
                    report.lean,
                    Verdict::Ok(values.clone()),
                    "{}: {report:?}",
                    run.label
                );
                assert_eq!(report.comparison, Comparison::Agree);
                counts.0 += 1;
            }
            Verdict::TypeError(_) => {
                assert!(
                    matches!(report.rust, Verdict::TypeError(_)),
                    "{}: {report:?}",
                    run.label
                );
                assert!(
                    matches!(report.lean, Verdict::TypeError(_)),
                    "{}: {report:?}",
                    run.label
                );
                counts.1 += 1;
            }
            Verdict::Unsupported(_) => {
                assert_eq!(
                    report.rust,
                    Verdict::Unsupported("unsupported_vector_shape".into()),
                    "{}: {report:?}",
                    run.label
                );
                assert_eq!(
                    report.lean,
                    Verdict::Unsupported("vector_shape".into()),
                    "{}: {report:?}",
                    run.label
                );
                counts.2 += 1;
            }
            _ => unreachable!(),
        }
    }
    assert_eq!(counts, (148, 3210, 34));
    eprintln!(
        "typed constant cross product: {} successful, {} TypeError, {} vector census refusals",
        counts.0, counts.1, counts.2
    );
}

fn value_for(case: &TypeCase, family: &str, bits: u32) -> Val {
    let i8_value = |raw| Val::Int { width: 8, raw };
    let fields = || vec![i8_value(7), Val::Bool(true)];
    match family {
        "int" | "zero" if case.ty != Ty::Ptr => Val::Int {
            width: case.ty.bit_width_with(bits).expect("integer width"),
            raw: if family == "int" { 7 } else { 0 },
        },
        "zero" => Val::Ptr { null: true },
        "u128" => Val::Int {
            width: 128,
            raw: (1u128 << 127) + 7,
        },
        "float" => Val::Float(
            match case.ty {
                Ty::F16 => 0.0999755859375f64,
                Ty::F32 => 0.1f32 as f64,
                Ty::F64 => 0.1,
                _ => unreachable!(),
            }
            .to_bits(),
        ),
        "bool" => Val::Bool(true),
        "phantom" | "empty_aggregate" | "empty_array" | "empty_bytes" => Val::Aggregate(vec![]),
        "bytes" => Val::Aggregate(vec![i8_value(3), i8_value(9)]),
        "fields" | "unwritten_fields" if matches!(case.ty, Ty::Record(_)) => Val::Record(vec![
            ("a".into(), i8_value(7)),
            ("b".into(), Val::Bool(true)),
        ]),
        "fields" | "unwritten_fields"
            if !matches!(case.name.as_str(), "TuplePtr" | "StructPtr") =>
        {
            Val::Aggregate(fields())
        }
        "pointer_fields" if matches!(case.ty, Ty::Record(_)) => Val::Record(vec![
            ("a".into(), i8_value(0)),
            ("b".into(), Val::Bool(true)),
        ]),
        "pointer_fields" if !matches!(case.name.as_str(), "TuplePtr" | "StructPtr") => {
            Val::Aggregate(vec![i8_value(0), Val::Bool(true)])
        }
        "pointer_fields" | "unwritten_fields" => {
            Val::Aggregate(vec![Val::Ptr { null: true }, Val::Bool(true)])
        }
        "null_pair" => {
            let Ty::FatPtr(kind) = &case.ty else {
                unreachable!()
            };
            let metadata = if matches!(
                kind,
                FatPtrKind::TraitObject { .. } | FatPtrKind::ContainerVtable
            ) {
                Val::Ptr { null: true }
            } else {
                Val::Int {
                    width: bits,
                    raw: 0,
                }
            };
            Val::FatPtr(Box::new(Val::Ptr { null: true }), Box::new(metadata))
        }
        "enum_fields" => Val::Aggregate(vec![i8_value(3), i8_value(7), Val::Bool(true)]),
        "array" | "pos_array" => Val::Aggregate(vec![i8_value(7), i8_value(9)]),
        "splat" => Val::Aggregate(vec![i8_value(7), i8_value(7)]),
        "vector_int" => Val::Vector(vec![i8_value(7), i8_value(9)]),
        "vector_zero" => Val::Vector(vec![i8_value(0), i8_value(0)]),
        "short_vector" => Val::Vector(vec![i8_value(7)]),
        "vector_bool" => Val::Vector(vec![Val::Bool(true), Val::Bool(false)]),
        "vector_float" => Val::Vector(
            [0.1f64, 1.0006]
                .into_iter()
                .map(|value| Val::Float((value as f32 as f64).to_bits()))
                .collect(),
        ),
        "sequence" => Val::Sequence(vec![i8_value(7), i8_value(9)]),
        "set" => Val::Set(vec![i8_value(7), i8_value(9)]),
        "record" => Val::Record(vec![
            ("a".into(), i8_value(7)),
            ("b".into(), Val::Bool(true)),
        ]),
        "closure" => Val::Closure {
            func: 1,
            captures: fields(),
        },
        "function" => Val::Function {
            signature: 0,
            func: 0,
        },
        _ => unreachable!("no golden value for {family}/{}", case.name),
    }
}

fn positive_module(bits: u32) -> (Module, Vec<Run>) {
    let (mut mb, types, families) = definitions(bits);
    let mut runs = Vec::new();
    for case in &types {
        for (family, constant) in &families {
            if !case.accepts.contains(family) {
                continue;
            }
            // Uniform positional arrays are typed but canonically spelled
            // Splat. The raw matrix includes them; this validated cohort
            // already exercises their canonical spelling.
            if *family == "null_pair" && matches!(case.ty, Ty::Array(_, _)) {
                continue;
            }
            let sig = mb.add_func_type(vec![], vec![case.ty.clone()]);
            let mut fb = mb.function(format!("{}_{}", case.name, family), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let mut value = fb.const_value(case.ty.clone(), constant.clone());
            if *family == "unwritten_fields" {
                let (ty, constant) = if matches!(case.name.as_str(), "TuplePtr" | "StructPtr") {
                    (Ty::Ptr, C::Int(0))
                } else {
                    (Ty::I8, C::Int(7))
                };
                let replacement = fb.const_value(ty, constant);
                value = fb.insert_field(case.ty.clone(), value, 0, replacement);
            }
            fb.ret(vec![value]);
            runs.push(Run {
                func: fb.build(),
                label: format!("{bits}/{}:{family}", case.name),
                expected: Verdict::Ok(vec![value_for(case, family, bits)]),
            });
        }
    }
    let module = mb.build().expect("valid constant families");
    assert_eq!(runs.len(), 72);
    (module, runs)
}

fn cold_variants(module: Module) -> Vec<(&'static str, Module)> {
    let binary = trust_ir::binary::serialize_module(&module).expect("encode binary");
    let text = trust_ir::format::text_checked(&module).expect("encode text");
    let json = serde_json::to_vec(&module).expect("encode JSON");
    let msgpack = rmp_serde::to_vec(&module).expect("encode MessagePack");
    vec![
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
    ]
}

#[test]
fn typed_constant_values_and_unwritten_repairs_survive_cold_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, runs) = positive_module(bits);
        for (codec, module) in cold_variants(module) {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((
                format!("constant_values_{bits}_{codec}"),
                module,
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
            runs: runs.iter().map(|run| (run.func, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 720);
    for (report, run) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, runs)| runs))
    {
        assert_eq!(report.rust, run.expected, "{}: {report:?}", run.label);
        assert_eq!(report.lean, run.expected, "{}: {report:?}", run.label);
        assert_eq!(
            report.comparison,
            Comparison::Agree,
            "{}: {report:?}",
            run.label
        );
    }
}

fn nested_refusal_module(bits: u32) -> (Module, Vec<Run>) {
    let (mut mb, types, _) = definitions(bits);
    let ty = |name: &str| {
        types
            .iter()
            .find(|case| case.name == name)
            .expect("declared type")
            .ty
            .clone()
    };
    let bad_fields = || vec![C::Bool(true), C::Bool(true)];
    let mut cases = vec![
        ("tuple_field", ty("Tuple"), C::Aggregate(bad_fields())),
        ("struct_field", ty("Struct"), C::Aggregate(bad_fields())),
        (
            "enum_field",
            ty("Enum"),
            C::Aggregate(vec![C::Int(3), C::Bool(true), C::Bool(true)]),
        ),
        (
            "record_field",
            ty("Record"),
            C::Record(vec![
                ("a".into(), C::Bool(true)),
                ("b".into(), C::Bool(true)),
            ]),
        ),
        (
            "record_positional",
            ty("Record"),
            C::Aggregate(bad_fields()),
        ),
        (
            "closure_capture",
            ty("Closure"),
            C::Closure {
                func: FuncId::new(1),
                captures: bad_fields(),
            },
        ),
        (
            "array_field",
            ty("ArrayI8"),
            C::Array(vec![C::Bool(true), C::Int(7)]),
        ),
        (
            "array_positional",
            ty("ArrayI8"),
            C::Aggregate(vec![C::Bool(true), C::Int(7)]),
        ),
        (
            "splat_field",
            ty("ArrayI8"),
            C::Splat {
                elem: Box::new(C::Bool(true)),
                len: 2,
            },
        ),
        (
            "sequence_field",
            ty("Sequence"),
            C::Sequence(vec![C::Bool(true), C::Int(7)]),
        ),
        (
            "set_field",
            ty("Set"),
            C::Set(vec![C::Bool(true), C::Int(7)]),
        ),
        ("vector_field", ty("VectorI8"), C::Vector(bad_fields())),
    ];
    let tuple = ty("TuplePtr");
    let tuple_id = mb.add_type(tuple.clone());
    let unwritten = || C::Aggregate(vec![C::Uninit, C::Bool(true)]);
    let nested_struct = mb.add_struct(StructDef {
        id: StructId::new(10),
        name: "Nested".into(),
        fields: vec![FieldDef {
            name: "v".into(),
            ty: tuple.clone(),
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    cases.extend([
        (
            "nested_tuple_uninit",
            Ty::Tuple(vec![tuple.clone()]),
            C::Aggregate(vec![unwritten()]),
        ),
        (
            "nested_struct_uninit",
            Ty::Struct(nested_struct),
            C::Aggregate(vec![unwritten()]),
        ),
        (
            "array_tuple_uninit",
            Ty::Array(tuple_id, 2),
            C::Splat {
                elem: Box::new(unwritten()),
                len: 2,
            },
        ),
        (
            "sequence_tuple_uninit",
            Ty::Sequence(tuple_id),
            C::Sequence(vec![unwritten()]),
        ),
        (
            "record_uninit",
            ty("Record"),
            C::Record(vec![("a".into(), C::Uninit), ("b".into(), C::Bool(true))]),
        ),
        (
            "closure_uninit",
            ty("Closure"),
            C::Closure {
                func: FuncId::new(1),
                captures: vec![C::Uninit, C::Bool(true)],
            },
        ),
        (
            "enum_uninit",
            ty("Enum"),
            C::Aggregate(vec![C::Int(3), C::Uninit, C::Bool(true)]),
        ),
        (
            "vector_uninit",
            ty("VectorI8"),
            C::Vector(vec![C::Uninit, C::Int(7)]),
        ),
        (
            "splat_uninit",
            ty("ArrayI8"),
            C::Splat {
                elem: Box::new(C::Uninit),
                len: 2,
            },
        ),
        (
            "nested_record_duplicate",
            Ty::Tuple(vec![ty("Record")]),
            C::Aggregate(vec![C::Record(vec![
                ("a".into(), C::Int(7)),
                ("a".into(), C::Int(9)),
            ])]),
        ),
        (
            "enum_bool_tag",
            ty("Enum"),
            C::Aggregate(vec![C::Bool(false), C::Int(7), C::Bool(true)]),
        ),
        (
            "record_unknown_name",
            ty("Record"),
            C::Record(vec![("a".into(), C::Int(7)), ("z".into(), C::Bool(true))]),
        ),
        (
            "closure_count",
            ty("Closure"),
            C::Closure {
                func: FuncId::new(1),
                captures: vec![C::Int(7)],
            },
        ),
        (
            "splat_float_at_integer",
            ty("ArrayI8"),
            C::Splat {
                elem: Box::new(C::Float(0.1)),
                len: 2,
            },
        ),
        (
            "nested_bytes_count",
            Ty::Tuple(vec![ty("ArrayU8")]),
            C::Aggregate(vec![C::Bytes {
                data: vec![3],
                utf8: false,
            }]),
        ),
    ]);
    assert_eq!(cases.len(), 27);
    let sig = mb.add_func_type(vec![], vec![]);
    let mut runs = Vec::new();
    for (name, ty, constant) in cases {
        let mut fb = mb.function(name, sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.const_value(ty, constant);
        fb.ret(vec![]);
        runs.push(Run {
            func: fb.build(),
            label: format!("{bits}/{name}"),
            expected: Verdict::TypeError(String::new()),
        });
    }
    (mb.build().expect("nested refusal module"), runs)
}

#[test]
fn nested_constant_types_and_unwritten_placement_refuse_across_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, runs) = nested_refusal_module(bits);
        for (codec, module) in cold_variants(module) {
            assert!(!trust_ir_build::validate_module(&module).is_empty());
            modules.push((
                format!("nested_refusal_{bits}_{codec}"),
                module,
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
            runs: runs.iter().map(|run| (run.func, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 270);
    for (report, run) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, runs)| runs))
    {
        assert!(
            matches!(report.rust, Verdict::TypeError(_)),
            "{}: {report:?}",
            run.label
        );
        assert!(
            matches!(report.lean, Verdict::TypeError(_)),
            "{}: {report:?}",
            run.label
        );
    }
}

fn global_module(bits: u32, valid_only: bool) -> (Module, Vec<Run>) {
    use trust_ir::value::GlobalId;
    use trust_ir::{Global, Linkage};
    let (mut mb, _, _) = definitions(bits);
    let void = mb.add_func_type(vec![], vec![]);
    let mut runs = Vec::new();
    for (index, (ty, constant)) in [
        (Ty::I8, C::Bool(true)),
        (Ty::Bool, C::Int(1)),
        (Ty::F64, C::Int(7)),
        (Ty::I32, C::Float(1.5)),
        (Ty::Unit, C::Aggregate(vec![])),
        (
            Ty::Vector(Box::new(Ty::I8), 2),
            C::Vector(vec![C::Int(7), C::Bool(true)]),
        ),
        (Ty::Ptr, C::PhantomData),
        (Ty::I8, C::U128(u128::MAX)),
        (Ty::F32, C::Bool(true)),
        (Ty::I8, C::Uninit),
    ]
    .into_iter()
    .enumerate()
    .filter(|_| !valid_only)
    {
        mb.add_global(Global {
            name: format!("BAD{index}"),
            ty,
            mutable: false,
            initializer: Some(constant),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let mut fb = mb.function(format!("bad_global_{index}"), void);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.global_addr(GlobalId::new(index as u32));
        fb.ret(vec![]);
        runs.push(Run {
            func: fb.build(),
            label: format!("{bits}/bad_global_{index}"),
            expected: Verdict::TypeError(String::new()),
        });
    }
    if valid_only {
        mb.add_global(Global {
            name: "UNIT".into(),
            ty: Ty::Unit,
            mutable: false,
            initializer: Some(C::PhantomData),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let sig = mb.add_func_type(vec![], vec![Ty::Unit]);
        let mut fb = mb.function("unit_global_load", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let pointer = fb.global_addr(GlobalId::new(0));
        let value = fb.load(Ty::Unit, pointer);
        fb.ret(vec![value]);
        runs.push(Run {
            func: fb.build(),
            label: format!("{bits}/unit_global"),
            expected: Verdict::Ok(vec![Val::Aggregate(vec![])]),
        });
        let mut fb = mb.function("unit_store_load", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let pointer = fb.alloca(Ty::Unit);
        let value = fb.const_value(Ty::Unit, C::PhantomData);
        fb.store(Ty::Unit, pointer, value);
        let value = fb.load(Ty::Unit, pointer);
        fb.ret(vec![value]);
        runs.push(Run {
            func: fb.build(),
            label: format!("{bits}/unit_store"),
            expected: Verdict::Ok(vec![Val::Aggregate(vec![])]),
        });
    }
    (mb.build().expect("global type-check module"), runs)
}

#[test]
fn global_initializers_check_families_and_unit_has_an_empty_image() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        for valid in [false, true] {
            let (module, runs) = global_module(bits, valid);
            assert_eq!(runs.len(), if valid { 2 } else { 10 });
            for (codec, module) in cold_variants(module) {
                let errors = trust_ir_build::validate_module(&module);
                assert_eq!(
                    errors.is_empty(),
                    valid,
                    "{bits}/{codec}/{valid}: {errors:?}"
                );
                modules.push((
                    format!("global_types_{bits}_{codec}_{valid}"),
                    module,
                    runs.clone(),
                ));
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs.iter().map(|run| (run.func, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 120);
    for (report, run) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, runs)| runs))
    {
        if matches!(run.expected, Verdict::TypeError(_)) {
            assert!(
                matches!(report.rust, Verdict::TypeError(_)),
                "{}: {report:?}",
                run.label
            );
            assert!(
                matches!(report.lean, Verdict::TypeError(_)),
                "{}: {report:?}",
                run.label
            );
        } else {
            assert_eq!(report.rust, run.expected, "{}: {report:?}", run.label);
            assert_eq!(report.lean, run.expected, "{}: {report:?}", run.label);
            assert_eq!(
                report.comparison,
                Comparison::Agree,
                "{}: {report:?}",
                run.label
            );
        }
    }
}
