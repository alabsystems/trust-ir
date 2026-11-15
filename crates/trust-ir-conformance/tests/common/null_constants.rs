// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant;
use trust_ir::inst::{CastOp, ICmpOp};
use trust_ir::ty::{
    ClosureTy, EnumDef, EnumTagRepr, EnumVariant, FatPtrKind, FieldDef, RecordDef, SetRepr,
    StructDef, Ty,
};
use trust_ir::value::{EnumId, FuncId, GlobalId, RecordId, StructId};
use trust_ir::{Global, Linkage, Module};
use trust_ir_build::ModuleBuilder;

#[derive(Clone)]
struct ExpectedRun {
    func: FuncId,
    /// `None` means execution must report UB before returning a value.
    values: Option<Vec<Val>>,
}

fn null_constant(ty: &Ty) -> Constant {
    match ty {
        Ty::Ptr => Constant::Int(0),
        Ty::FatPtr(_) => Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
        _ => unreachable!("the null matrix only constructs pointer leaves"),
    }
}

fn null_value(ty: &Ty, bits: u32) -> Val {
    let null = Val::Ptr { null: true };
    match ty {
        Ty::Ptr => null,
        Ty::FatPtr(kind) => {
            let metadata = match kind.metadata_ty(bits).expect("canonical metadata type") {
                Ty::U32 => Val::Int { width: 32, raw: 0 },
                Ty::U64 => Val::Int { width: 64, raw: 0 },
                Ty::Ptr => null.clone(),
                ty => unreachable!("unexpected pointer metadata type: {ty:?}"),
            };
            Val::FatPtr(Box::new(null), Box::new(metadata))
        }
        _ => unreachable!("the null matrix only observes pointer leaves"),
    }
}

fn add_constant_case(mb: &mut ModuleBuilder, name: String, ty: Ty, constant: Constant) -> FuncId {
    let sig = mb.add_func_type(vec![], vec![ty.clone()]);
    let mut fb = mb.function(name, sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let value = fb.const_value(ty, constant);
    fb.ret(vec![value]);
    fb.build()
}

fn add_global(
    mb: &mut ModuleBuilder,
    next_global: &mut u32,
    name: String,
    ty: Ty,
    initializer: Constant,
) -> GlobalId {
    let id = GlobalId::new(*next_global);
    *next_global += 1;
    mb.add_global(Global {
        name,
        ty,
        mutable: false,
        initializer: Some(initializer),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    id
}

fn null_module(bits: u32) -> (Module, Vec<ExpectedRun>) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("null_constants_{bits}"), semr_target(bits));
    let byte = mb.add_type(Ty::U8);
    let leaves = [
        ("thin", Ty::Ptr),
        ("slice", Ty::FatPtr(FatPtrKind::Slice(byte))),
        ("str", Ty::FatPtr(FatPtrKind::Str)),
        (
            "trait_object",
            Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 7 }),
        ),
        ("container_len", Ty::FatPtr(FatPtrKind::ContainerLen)),
        ("container_vtable", Ty::FatPtr(FatPtrKind::ContainerVtable)),
    ];
    let mut expected = Vec::new();
    let mut next_global = 0;
    for (index, (name, leaf_ty)) in leaves.into_iter().enumerate() {
        let constant = null_constant(&leaf_ty);
        let value = null_value(&leaf_ty, bits);
        let leaf_id = mb.add_type(leaf_ty.clone());
        let fields = vec![
            FieldDef {
                name: "a".into(),
                ty: leaf_ty.clone(),
                offset: None,
            },
            FieldDef {
                name: "z".into(),
                ty: Ty::Bool,
                offset: None,
            },
        ];
        let sid = mb.add_struct(StructDef {
            id: StructId::new(10 + index as u32 * 10),
            name: format!("NullStruct_{name}"),
            fields: fields.clone(),
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        let rid = mb.add_record(RecordDef {
            id: RecordId::new(10 + index as u32 * 10),
            name: format!("NullRecord_{name}"),
            fields,
        });
        let eid = mb.add_enum(
            EnumDef::new(
                EnumId::new(10 + index as u32 * 10),
                format!("NullEnum_{name}"),
                vec![EnumVariant {
                    name: "Pointer".into(),
                    fields: vec![leaf_ty.clone()],
                    field_names: vec![],
                }],
            )
            .with_repr(EnumTagRepr::U8),
        );
        let aggregate = Constant::Aggregate(vec![constant.clone(), Constant::Bool(true)]);
        let aggregate_value = Val::Aggregate(vec![value.clone(), Val::Bool(true)]);
        let cases = [
            ("direct", leaf_ty.clone(), constant.clone(), value.clone()),
            (
                "tuple",
                Ty::Tuple(vec![leaf_ty.clone(), Ty::Bool]),
                aggregate.clone(),
                aggregate_value.clone(),
            ),
            ("struct", Ty::Struct(sid), aggregate, aggregate_value),
            (
                "record",
                Ty::Record(rid),
                Constant::Record(vec![
                    ("a".into(), constant.clone()),
                    ("z".into(), Constant::Bool(true)),
                ]),
                Val::Record(vec![
                    ("a".into(), value.clone()),
                    ("z".into(), Val::Bool(true)),
                ]),
            ),
            (
                "array_splat",
                Ty::Array(leaf_id, 2),
                Constant::Splat {
                    elem: Box::new(constant.clone()),
                    len: 2,
                },
                Val::Aggregate(vec![value.clone(); 2]),
            ),
            (
                "sequence",
                Ty::Sequence(leaf_id),
                Constant::Sequence(vec![constant.clone()]),
                Val::Sequence(vec![value.clone()]),
            ),
            (
                "set",
                Ty::Set(leaf_id, SetRepr::Boxed),
                Constant::Set(vec![constant.clone()]),
                Val::Set(vec![value.clone()]),
            ),
            (
                "enum",
                Ty::Enum(eid),
                Constant::Aggregate(vec![Constant::Int(0), constant.clone()]),
                Val::Aggregate(vec![Val::Int { width: 8, raw: 0 }, value.clone()]),
            ),
        ];
        for (shape, ty, constant, value) in cases {
            expected.push(ExpectedRun {
                func: add_constant_case(&mut mb, format!("{name}_{shape}"), ty, constant),
                values: Some(vec![value]),
            });
        }

        // Construct and invoke the closure: a constant closure-shaped value
        // would not exercise capture carriage through MakeClosure/CallIndirect.
        let apparent = mb.add_func_type(vec![], vec![leaf_ty.clone()]);
        let physical = mb.add_func_type(vec![leaf_ty.clone()], vec![leaf_ty.clone()]);
        let cid = mb.add_closure_type(ClosureTy {
            func: apparent,
            captures: vec![leaf_ty.clone()],
        });
        let target = {
            let mut fb = mb.function(format!("{name}_closure_target"), physical);
            let entry = fb.create_block();
            let capture = fb.add_block_param(entry, leaf_ty.clone());
            fb.switch_to_block(entry);
            fb.ret(vec![capture]);
            fb.build()
        };
        let closure = {
            let mut fb = mb.function(format!("{name}_closure"), apparent);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let capture = fb.const_value(leaf_ty.clone(), constant.clone());
            let closure = fb.make_closure(cid, target, vec![capture]);
            let result = fb.call_indirect(closure, apparent, vec![]);
            fb.ret(vec![result]);
            fb.build()
        };
        expected.push(ExpectedRun {
            func: closure,
            values: Some(vec![value.clone()]),
        });

        let global = add_global(
            &mut mb,
            &mut next_global,
            format!("{name}_global"),
            leaf_ty.clone(),
            constant.clone(),
        );
        let sig = mb.add_func_type(vec![], vec![leaf_ty.clone(), Ty::Bool]);
        let mut fb = mb.function(format!("{name}_global_load_and_cache"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let address = fb.global_addr(global);
        let again = fb.global_addr(global);
        let same_address = fb.icmp(ICmpOp::Eq, Ty::Ptr, address, again);
        let loaded = fb.load(leaf_ty.clone(), address);
        fb.ret(vec![loaded, same_address]);
        expected.push(ExpectedRun {
            func: fb.build(),
            values: Some(vec![value.clone(), Val::Bool(true)]),
        });

        let int_ty = if bits == 32 { Ty::U32 } else { Ty::U64 };
        let (returns, expected_outputs) = match &leaf_ty {
            Ty::Ptr => (
                vec![int_ty.clone()],
                vec![Val::Int {
                    width: bits,
                    raw: 0,
                }],
            ),
            Ty::FatPtr(kind) => {
                let metadata_ty = kind.metadata_ty(bits).expect("canonical metadata type");
                let Val::FatPtr(data, metadata) = &value else {
                    unreachable!()
                };
                (
                    vec![int_ty.clone(), Ty::Ptr, metadata_ty, leaf_ty.clone()],
                    vec![
                        Val::Int {
                            width: bits,
                            raw: 0,
                        },
                        (**data).clone(),
                        (**metadata).clone(),
                        value.clone(),
                    ],
                )
            }
            _ => unreachable!(),
        };
        let sig = mb.add_func_type(vec![], returns);
        let mut fb = mb.function(format!("{name}_pointer_consumers"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let pointer = fb.const_value(leaf_ty.clone(), constant.clone());
        let outputs = match &leaf_ty {
            Ty::Ptr => vec![fb.cast(CastOp::PtrToInt, Ty::Ptr, int_ty, pointer)],
            Ty::FatPtr(kind) => {
                let metadata_ty = kind.metadata_ty(bits).expect("canonical metadata type");
                let data = fb.ptr_data(leaf_ty.clone(), pointer);
                let metadata = fb.ptr_metadata(leaf_ty.clone(), metadata_ty.clone(), pointer);
                let rebuilt = fb.ptr_from_parts(leaf_ty.clone(), metadata_ty, data, metadata);
                let integer = fb.cast(CastOp::PtrToInt, Ty::Ptr, int_ty, data);
                vec![integer, data, metadata, rebuilt]
            }
            _ => unreachable!(),
        };
        fb.ret(outputs);
        expected.push(ExpectedRun {
            func: fb.build(),
            values: Some(expected_outputs),
        });

        let sig = mb.add_func_type(vec![], vec![Ty::U8]);
        let mut fb = mb.function(format!("{name}_dereference_null"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let pointer = fb.const_value(leaf_ty.clone(), constant);
        let data = if matches!(leaf_ty, Ty::FatPtr(_)) {
            fb.ptr_data(leaf_ty, pointer)
        } else {
            pointer
        };
        let byte = fb.load(Ty::U8, data);
        fb.ret(vec![byte]);
        expected.push(ExpectedRun {
            func: fb.build(),
            values: None,
        });
    }

    // These inline globals must use their element types while lowering the
    // initializer, including integer residue and binary32 rounding.
    for (name, ty, constant, value) in [
        (
            "vector_i8",
            Ty::Vector(Box::new(Ty::I8), 2),
            Constant::Vector(vec![Constant::Int(-7), Constant::Int(2)]),
            Val::Vector(vec![
                Val::Int { width: 8, raw: 249 },
                Val::Int { width: 8, raw: 2 },
            ]),
        ),
        (
            "vector_f32",
            Ty::Vector(Box::new(Ty::F32), 2),
            Constant::Vector(vec![Constant::Float(0.1), Constant::Float(1.0006)]),
            Val::Vector(vec![
                Val::Float((0.1f64 as f32 as f64).to_bits()),
                Val::Float((1.0006f64 as f32 as f64).to_bits()),
            ]),
        ),
    ] {
        let global = add_global(&mut mb, &mut next_global, name.into(), ty.clone(), constant);
        let sig = mb.add_func_type(vec![], vec![ty.clone()]);
        let mut fb = mb.function(format!("{name}_global_load"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let address = fb.global_addr(global);
        let result = fb.load(ty, address);
        fb.ret(vec![result]);
        expected.push(ExpectedRun {
            func: fb.build(),
            values: Some(vec![value]),
        });
    }

    let global = add_global(
        &mut mb,
        &mut next_global,
        "null_before_fresh_alloca".into(),
        Ty::Ptr,
        Constant::Int(0),
    );
    let sig = mb.add_func_type(vec![], vec![Ty::Ptr, Ty::I32]);
    let mut fb = mb.function("global_null_then_fresh_uninitialized_load", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let address = fb.global_addr(global);
    let null = fb.load(Ty::Ptr, address);
    let fresh = fb.alloca(Ty::I32);
    let uninitialized = fb.load(Ty::I32, fresh);
    fb.ret(vec![null, uninitialized]);
    expected.push(ExpectedRun {
        func: fb.build(),
        values: None,
    });

    assert_eq!(expected.len(), 75);
    assert_eq!(
        expected.iter().filter(|run| run.values.is_some()).count(),
        68
    );
    (mb.build().expect("null constant matrix module"), expected)
}

/// Cold codecs carry runtime values; they do not grant a producer body license.
#[test]
fn null_constants_preserve_shapes_consumers_and_globals_across_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, expected) = null_module(bits);
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
                format!("null_constants_{bits}_{format}"),
                decoded,
                expected.clone(),
            ));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, expected)| Batch {
            label: label.clone(),
            module,
            runs: expected.iter().map(|run| (run.func, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 750);
    let mut ok = 0;
    let mut ub = 0;
    for (report, expected) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, expected)| expected))
    {
        if let Some(values) = &expected.values {
            let verdict = Verdict::Ok(values.clone());
            assert_eq!(report.rust, verdict, "{report:?}");
            assert_eq!(report.lean, verdict, "{report:?}");
            ok += 1;
        } else {
            assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
            assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
            ub += 1;
        }
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
    assert_eq!((ok, ub), (680, 70));
}
