// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::{Batch, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::ty::{ClosureTy, EnumDef, EnumVariant, FatPtrKind, FieldDef, RecordDef, StructDef};
use trust_ir::value::{EnumId, FuncId, RecordId, StructId};
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone)]
enum Expected {
    Value(Val),
    TypeError,
    Poison,
}

fn module(bits: u32, count: u64, wrong: bool) -> (Module, Vec<(FuncId, Expected)>) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("typed_splat_{bits}_{count}_{wrong}"),
        semr_target(bits),
    );
    let logical = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("logical", logical);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    let logical_fn = fb.build();
    let physical = mb.add_func_type(vec![Ty::I32], vec![]);
    let mut fb = mb.function("physical", physical);
    let entry = fb.create_block();
    fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    let physical_fn = fb.build();
    let mut structs = Vec::new();
    let mut records = Vec::new();
    let mut enums = Vec::new();
    let mut closures = Vec::new();
    for id in 0..2 {
        let fields = vec![FieldDef {
            name: "x".into(),
            ty: Ty::I32,
            offset: None,
        }];
        structs.push(mb.add_struct(StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: fields.clone(),
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        }));
        records.push(mb.add_record(RecordDef {
            id: RecordId::new(id),
            name: format!("R{id}"),
            fields,
        }));
        enums.push(mb.add_enum(EnumDef::new(
            EnumId::new(id),
            format!("E{id}"),
            vec![EnumVariant {
                name: "Only".into(),
                fields: vec![Ty::I32],
                field_names: vec![],
            }],
        )));
        closures.push(mb.add_closure_type(ClosureTy {
            func: logical,
            captures: vec![Ty::I32],
        }));
    }
    let int = |width, raw| Val::Int { width, raw };
    let mut cases = Vec::new();
    for (a, b) in [
        (Ty::I8, Ty::U8),
        (Ty::I16, Ty::U16),
        (Ty::I32, Ty::U32),
        (Ty::I64, Ty::U64),
        (Ty::I128, Ty::U128),
        (Ty::Isize, Ty::Usize),
        (Ty::Char, Ty::U32),
    ] {
        for (wanted, actual) in [(a.clone(), b.clone()), (b, a)] {
            let value = int(actual.bit_width_with(bits).expect("integer width"), 9);
            cases.push((wanted, actual, C::Int(9), value));
        }
    }
    for (wanted, actual) in [(Ty::F32, Ty::F64), (Ty::F64, Ty::F32), (Ty::F16, Ty::F32)] {
        cases.push((wanted, actual, C::Float(0.5), Val::Float(0.5f64.to_bits())));
    }
    cases.extend([
        (Ty::U8, Ty::Bool, C::Bool(true), Val::Bool(true)),
        (Ty::Bool, Ty::U8, C::Int(1), int(8, 1)),
        (Ty::Ptr, Ty::Usize, C::Int(0), int(bits, 0)),
        (Ty::Usize, Ty::Ptr, C::Int(0), Val::Ptr { null: true }),
        (
            Ty::Tuple(vec![Ty::I32]),
            Ty::Tuple(vec![Ty::U32]),
            C::Aggregate(vec![C::Int(9)]),
            Val::Aggregate(vec![int(32, 9)]),
        ),
        (
            Ty::Tuple(vec![]),
            Ty::Unit,
            C::PhantomData,
            Val::Aggregate(vec![]),
        ),
        (
            Ty::Unit,
            Ty::Tuple(vec![]),
            C::Aggregate(vec![]),
            Val::Aggregate(vec![]),
        ),
        (Ty::F32, Ty::F64, C::Float(f64::NAN), Val::Nan),
        (Ty::F64, Ty::F32, C::Float(f64::NAN), Val::Nan),
        (
            Ty::Func(logical),
            Ty::Func(physical),
            C::FnDef(physical_fn),
            Val::Function {
                signature: physical.index(),
                func: physical_fn.index(),
            },
        ),
        (
            Ty::Func(physical),
            Ty::Func(logical),
            C::FnDef(logical_fn),
            Val::Function {
                signature: logical.index(),
                func: logical_fn.index(),
            },
        ),
        (
            Ty::Struct(structs[0]),
            Ty::Struct(structs[1]),
            C::Aggregate(vec![C::Int(9)]),
            Val::Aggregate(vec![int(32, 9)]),
        ),
        (
            Ty::Struct(structs[1]),
            Ty::Struct(structs[0]),
            C::Aggregate(vec![C::Int(9)]),
            Val::Aggregate(vec![int(32, 9)]),
        ),
        (
            Ty::Record(records[0]),
            Ty::Record(records[1]),
            C::Aggregate(vec![C::Int(9)]),
            Val::Record(vec![("x".into(), int(32, 9))]),
        ),
        (
            Ty::Enum(enums[0]),
            Ty::Enum(enums[1]),
            C::Aggregate(vec![C::Int(0), C::Int(9)]),
            Val::Aggregate(vec![int(8, 0), int(32, 9)]),
        ),
        (
            Ty::Closure(closures[0]),
            Ty::Closure(closures[1]),
            C::Closure {
                func: physical_fn,
                captures: vec![C::Int(9)],
            },
            Val::Closure {
                func: physical_fn.index(),
                captures: vec![int(32, 9)],
            },
        ),
        (
            Ty::FatPtr(FatPtrKind::Str),
            Ty::FatPtr(FatPtrKind::ContainerLen),
            C::Aggregate(vec![C::Int(0), C::Int(0)]),
            Val::FatPtr(Box::new(Val::Ptr { null: true }), Box::new(int(bits, 0))),
        ),
        (
            Ty::FatPtr(FatPtrKind::ContainerLen),
            Ty::FatPtr(FatPtrKind::Str),
            C::Aggregate(vec![C::Int(0), C::Int(0)]),
            Val::FatPtr(Box::new(Val::Ptr { null: true }), Box::new(int(bits, 0))),
        ),
    ]);
    assert_eq!(cases.len(), 35, "reviewed element-type roster");
    let mut runs = Vec::new();
    for (index, (wanted, actual, constant, expected)) in cases.into_iter().enumerate() {
        assert_ne!(
            wanted, actual,
            "negative control must change the actual type"
        );
        let element_ty = if wrong { wanted } else { actual.clone() };
        let element = mb.add_type(element_ty);
        let array_ty = Ty::Array(element, count);
        // Wrong-type cases discard the result, so neither a return check nor
        // an element consumer can hide an unchecked ArraySplat constructor.
        let returns = if wrong {
            vec![]
        } else {
            vec![array_ty.clone()]
        };
        let sig = mb.add_func_type(vec![], returns);
        let mut fb = mb.function(format!("case_{index}"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = fb.const_value(actual, constant);
        let array = fb.array_splat(array_ty, value);
        fb.ret(if wrong { vec![] } else { vec![array] });
        runs.push((
            fb.build(),
            if wrong {
                Expected::TypeError
            } else {
                Expected::Value(Val::Aggregate(vec![expected; count as usize]))
            },
        ));
    }
    let source = if wrong { Ty::U32 } else { Ty::I32 };
    let element = mb.add_type(Ty::I32);
    let sig = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("poison_precedes_type", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let poison = fb.undef(source);
    fb.array_splat(Ty::Array(element, count), poison);
    fb.ret(vec![]);
    runs.push((fb.build(), Expected::Poison));
    let module = mb.build().expect("typed ArraySplat matrix");
    if count > 0 && !wrong {
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "validated positive cohort: {errors:?}");
    }
    (module, runs)
}

#[test]
fn array_splat_exact_element_types_and_register_transport() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        for count in [0, 1, 3] {
            for wrong in [false, true] {
                let (module, runs) = module(bits, count, wrong);
                let binary = trust_ir::binary::serialize_module(&module).expect("binary");
                let text = trust_ir::format::text_checked(&module).expect("text");
                let json = serde_json::to_vec(&module).expect("JSON");
                let msgpack = rmp_serde::to_vec(&module).expect("MessagePack");
                for module in [
                    module,
                    trust_ir::binary::deserialize_module(&binary).expect("binary"),
                    trust_ir::parser::parse_module(&text).expect("text"),
                    serde_json::from_slice(&json).expect("JSON"),
                    rmp_serde::from_slice(&msgpack).expect("MessagePack"),
                ] {
                    if count > 0 && !wrong {
                        assert!(trust_ir_build::validate_module(&module).is_empty());
                    }
                    modules.push((module, runs.clone()));
                }
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(module, runs)| Batch {
            label: module.name.clone(),
            module,
            runs: runs
                .iter()
                .map(|(function, _)| (*function, vec![]))
                .collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 2160);
    let mut census = [0; 3];
    for (report, (_, expected)) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, runs)| runs))
    {
        match expected {
            Expected::Value(value) => {
                assert_eq!(report.rust, Verdict::Ok(vec![value.clone()]), "{report:?}");
                assert_eq!(report.rust, report.lean, "{report:?}");
                census[0] += 1;
            }
            Expected::TypeError => {
                assert!(matches!(report.rust, Verdict::TypeError(_)), "{report:?}");
                assert!(matches!(report.lean, Verdict::TypeError(_)), "{report:?}");
                census[1] += 1;
            }
            Expected::Poison => {
                assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
                assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
                census[2] += 1;
            }
        }
    }
    assert_eq!(census, [1050, 1050, 60]);
}
