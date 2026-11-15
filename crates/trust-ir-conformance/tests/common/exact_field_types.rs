// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::{Batch, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant;
use trust_ir::ty::{EnumDef, EnumTagRepr, EnumVariant, FieldDef, RecordDef, StructDef};
use trust_ir::value::{EnumId, RecordId, StructId};
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

fn cases(bits: u32) -> (Module, Vec<(trust_ir::value::FuncId, bool, bool, u128)>) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("exact_fields_{bits}"), semr_target(bits));
    let enumeration = mb.add_enum(EnumDef {
        id: EnumId::new(0),
        name: "SignedOrUnsigned".into(),
        variants: vec![
            EnumVariant {
                name: "Signed".into(),
                fields: vec![Ty::I32],
                field_names: vec![],
            },
            EnumVariant {
                name: "Unsigned".into(),
                fields: vec![Ty::U32],
                field_names: vec![],
            },
        ],
        discriminants: vec![Some(-1), Some(7)],
        repr: Some(EnumTagRepr::I8),
        layout: None,
        origin: None,
    });
    let mut runs = Vec::new();
    for (signed, lane, other, disc) in [(true, Ty::I32, Ty::U32, -1), (false, Ty::U32, Ty::I32, 7)]
    {
        let fields = vec![FieldDef {
            name: "x".into(),
            ty: lane.clone(),
            offset: None,
        }];
        let sid = mb.add_struct(StructDef {
            id: StructId::new(u32::from(!signed)),
            name: format!("S{signed}"),
            fields: fields.clone(),
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        let rid = mb.add_record(RecordDef {
            id: RecordId::new(u32::from(!signed)),
            name: format!("R{signed}"),
            fields,
        });
        for (kind, aggregate, constant, field) in [
            (
                "tuple",
                Ty::Tuple(vec![lane.clone()]),
                Constant::Aggregate(vec![Constant::Int(9)]),
                0,
            ),
            (
                "struct",
                Ty::Struct(sid),
                Constant::Aggregate(vec![Constant::Int(9)]),
                0,
            ),
            (
                "record",
                Ty::Record(rid),
                Constant::Aggregate(vec![Constant::Int(9)]),
                0,
            ),
            (
                "enum",
                Ty::Enum(enumeration),
                Constant::Aggregate(vec![Constant::Int(disc), Constant::Int(9)]),
                1,
            ),
        ] {
            for write in [false, true] {
                for wrong in [false, true] {
                    let access = if wrong { other.clone() } else { lane.clone() };
                    let result = if write { lane.clone() } else { access.clone() };
                    let sig = mb.add_func_type(vec![], vec![result]);
                    let mut fb = mb.function(format!("{kind}_{signed}_{write}_{wrong}"), sig);
                    let entry = fb.create_block();
                    fb.switch_to_block(entry);
                    let held = fb.const_value(aggregate.clone(), constant.clone());
                    let result = if write {
                        let replacement = fb.const_value(access, Constant::Int(3));
                        let updated = fb.insert_field(aggregate.clone(), held, field, replacement);
                        fb.extract_field(lane.clone(), updated, field)
                    } else {
                        fb.extract_field(access, held, field)
                    };
                    fb.ret(vec![result]);
                    runs.push((fb.build(), wrong, kind == "enum", if write { 3 } else { 9 }));
                }
            }
        }
    }
    // The tag rewrite itself is forbidden, even for an equal-width unsigned
    // replacement or a different-width replacement. It precedes lane typing.
    for replacement_ty in [Ty::I8, Ty::U8, Ty::U64] {
        let sig = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function(format!("forbidden_tag_write_{replacement_ty:?}"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let held = fb.const_value(
            Ty::Enum(enumeration),
            Constant::Aggregate(vec![Constant::Int(-1), Constant::Int(9)]),
        );
        let replacement = fb.const_value(replacement_ty, Constant::Int(3));
        fb.insert_field(Ty::Enum(enumeration), held, 0, replacement);
        fb.ret(vec![]);
        runs.push((fb.build(), true, true, 0));
    }
    // Rust checks the aggregate's nominal result type before either the
    // forbidden tag-write rule or field bounds.
    for field in [0, 1, 99] {
        let sig = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function(format!("wrong_aggregate_type_{field}"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let held = fb.const_value(
            Ty::Enum(enumeration),
            Constant::Aggregate(vec![Constant::Int(-1), Constant::Int(9)]),
        );
        let replacement = fb.const_value(Ty::I32, Constant::Int(3));
        fb.insert_field(Ty::Tuple(vec![Ty::I32]), held, field, replacement);
        fb.ret(vec![]);
        runs.push((fb.build(), true, false, 0));
    }
    (mb.build().expect("field matrix"), runs)
}

#[test]
fn exact_field_signedness_and_active_variants_survive_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, runs) = cases(bits);
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
            modules.push((module, runs.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(module, runs)| Batch {
            label: module.name.clone(),
            module,
            runs: runs.iter().map(|(f, _, _, _)| (*f, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 380);
    for (report, (_, wrong, enumeration, expected)) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, runs)| runs))
    {
        if *wrong {
            if *enumeration {
                assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
                assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
            } else {
                assert!(matches!(report.rust, Verdict::TypeError(_)), "{report:?}");
                assert!(matches!(report.lean, Verdict::TypeError(_)), "{report:?}");
            }
        } else {
            assert_eq!(
                report.rust,
                Verdict::Ok(vec![Val::Int {
                    width: 32,
                    raw: *expected
                }]),
                "{report:?}"
            );
            assert_eq!(report.rust, report.lean, "{report:?}");
        }
    }
}
