// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::{Batch, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::ty::{FatPtrKind, FieldDef, RecordDef};
use trust_ir::value::{GlobalId, RecordId};
use trust_ir::{Global, Linkage, Ty};
use trust_ir_build::ModuleBuilder;

#[test]
fn malformed_pointer_forms_and_global_images_refuse() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb =
            ModuleBuilder::new_with_target_info(format!("null_refusals_{bits}"), semr_target(bits));
        let byte = mb.add_type(Ty::U8);
        let mut cases = vec![
            (Ty::Ptr, C::Int(7)),
            (Ty::Ptr, C::Int(-1)),
            (Ty::Ptr, C::Bool(false)),
        ];
        for kind in [
            FatPtrKind::Slice(byte),
            FatPtrKind::Str,
            FatPtrKind::TraitObject { trait_id: 7 },
            FatPtrKind::ContainerLen,
            FatPtrKind::ContainerVtable,
        ] {
            for values in [
                vec![C::Int(1), C::Int(0)],
                vec![C::Int(0), C::Int(1)],
                vec![C::Int(0), C::Float(0.1)],
                vec![C::Int(0)],
                vec![C::Bool(false), C::Int(0)],
            ] {
                cases.push((Ty::FatPtr(kind), C::Aggregate(values)));
            }
        }
        let bad = C::Aggregate(vec![C::Int(0), C::Float(0.1)]);
        let fat = Ty::FatPtr(FatPtrKind::Str);
        let tid = mb.add_type(fat.clone());
        let rid = mb.add_record(RecordDef {
            id: RecordId::new(8),
            name: "R".into(),
            fields: vec![FieldDef {
                name: "a".into(),
                ty: fat.clone(),
                offset: None,
            }],
        });
        cases.extend([
            (Ty::Tuple(vec![Ty::Ptr]), C::Aggregate(vec![C::Int(7)])),
            (
                Ty::Tuple(vec![fat.clone()]),
                C::Aggregate(vec![bad.clone()]),
            ),
            (Ty::Record(rid), C::Record(vec![("a".into(), bad.clone())])),
            (
                Ty::Array(tid, 2),
                C::Splat {
                    elem: Box::new(bad.clone()),
                    len: 2,
                },
            ),
            (Ty::Sequence(tid), C::Sequence(vec![bad])),
        ]);
        let sig = mb.add_func_type(vec![], vec![]);
        let mut runs = Vec::new();
        for (index, (ty, value)) in cases.into_iter().enumerate() {
            let mut fb = mb.function(format!("bad_{index}"), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.const_value(ty, value);
            fb.ret(vec![]);
            runs.push((fb.build(), vec![]));
        }
        for (index, (ty, value)) in [
            (Ty::I8, C::U128(u128::MAX)),
            (Ty::Bool, C::Int(1)),
            (Ty::Ptr, C::Int(7)),
        ]
        .into_iter()
        .enumerate()
        {
            mb.add_global(Global {
                name: format!("G{index}"),
                ty,
                mutable: true,
                initializer: Some(value),
                linkage: Linkage::Internal,
                tls: None,
                align: None,
                section: None,
                visibility: Default::default(),
                retained: false,
            });
            let mut fb = mb.function(format!("bad_global_{index}"), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.global_addr(GlobalId::new(index as u32));
            fb.ret(vec![]);
            runs.push((fb.build(), vec![]));
        }
        let module = mb.build().expect("pointer refusal module");
        assert!(!trust_ir_build::validate_module(&module).is_empty());
        assert_eq!(runs.len(), 36);
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
    assert_eq!(reports.len(), 72);
    for report in reports {
        assert!(matches!(report.rust, Verdict::TypeError(_)), "{report:?}");
        assert!(matches!(report.lean, Verdict::TypeError(_)), "{report:?}");
    }
}

#[test]
fn link_time_pointer_constants_keep_their_explicit_boundary() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb =
            ModuleBuilder::new_with_target_info(format!("link_boundary_{bits}"), semr_target(bits));
        mb.add_global(Global {
            name: "BYTE".into(),
            ty: Ty::U8,
            mutable: false,
            initializer: Some(C::Int(7)),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let ty = Ty::PtrConst(Box::new(Ty::U8));
        let sig = mb.add_func_type(vec![], vec![ty.clone()]);
        let mut fb = mb.function("pointer", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let pointer = fb.const_value(
            ty,
            C::SymbolAddr {
                symbol: "BYTE".into(),
                addend: 0,
            },
        );
        fb.ret(vec![pointer]);
        let root = fb.build();
        let module = mb.build().expect("symbol boundary module");
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let mut malformed = module.clone();
        malformed.functions[0].blocks[0].body[0].inst = trust_ir::Inst::Const {
            ty: Ty::FatPtr(FatPtrKind::Str),
            value: C::Aggregate(vec![
                C::SymbolAddr {
                    symbol: "BYTE".into(),
                    addend: 0,
                },
                C::Float(0.1),
            ]),
        };
        modules.push((module, root, false));
        modules.push((malformed, root, true));
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(module, root, _)| Batch {
            label: module.name.clone(),
            module,
            runs: vec![(*root, vec![])],
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 4);
    for (report, (_, _, malformed)) in reports.iter().zip(&modules) {
        if *malformed {
            assert!(matches!(report.rust, Verdict::TypeError(_)), "{report:?}");
        } else {
            assert_eq!(
                report.rust,
                Verdict::Ok(vec![Val::Ptr { null: false }]),
                "{report:?}"
            );
        }
        assert_eq!(
            report.lean,
            Verdict::Unsupported("link_time_address".into()),
            "{report:?}"
        );
    }
}
