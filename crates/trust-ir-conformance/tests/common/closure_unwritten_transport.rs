// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::ty::{ClosureTy, FieldDef, StructDef};
use trust_ir::value::{FuncId, StructId};
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy, Debug)]
enum Op {
    Construct,
    ExtractWhole,
    InsertWhole,
    CallIgnore,
    CallReadSibling,
    CallReturnWhole,
    CallArgument,
    ReadUnwritten,
}

fn case(bits: u32, structure: bool, unwritten: bool, op: Op) -> (Module, FuncId, Option<Val>) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("closure_transport_{bits}_{structure}_{unwritten}_{op:?}"),
        semr_target(bits),
    );
    let capture_ty = if structure {
        Ty::Struct(mb.add_struct(StructDef {
            id: StructId::new(0),
            name: "Pair".into(),
            fields: vec![
                FieldDef {
                    name: "first".into(),
                    ty: Ty::U32,
                    offset: None,
                },
                FieldDef {
                    name: "second".into(),
                    ty: Ty::U32,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        }))
    } else {
        Ty::Tuple(vec![Ty::U32, Ty::U32])
    };
    let whole_result = matches!(op, Op::CallReturnWhole);
    let logical_result = if whole_result {
        capture_ty.clone()
    } else {
        Ty::U32
    };
    let argument = matches!(op, Op::CallArgument);
    let apparent = mb.add_func_type(
        if argument {
            vec![capture_ty.clone()]
        } else {
            vec![]
        },
        vec![logical_result.clone()],
    );
    let physical = mb.add_func_type(vec![capture_ty.clone()], vec![logical_result]);
    let cid = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: if argument {
            vec![]
        } else {
            vec![capture_ty.clone()]
        },
    });
    let target = {
        let mut fb = mb.function("target", physical);
        let block = fb.create_block();
        let capture = fb.add_block_param(block, capture_ty.clone());
        fb.switch_to_block(block);
        let result = if whole_result {
            capture
        } else if matches!(op, Op::CallReadSibling) {
            fb.extract_field(Ty::U32, capture, 1)
        } else {
            fb.iconst(Ty::U32, 99)
        };
        fb.ret(vec![result]);
        fb.build()
    };
    let returns_whole = matches!(op, Op::ExtractWhole | Op::InsertWhole | Op::CallReturnWhole);
    let entry_sig = mb.add_func_type(
        vec![],
        vec![if returns_whole {
            capture_ty.clone()
        } else {
            Ty::U32
        }],
    );
    let mut fb = mb.function("entry", entry_sig);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let payload = C::Aggregate(vec![
        if unwritten { C::Uninit } else { C::Int(1) },
        C::Int(42),
    ]);
    let capture = fb.const_value(capture_ty.clone(), payload);
    // InsertWhole isolates replacement transport: its initial environment is fully written.
    let initial = if matches!(op, Op::InsertWhole) {
        fb.const_value(capture_ty.clone(), C::Aggregate(vec![C::Int(7), C::Int(8)]))
    } else {
        capture
    };
    let closure = fb.make_closure(cid, target, if argument { vec![] } else { vec![initial] });
    let result = match op {
        Op::Construct => fb.iconst(Ty::U32, 99),
        Op::ExtractWhole => fb.extract_field(capture_ty.clone(), closure, 0),
        Op::InsertWhole => {
            let updated = fb.insert_field(Ty::Closure(cid), closure, 0, capture);
            fb.extract_field(capture_ty, updated, 0)
        }
        Op::CallIgnore | Op::CallReadSibling | Op::CallReturnWhole => {
            fb.call_indirect(closure, apparent, vec![])
        }
        Op::CallArgument => fb.call_indirect(closure, apparent, vec![capture]),
        Op::ReadUnwritten => {
            let held = fb.extract_field(capture_ty, closure, 0);
            fb.extract_field(Ty::U32, held, 0)
        }
    };
    fb.ret(vec![result]);
    let entry = fb.build();
    let module = mb.build().expect("closure transport module");
    let expected = if matches!(op, Op::ReadUnwritten) && unwritten {
        None
    } else if returns_whole {
        Some(Val::Aggregate(vec![
            if unwritten {
                Val::Uninit
            } else {
                Val::Int { width: 32, raw: 1 }
            },
            Val::Int { width: 32, raw: 42 },
        ]))
    } else {
        Some(Val::Int {
            width: 32,
            raw: match op {
                Op::CallReadSibling => 42,
                Op::ReadUnwritten => 1,
                _ => 99,
            },
        })
    };
    (module, entry, expected)
}

#[test]
fn unwritten_aggregate_fields_transport_through_closures_and_fault_at_read() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        for structure in [false, true] {
            for unwritten in [false, true] {
                for op in [
                    Op::Construct,
                    Op::ExtractWhole,
                    Op::InsertWhole,
                    Op::CallIgnore,
                    Op::CallReadSibling,
                    Op::CallReturnWhole,
                    Op::CallArgument,
                    Op::ReadUnwritten,
                ] {
                    let (module, entry, expected) = case(bits, structure, unwritten, op);
                    assert!(
                        trust_ir_build::validate_module(&module).is_empty(),
                        "{}",
                        module.name
                    );
                    let binary = trust_ir::binary::serialize_module(&module).expect("binary");
                    let text = trust_ir::format::text_checked(&module).expect("text");
                    let json = serde_json::to_vec(&module).expect("JSON");
                    let msgpack = rmp_serde::to_vec(&module).expect("MessagePack");
                    for (format, decoded) in [
                        ("original", module),
                        (
                            "binary",
                            trust_ir::binary::deserialize_module(&binary).expect("binary decode"),
                        ),
                        (
                            "text",
                            trust_ir::parser::parse_module(&text).expect("text decode"),
                        ),
                        ("JSON", serde_json::from_slice(&json).expect("JSON decode")),
                        (
                            "MessagePack",
                            rmp_serde::from_slice(&msgpack).expect("MessagePack decode"),
                        ),
                    ] {
                        assert!(
                            trust_ir_build::validate_module(&decoded).is_empty(),
                            "{} {format}",
                            decoded.name
                        );
                        modules.push((format, decoded, entry, expected.clone()));
                    }
                }
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(format, module, entry, _)| Batch {
            label: format!("{}-{format}", module.name),
            module,
            runs: vec![(*entry, vec![])],
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 320);
    let mut rust_values = 0;
    let mut rust_faults = 0;
    for (report, (_, _, _, expected)) in reports.iter().zip(&modules) {
        match expected {
            Some(expected) => {
                assert_eq!(
                    report.rust,
                    Verdict::Ok(vec![expected.clone()]),
                    "{report:?}"
                );
                rust_values += 1;
            }
            None => {
                assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
                rust_faults += 1;
            }
        }
    }
    assert_eq!((rust_values, rust_faults), (300, 20));
    eprintln!("closure transport Rust census: 300 exact results, 20 read UBs");
    let mut values = 0;
    let mut faults = 0;
    for (report, (_, _, _, expected)) in reports.iter().zip(&modules) {
        match expected {
            Some(expected) => {
                let expected = Verdict::Ok(vec![expected.clone()]);
                assert_eq!(report.rust, expected, "{report:?}");
                assert_eq!(report.lean, expected, "{report:?}");
                values += 1;
            }
            None => {
                assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
                assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
                faults += 1;
            }
        }
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
    assert_eq!((values, faults), (300, 20));
    eprintln!("closure transport Lean census: 300 exact results, 20 read UBs");
}
