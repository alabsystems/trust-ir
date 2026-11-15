// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Real instruction execution and whole-result observations, across all five
//! codecs. Indexed checks supplement the exact full graph comparison.

use super::{Batch, Comparison, Oracle, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::inst::BinOp;
use trust_ir::ty::{ClosureTy, FieldDef, StructDef};
use trust_ir::{FuncId, Module, Ordering, StructId, Ty};
use trust_ir_build::ModuleBuilder;

fn codecs(module: Module) -> Vec<Module> {
    let binary = trust_ir::binary::serialize_module(&module).unwrap();
    let text = trust_ir::format::text_checked(&module).unwrap();
    let json = serde_json::to_vec(&module).unwrap();
    let msgpack = rmp_serde::to_vec(&module).unwrap();
    vec![
        module,
        trust_ir::binary::deserialize_module(&binary).unwrap(),
        trust_ir::parser::parse_module(&text).unwrap(),
        serde_json::from_slice(&json).unwrap(),
        rmp_serde::from_slice(&msgpack).unwrap(),
    ]
}

fn repeated(value: C, count: u64) -> C {
    match count {
        0 => C::Array(vec![]),
        1 => C::Array(vec![value]),
        _ => C::Splat {
            elem: Box::new(value),
            len: count,
        },
    }
}

fn graph(verdict: &Verdict) -> &super::compact_value_graph::Graph {
    let Verdict::Graph(graph) = verdict else {
        panic!("expected an executed graph: {verdict:?}")
    };
    graph
}

fn array_extent(graph: &super::compact_value_graph::Graph, root: usize, count: u64) {
    let node = &graph.nodes()[root];
    assert_eq!(
        node[0], "array",
        "actual execution must use the compact array carrier"
    );
    assert_eq!(node[1], count.to_string());
    assert!(graph.sequence_element(root, count).is_none());
}

fn int_at(graph: &super::compact_value_graph::Graph, root: usize, index: u64, expected: u64) {
    let value = graph
        .sequence_element(root, index)
        .expect("in-bounds array value");
    assert_eq!(value[0], "int");
    assert_eq!(value[1], 32);
    assert_eq!(value[2], expected.to_string());
}

fn register_module(bits: u32, count: u64) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("compact_register_{bits}_{count}"),
        semr_target(bits),
    );
    let element = mb.add_type(Ty::U32);
    let ty = Ty::Array(element, count);
    let apparent = mb.add_func_type(vec![], vec![ty.clone()]);
    let physical = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
    let cid = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![ty.clone()],
    });
    let target = {
        let mut fb = mb.function("capture_identity", physical);
        let block = fb.create_block();
        let captured = fb.add_block_param(block, ty.clone());
        fb.switch_to_block(block);
        fb.ret(vec![captured]);
        fb.build()
    };
    let signature = mb.add_func_type(
        vec![],
        vec![
            ty.clone(),
            ty.clone(),
            ty.clone(),
            ty.clone(),
            Ty::U32,
            Ty::U32,
        ],
    );
    let root = {
        let mut fb = mb.function("entry", signature);
        let block = fb.create_block();
        fb.switch_to_block(block);
        let constant = fb.const_value(ty.clone(), repeated(C::Int(7), count));
        let seven = fb.uconst(Ty::U32, 7);
        let register = if count == 0 {
            fb.make_aggregate(ty.clone(), vec![])
        } else {
            fb.array_splat(ty.clone(), seven)
        };
        let (updated, old_last, new_last) = if count == 0 {
            let zero = fb.uconst(Ty::U32, 0);
            (register, zero, zero)
        } else {
            let index = fb.uconst(Ty::U64, u128::from(count - 1));
            let replacement = fb.uconst(Ty::U32, 99);
            let updated = fb.insert_element(ty.clone(), register, index, replacement);
            let old = fb.extract_element(Ty::U32, register, index);
            let new = fb.extract_element(Ty::U32, updated, index);
            (updated, old, new)
        };
        let closure = fb.make_closure(cid, target, vec![updated]);
        let returned = fb.call_indirect(closure, apparent, vec![]);
        fb.ret(vec![
            constant, register, updated, returned, old_last, new_last,
        ]);
        fb.build()
    };
    let module = mb.build().unwrap();
    assert!(
        trust_ir_build::validate_module(&module).is_empty(),
        "{}",
        module.name
    );
    (module, root)
}

#[test]
fn actual_compact_arrays_cover_constants_registers_closures_and_late_updates() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        for count in [0, 1, 2, u64::from(u32::MAX) + 17, u64::MAX] {
            let (module, root) = register_module(bits, count);
            for module in codecs(module) {
                modules.push((module, root, count));
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(module, root, _)| Batch {
            label: module.name.clone(),
            module,
            runs: vec![(*root, vec![])],
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 50);
    for (report, (_, _, count)) in reports.iter().zip(&modules) {
        assert_eq!(
            report.comparison,
            Comparison::Agree,
            "full compact execution must agree: {report:?}"
        );
        for verdict in [&report.rust, &report.lean] {
            let graph = graph(verdict);
            assert_eq!(graph.roots().len(), 6);
            assert!(
                graph.nodes().len() < 512,
                "logical count must not control output storage"
            );
            for (slot, &root) in graph.roots()[..4].iter().enumerate() {
                array_extent(graph, root, *count);
                if *count > 0 {
                    for index in [0, count / 2, count - 1] {
                        let expected = if slot >= 2 && index == count - 1 {
                            99
                        } else {
                            7
                        };
                        int_at(graph, root, index, expected);
                    }
                }
            }
            for (slot, expected) in [
                (4, if *count == 0 { "0" } else { "7" }),
                (5, if *count == 0 { "0" } else { "99" }),
            ] {
                assert_eq!(
                    graph.nodes()[graph.roots()[slot]],
                    serde_json::json!(["int", 32, expected])
                );
            }
        }
    }
    eprintln!("COMPACT_REGISTER_PASS 50 executed rows");
}

fn memory_module(bits: u32) -> (Module, FuncId) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("compact_memory_{bits}"), semr_target(bits));
    let element = mb.add_type(Ty::U32);
    let ty = Ty::Array(element, 65);
    let sig = mb.add_func_type(
        vec![],
        vec![
            ty.clone(),
            ty.clone(),
            ty.clone(),
            ty.clone(),
            ty.clone(),
            Ty::Bool,
            Ty::Bool,
            Ty::U32,
        ],
    );
    let mut fb = mb.function("entry", sig);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let constant = fb.const_value(ty.clone(), C::Array((0..65).map(C::Int).collect()));
    let lanes = (0..65).map(|n| fb.uconst(Ty::U32, n)).collect();
    let made = fb.make_aggregate(ty.clone(), lanes);
    let last = fb.uconst(Ty::U64, 64);
    let replacement = fb.uconst(Ty::U32, 777);
    let updated = fb.insert_element(ty.clone(), made, last, replacement);
    let pointer = fb.alloca(ty.clone());
    fb.store(ty.clone(), pointer, constant);
    let (old1, yes) = fb.cmpxchg(
        ty.clone(),
        pointer,
        made,
        updated,
        Ordering::SeqCst,
        Ordering::SeqCst,
    );
    let (old2, no) = fb.cmpxchg(
        ty.clone(),
        pointer,
        made,
        constant,
        Ordering::SeqCst,
        Ordering::SeqCst,
    );
    let loaded = fb.load(ty.clone(), pointer);
    let value = fb.extract_element(Ty::U32, loaded, last);
    fb.ret(vec![constant, made, old1, old2, loaded, yes, no, value]);
    let root = fb.build();
    let module = mb.build().unwrap();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (module, root)
}

#[test]
fn actual_compact_arrays_preserve_typed_images_and_strong_exchange() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, root) = memory_module(bits);
        for module in codecs(module) {
            modules.push((module, root));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(module, root)| Batch {
            label: module.name.clone(),
            module,
            runs: vec![(*root, vec![])],
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 10);
    for report in reports {
        assert_eq!(
            report.comparison,
            Comparison::Agree,
            "typed array exchange must match exact contents: {report:?}"
        );
        for verdict in [&report.rust, &report.lean] {
            let graph = graph(verdict);
            assert_eq!(graph.roots().len(), 8);
            for (slot, &root) in graph.roots()[..5].iter().enumerate() {
                array_extent(graph, root, 65);
                for index in 0..65 {
                    int_at(
                        graph,
                        root,
                        index,
                        if slot >= 3 && index == 64 { 777 } else { index },
                    );
                }
            }
            assert_eq!(
                graph.nodes()[graph.roots()[5]],
                serde_json::json!(["bool", true])
            );
            assert_eq!(
                graph.nodes()[graph.roots()[6]],
                serde_json::json!(["bool", false])
            );
            assert_eq!(
                graph.nodes()[graph.roots()[7]],
                serde_json::json!(["int", 32, "777"])
            );
        }
    }
    eprintln!("COMPACT_MEMORY_PASS 10 executed rows");
}

fn empty_image_module(bits: u32, count: u64) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("compact_zst_{bits}_{count}"),
        semr_target(bits),
    );
    let element = mb.add_type(Ty::Unit);
    let ty = Ty::Array(element, count);
    let sig = mb.add_func_type(vec![], vec![ty.clone(), ty.clone(), ty.clone(), Ty::Bool]);
    let mut fb = mb.function("entry", sig);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let original = fb.const_value(ty.clone(), repeated(C::PhantomData, count));
    let expected = if count == 0 {
        original
    } else {
        let unit = fb.const_value(Ty::Unit, C::PhantomData);
        let index = fb.uconst(Ty::U64, u128::from(count - 1));
        fb.insert_element(ty.clone(), original, index, unit)
    };
    let pointer = fb.alloca(ty.clone());
    fb.store(ty.clone(), pointer, original);
    let (old, success) = fb.cmpxchg(
        ty.clone(),
        pointer,
        expected,
        original,
        Ordering::SeqCst,
        Ordering::SeqCst,
    );
    let loaded = fb.load(ty, pointer);
    fb.ret(vec![expected, old, loaded, success]);
    let root = fb.build();
    let module = mb.build().unwrap();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (module, root)
}

#[test]
fn actual_compact_arrays_with_zero_sized_elements_use_empty_images() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        for count in [0, 1, 17, u64::MAX] {
            let (module, root) = empty_image_module(bits, count);
            for module in codecs(module) {
                modules.push((module, root, count));
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(module, root, _)| Batch {
            label: module.name.clone(),
            module,
            runs: vec![(*root, vec![])],
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 40);
    for (report, (_, _, count)) in reports.iter().zip(&modules) {
        assert_eq!(
            report.comparison,
            Comparison::Agree,
            "zero-sized array image must remain compact: {report:?}"
        );
        for verdict in [&report.rust, &report.lean] {
            let graph = graph(verdict);
            assert_eq!(graph.roots().len(), 4);
            assert!(graph.nodes().len() < 512);
            for &root in &graph.roots()[..3] {
                array_extent(graph, root, *count);
                if *count > 0 {
                    for index in [0, count / 2, count - 1] {
                        assert_eq!(graph.sequence_element(root, index).unwrap()[0], "aggregate");
                    }
                }
            }
            assert_eq!(
                graph.nodes()[graph.roots()[3]],
                serde_json::json!(["bool", true])
            );
        }
    }
    eprintln!("COMPACT_ZST_PASS 40 executed rows");
}

fn guard_module(bits: u32, case: usize) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("compact_guard_{bits}_{case}"),
        semr_target(bits),
    );
    let s0 = mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "A".into(),
        fields: vec![FieldDef {
            name: "x".into(),
            ty: Ty::U32,
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    let s1 = mb.add_struct(StructDef {
        id: StructId::new(1),
        name: "B".into(),
        fields: vec![FieldDef {
            name: "x".into(),
            ty: Ty::U32,
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    let wanted = if case == 3 {
        Ty::Struct(s0)
    } else if case == 4 {
        Ty::F64
    } else {
        Ty::I32
    };
    let element = mb.add_type(wanted);
    let ty = Ty::Array(element, if case == 1 || case == 4 { 2 } else { 1 });
    let sig = mb.add_func_type(vec![], if case == 4 { vec![ty.clone()] } else { vec![] });
    let mut fb = mb.function("entry", sig);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let fields = match case {
        0 => vec![fb.uconst(Ty::U32, 7)],
        1 => vec![fb.iconst(Ty::I32, 7)],
        2 => vec![fb.undef(Ty::U32)],
        3 => vec![fb.const_value(Ty::Struct(s1), C::Aggregate(vec![C::Int(7)]))],
        4 => {
            let zero = fb.fconst(Ty::F64, 0.0);
            let nan = fb.binop(BinOp::FDiv, Ty::F64, zero, zero);
            let finite = fb.fconst(Ty::F64, 1.5);
            vec![nan, finite]
        }
        _ => unreachable!(),
    };
    let array = fb.make_aggregate(ty, fields);
    fb.ret(if case == 4 { vec![array] } else { vec![] });
    let root = fb.build();
    let module = mb.build().unwrap();
    assert_eq!(
        trust_ir_build::validate_module(&module).is_empty(),
        case == 4
    );
    (module, root)
}

#[test]
fn actual_array_constructors_refuse_wrong_sources_without_observing_payloads() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        for case in 0..5 {
            let (module, root) = guard_module(bits, case);
            for module in codecs(module) {
                modules.push((module, root, case));
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(module, root, _)| Batch {
            label: module.name.clone(),
            module,
            runs: vec![(*root, vec![])],
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 50);
    let mut census = [0; 3];
    for (report, (_, _, case)) in reports.iter().zip(&modules) {
        match case {
            2 => {
                assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
                assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
                census[1] += 1;
            }
            4 => {
                assert_eq!(
                    report.comparison,
                    Comparison::Agree,
                    "array constructor must transport NaNs without image admission: {report:?}"
                );
                for verdict in [&report.rust, &report.lean] {
                    let graph = graph(verdict);
                    let root = graph.roots()[0];
                    array_extent(graph, root, 2);
                    assert_eq!(
                        graph.sequence_element(root, 0).unwrap(),
                        &serde_json::json!(["float", "nan"])
                    );
                    assert_eq!(
                        graph.sequence_element(root, 1).unwrap(),
                        &serde_json::json!(["float", 1.5f64.to_bits().to_string()])
                    );
                }
                census[2] += 1;
            }
            _ => {
                assert!(matches!(report.rust, Verdict::TypeError(_)), "{report:?}");
                assert!(
                    matches!(report.lean, Verdict::TypeError(_)),
                    "array constructor must reject wrong original source type or census: {report:?}"
                );
                census[0] += 1;
            }
        }
    }
    assert_eq!(census, [30, 10, 10]);
    eprintln!(
        "COMPACT_GUARD_PASS 50 executed rows: 30 type errors, 10 poison UB, 10 NaN transport"
    );
}
