// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual bulk operations over sparse images. Generic Lean pointwise laws
//! cover the full byte ranges; these runs check instruction/codec wiring.
use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::value::GlobalId;
use trust_ir::{FuncId, Global, Linkage, Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone)]
enum Expected {
    Values(Vec<Val>),
    Ub,
}

fn byte(value: u128) -> Val {
    Val::Int {
        width: 8,
        raw: value,
    }
}

fn module(bits: u32, count: u64) -> (Module, Vec<(FuncId, Expected)>) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("compact_bulk_{bits}_{count}"),
        semr_target(bits),
    );
    let element = mb.add_type(Ty::U8);
    let array = Ty::Array(element, count);
    mb.add_global(Global {
        name: "zero_region".into(),
        ty: array.clone(),
        mutable: true,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let signature = mb.add_func_type(vec![], vec![Ty::U8; 6]);
    let mut fb = mb.function("copy_and_overlap", signature);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let src = fb.alloca(array.clone());
    let dst = fb.alloca(array.clone());
    let size = fb.uconst(Ty::Usize, u128::from(count));
    let fill = fb.uconst(Ty::U8, 7);
    fb.memset(src, fill, size);
    let mut expected = Vec::new();
    let mut values = Vec::new();
    if count == 0 {
        fb.memcopy(dst, src, size, false);
        for _ in 0..6 {
            values.push(fb.uconst(Ty::U8, 0));
            expected.push(byte(0));
        }
    } else {
        let last = fb.gep_byte_offset(src, count - 1);
        let replacement = fb.uconst(Ty::U8, 99);
        fb.store(Ty::U8, last, replacement);
        fb.memcopy(dst, src, size, false);
        for index in [0, count / 2, count - 1] {
            let pointer = fb.gep_byte_offset(dst, index);
            values.push(fb.load(Ty::U8, pointer));
            expected.push(byte(if index == count - 1 { 99 } else { 7 }));
        }
        let shifted = fb.gep_byte_offset(dst, 1);
        let moved = fb.uconst(Ty::Usize, u128::from(count - 1));
        fb.memcopy(shifted, dst, moved, true);
        for index in [0, count / 2, count - 1] {
            let pointer = fb.gep_byte_offset(dst, index);
            values.push(fb.load(Ty::U8, pointer));
            expected.push(byte(if count == 1 { 99 } else { 7 }));
        }
    }
    fb.ret(values);
    let copy = fb.build();
    let mut runs = vec![(copy, Expected::Values(expected))];

    let signature = mb.add_func_type(vec![], vec![Ty::U8]);
    let mut fb = mb.function("copy_erases_destination_init", signature);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let src = fb.alloca(array.clone());
    let dst = fb.alloca(array.clone());
    let size = fb.uconst(Ty::Usize, u128::from(count));
    let fill = fb.uconst(Ty::U8, 7);
    fb.memset(dst, fill, size);
    fb.memcopy(dst, src, size, false);
    let value = fb.load_volatile(Ty::U8, dst);
    fb.ret(vec![value]);
    runs.push((fb.build(), Expected::Ub));

    let signature = mb.add_func_type(vec![], vec![Ty::U8]);
    let mut fb = mb.function("bulk_range_must_fit_actual_allocation", signature);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let dst = fb.alloca(array);
    let size = fb.uconst(Ty::Usize, u128::from(count) + 1);
    let fill = fb.uconst(Ty::U8, 7);
    fb.memset(dst, fill, size);
    let zero = fb.uconst(Ty::U8, 0);
    fb.ret(vec![zero]);
    runs.push((fb.build(), Expected::Ub));

    let signature = mb.add_func_type(vec![], vec![Ty::U8; 3]);
    let mut fb = mb.function("zero_global_has_real_initialized_bytes", signature);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let pointer = fb.global_addr(GlobalId::new(0));
    let mut values = Vec::new();
    if count == 0 {
        for _ in 0..3 {
            values.push(fb.uconst(Ty::U8, 0));
        }
    } else {
        for index in [0, count / 2, count - 1] {
            let element = fb.gep_byte_offset(pointer, index);
            values.push(fb.load_volatile(Ty::U8, element));
        }
    }
    fb.ret(values);
    runs.push((fb.build(), Expected::Values(vec![byte(0); 3])));
    (mb.build().unwrap(), runs)
}

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

#[test]
fn compact_bulk_operations_retain_snapshots_init_states_and_source_bounds() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let counts = if bits == 32 {
            vec![0, 1, 17, (1u64 << 24) + 3]
        } else {
            vec![0, 1, 17, (1u64 << 32) + 17, (1u64 << 40) + 37]
        };
        for count in counts {
            let (module, runs) = module(bits, count);
            for decoded in codecs(module) {
                let errors = trust_ir_build::validate_module(&decoded);
                assert!(errors.is_empty(), "{bits}/{count}: {errors:?}");
                modules.push((decoded, runs.clone()));
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(module, runs)| Batch {
            label: module.name.clone(),
            module,
            runs: runs.iter().map(|(id, _)| (*id, vec![])).collect(),
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 180);
    for (report, (_, expected)) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, runs)| runs))
    {
        assert_eq!(
            report.comparison,
            Comparison::Agree,
            "compact bulk memory must preserve actual instruction behavior: {report:?}"
        );
        match expected {
            Expected::Values(values) => {
                assert_eq!(report.rust, Verdict::Ok(values.clone()), "{report:?}");
                assert_eq!(report.lean, Verdict::Ok(values.clone()), "{report:?}");
            }
            Expected::Ub => {
                assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
                assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
            }
        }
    }
    eprintln!("COMPACT_BULK_MEMORY_PASS 180 actual runs across both target widths and five codecs");
}

fn typed_module(bits: u32, count: u64) -> (Module, Vec<(FuncId, Vec<Val>)>) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("compact_typed_{bits}_{count}"),
        semr_target(bits),
    );
    let word_element = mb.add_type(Ty::U32);
    let byte_element = mb.add_type(Ty::U8);
    let words = Ty::Array(word_element, count);
    let bytes = Ty::Array(byte_element, 4 * count);
    mb.add_global(Global {
        name: "initialized_words".into(),
        ty: words.clone(),
        mutable: true,
        initializer: Some(trust_ir::constant::Constant::splat(
            trust_ir::constant::Constant::Int(0x0403_0201),
            count,
        )),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let signature = mb.add_func_type(
        vec![],
        vec![Ty::U32, Ty::U8, Ty::U8, Ty::U8, Ty::U8, Ty::U32],
    );
    let mut fb = mb.function("whole_typed_load_and_cross_width", signature);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let pointer = fb.alloca(words.clone());
    let unit = fb.uconst(Ty::U32, 0x0403_0201);
    let source = if count == 0 {
        fb.const_value(words.clone(), trust_ir::constant::Constant::Array(vec![]))
    } else {
        fb.array_splat(words.clone(), unit)
    };
    fb.store(words.clone(), pointer, source);
    let loaded = fb.load(words.clone(), pointer);
    let cross = fb.load(bytes, pointer);
    let mut returned = Vec::new();
    if count == 0 {
        returned.push(fb.uconst(Ty::U32, 0));
        for _ in 0..4 {
            returned.push(fb.uconst(Ty::U8, 0));
        }
        returned.push(fb.uconst(Ty::U32, 0));
    } else {
        let index = fb.uconst(Ty::Usize, u128::from(count / 2));
        returned.push(fb.extract_element(Ty::U32, loaded, index));
        for index in [0, 1, 2, 4 * count - 1] {
            let index = fb.uconst(Ty::Usize, u128::from(index));
            returned.push(fb.extract_element(Ty::U8, cross, index));
        }
        let last = fb.gep_byte_offset(pointer, 4 * count - 1);
        let replacement = fb.uconst(Ty::U8, 99);
        fb.store(Ty::U8, last, replacement);
        let changed = fb.load(words.clone(), pointer);
        let index = fb.uconst(Ty::Usize, u128::from(count - 1));
        returned.push(fb.extract_element(Ty::U32, changed, index));
    }
    fb.ret(returned);
    let normal = fb.build();
    let word = |raw| Val::Int { width: 32, raw };
    let expected = if count == 0 {
        vec![word(0), byte(0), byte(0), byte(0), byte(0), word(0)]
    } else {
        vec![
            word(0x0403_0201),
            byte(1),
            byte(2),
            byte(3),
            byte(4),
            word(0x6303_0201),
        ]
    };
    let signature = mb.add_func_type(vec![], vec![Ty::U32, Ty::U32, Ty::Bool, Ty::Bool]);
    let mut fb = mb.function("whole_typed_strong_exchange", signature);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let pointer = fb.alloca(words.clone());
    let seven = fb.uconst(Ty::U32, 7);
    let nine = fb.uconst(Ty::U32, 9);
    let expected_array = if count == 0 {
        fb.const_value(words.clone(), trust_ir::constant::Constant::Array(vec![]))
    } else {
        fb.array_splat(words.clone(), seven)
    };
    let desired_array = if count == 0 {
        fb.const_value(words.clone(), trust_ir::constant::Constant::Array(vec![]))
    } else {
        fb.array_splat(words.clone(), nine)
    };
    fb.store(words.clone(), pointer, expected_array);
    let (old, yes) = fb.cmpxchg(
        words.clone(),
        pointer,
        expected_array,
        desired_array,
        trust_ir::Ordering::SeqCst,
        trust_ir::Ordering::Relaxed,
    );
    let (_, again) = fb.cmpxchg(
        words.clone(),
        pointer,
        expected_array,
        desired_array,
        trust_ir::Ordering::SeqCst,
        trust_ir::Ordering::Relaxed,
    );
    let loaded = fb.load(words.clone(), pointer);
    let (old_lane, new_lane) = if count == 0 {
        (fb.uconst(Ty::U32, 0), fb.uconst(Ty::U32, 0))
    } else {
        let index = fb.uconst(Ty::Usize, u128::from(count - 1));
        (
            fb.extract_element(Ty::U32, old, index),
            fb.extract_element(Ty::U32, loaded, index),
        )
    };
    fb.ret(vec![old_lane, new_lane, yes, again]);
    let exchange = fb.build();
    let exchanged = vec![
        word(if count == 0 { 0 } else { 7 }),
        word(if count == 0 { 0 } else { 9 }),
        Val::Bool(true),
        Val::Bool(count == 0),
    ];
    let signature = mb.add_func_type(vec![], vec![Ty::U32; 3]);
    let mut fb = mb.function("initialized_typed_global", signature);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let pointer = fb.global_addr(GlobalId::new(0));
    let loaded = fb.load(words, pointer);
    let mut returned = Vec::new();
    if count == 0 {
        for _ in 0..3 {
            returned.push(fb.uconst(Ty::U32, 0));
        }
    } else {
        for index in [0, count / 2, count - 1] {
            let index = fb.uconst(Ty::Usize, u128::from(index));
            returned.push(fb.extract_element(Ty::U32, loaded, index));
        }
    }
    fb.ret(returned);
    let global = fb.build();
    let global_expected = vec![word(if count == 0 { 0 } else { 0x0403_0201 }); 3];
    (
        mb.build().unwrap(),
        vec![
            (normal, expected),
            (exchange, exchanged),
            (global, global_expected),
        ],
    )
}

#[test]
fn compact_typed_images_support_whole_loads_cross_width_and_strong_exchange() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let counts = if bits == 32 {
            vec![0, 1, 17, (1u64 << 24) + 3]
        } else {
            vec![0, 1, 17, (1u64 << 32) + 17, (1u64 << 40) + 37]
        };
        for count in counts {
            let (module, runs) = typed_module(bits, count);
            for decoded in codecs(module) {
                let errors = trust_ir_build::validate_module(&decoded);
                assert!(errors.is_empty(), "{bits}/{count}: {errors:?}");
                modules.push((decoded, runs.clone()));
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(module, runs)| Batch {
            label: module.name.clone(),
            module,
            runs: runs.iter().map(|(id, _)| (*id, vec![])).collect(),
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 135);
    for (report, (_, expected)) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, runs)| runs))
    {
        assert_eq!(
            report.comparison,
            Comparison::Agree,
            "compact typed memory must preserve actual instruction behavior: {report:?}"
        );
        assert_eq!(report.rust, Verdict::Ok(expected.clone()), "{report:?}");
        assert_eq!(report.lean, Verdict::Ok(expected.clone()), "{report:?}");
    }
    eprintln!(
        "COMPACT_TYPED_MEMORY_PASS 135 actual runs across both target widths and five codecs"
    );
}

// The input is a repeated nonuniform three-byte value, produced by actual
// typed stores and cross-width loads, rather than an observation-only fixture.
fn shared_periodic_module(bits: u32, count: u64) -> (Module, [FuncId; 2]) {
    use trust_ir::constant::Constant as C;
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("shared_periodic_{bits}_{count}"),
        semr_target(bits),
    );
    let byte = mb.add_type(Ty::U8);
    let unit = Ty::Array(byte, 3);
    let element = mb.add_type(unit.clone());
    let source = Ty::Array(element, count);
    let flat = Ty::Array(byte, 3 * count);
    let physical = mb.add_func_type(vec![flat.clone()], vec![flat.clone()]);
    let apparent = mb.add_func_type(vec![], vec![flat.clone()]);
    let closure = mb.add_closure_type(trust_ir::ty::ClosureTy {
        func: apparent,
        captures: vec![flat.clone()],
    });
    let identity = {
        let mut fb = mb.function("whole_array_identity", physical);
        let block = fb.create_block();
        let arg = fb.add_block_param(block, flat.clone());
        fb.switch_to_block(block);
        fb.ret(vec![arg]);
        fb.build()
    };
    let signature = mb.add_func_type(vec![], vec![flat.clone(), flat.clone()]);
    let mut fb = mb.function("periodic_whole_call_capture_store_reload", signature);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let unit_value = fb.const_value(
        unit.clone(),
        C::Array(vec![C::Int(1), C::Int(2), C::Int(3)]),
    );
    let repeated = fb.array_splat(source.clone(), unit_value);
    let pointer = fb.alloca(source.clone());
    fb.store(source.clone(), pointer, repeated);
    let original = fb.load(flat.clone(), pointer);
    let direct = fb.call(identity, vec![original]);
    let captured = fb.make_closure(closure, identity, vec![direct]);
    let returned = fb.call_indirect(captured, apparent, vec![]);
    let destination = fb.alloca(flat.clone());
    fb.store(flat.clone(), destination, returned);
    let reread = fb.load(flat.clone(), destination);
    fb.ret(vec![original, reread]);
    let normal = fb.build();

    let signature = mb.add_func_type(vec![], vec![flat.clone(), flat.clone(), Ty::Bool, Ty::Bool]);
    let mut fb = mb.function("periodic_whole_strong_exchange_late_difference", signature);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let unit_value = fb.const_value(unit, C::Array(vec![C::Int(1), C::Int(2), C::Int(3)]));
    let repeated = fb.array_splat(source.clone(), unit_value);
    let pointer = fb.alloca(source.clone());
    fb.store(source, pointer, repeated);
    let original = fb.load(flat.clone(), pointer);
    // Construct another storage path with equal contents; physical identity
    // cannot decide the exchange. The second exchange differs only at the end.
    let last = fb.uconst(Ty::Usize, u128::from(3 * count - 1));
    let three = fb.uconst(Ty::U8, 3);
    let expected = fb.insert_element(flat.clone(), original, last, three);
    let replacement = fb.uconst(Ty::U8, 99);
    let desired = fb.insert_element(flat.clone(), original, last, replacement);
    let (old, yes) = fb.cmpxchg(
        flat.clone(),
        pointer,
        expected,
        desired,
        trust_ir::Ordering::SeqCst,
        trust_ir::Ordering::Relaxed,
    );
    let (_, no) = fb.cmpxchg(
        flat.clone(),
        pointer,
        expected,
        original,
        trust_ir::Ordering::SeqCst,
        trust_ir::Ordering::Relaxed,
    );
    let current = fb.load(flat, pointer);
    fb.ret(vec![old, current, yes, no]);
    let exchange = fb.build();
    (mb.build().unwrap(), [normal, exchange])
}

fn expected_periodic_graph(count: u64, exchange: bool) -> super::compact_value_graph::Graph {
    use serde_json::json;
    // Independent repeat/concat specification of every element. This does
    // not reuse the interpreter's balanced tree or sample selected positions.
    let mut nodes = vec![
        json!(["int", 8, "1"]),
        json!(["int", 8, "2"]),
        json!(["int", 8, "3"]),
        json!(["nil"]),
        json!(["cons", 2, 3]),
        json!(["cons", 1, 4]),
        json!(["cons", 0, 5]),
        json!(["dense", 6]),
        json!(["repeat", 7, count.to_string()]),
        json!(["array", (3 * count).to_string(), 8]),
    ];
    let roots = if exchange {
        nodes.extend([
            json!(["int", 8, "99"]),
            json!(["cons", 10, 3]),
            json!(["cons", 1, 11]),
            json!(["cons", 0, 12]),
            json!(["dense", 13]),
            json!(["repeat", 7, (count - 1).to_string()]),
            json!(["concat", 15, 14]),
            json!(["array", (3 * count).to_string(), 16]),
            json!(["bool", true]),
            json!(["bool", false]),
        ]);
        vec![9, 17, 18, 19]
    } else {
        vec![9, 9]
    };
    super::compact_value_graph::Graph::decode(&json!({
        "graph": {"version": 2, "nodes": nodes, "roots": roots}
    }))
    .unwrap()
}

#[test]
fn shared_periodic_whole_results_cross_calls_closures_memory_and_exchange() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let counts = if bits == 32 {
            vec![1, 17, (1u64 << 24) + 3]
        } else {
            vec![1, 17, (1u64 << 32) + 17, (1u64 << 40) + 37]
        };
        for count in counts {
            let (module, roots) = shared_periodic_module(bits, count);
            for module in codecs(module) {
                let errors = trust_ir_build::validate_module(&module);
                assert!(errors.is_empty(), "{bits}/{count}: {errors:?}");
                modules.push((module, roots, count));
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = modules
        .iter()
        .map(|(module, roots, _)| Batch {
            label: module.name.clone(),
            module,
            runs: roots.iter().map(|&id| (id, vec![])).collect(),
        })
        .collect::<Vec<_>>();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 70);
    for (report, (count, exchange)) in reports.iter().zip(
        modules
            .iter()
            .flat_map(|(_, _, count)| [(*count, false), (*count, true)]),
    ) {
        assert_eq!(
            report.comparison,
            Comparison::Agree,
            "whole periodic execution must agree: {report:?}"
        );
        let expected = expected_periodic_graph(count, exchange);
        for verdict in [&report.rust, &report.lean] {
            let Verdict::Graph(actual) = verdict else {
                panic!("expected complete periodic graph: {verdict:?}")
            };
            assert!(
                actual.nodes().len() < 2048,
                "observation must retain actual sharing"
            );
            assert!(
                super::compact_graph_compare::equivalent(actual, &expected)
                    .unwrap()
                    .equal,
                "every returned periodic element and exchange flag must match: {report:?}"
            );
        }
    }
    eprintln!("SHARED_PERIODIC_IR_PASS 70 actual runs across both target widths and five codecs");
}
