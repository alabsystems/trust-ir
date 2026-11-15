// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant;
use trust_ir::inst::{CastOp, ICmpOp, Ordering};
use trust_ir::value::{FuncId, FuncTyId, GlobalId};
use trust_ir::{Global, Inst, Linkage, Module, Ty};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

fn scalar_function_memory(bits: u32, copy: bool) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("function_leaf_memory_{bits}_{copy}"),
        semr_target(bits),
    );
    let signature = mb.add_func_type(vec![], vec![Ty::U64]);
    let word_ty = if bits == 32 { Ty::U32 } else { Ty::U64 };
    let root_signature = mb.add_func_type(vec![], vec![Ty::U64, word_ty.clone()]);
    // An uncalled declaration occupies code address one. The leaf must use
    // source-table position two rather than a filtered executable-body index.
    mb.declare_function("unused", signature);
    let leaf = mb.declare_function("leaf", signature);
    let root = mb.declare_function("root", root_signature);
    {
        let mut fb = mb.define_function(leaf).unwrap();
        let block = fb.create_block();
        fb.switch_to_block(block);
        let answer = fb.uconst(Ty::U64, 42);
        fb.ret(vec![answer]);
        fb.build();
    }
    {
        let mut fb = mb.define_function(root).unwrap();
        let block = fb.create_block();
        fb.switch_to_block(block);
        let slot = fb.alloca(Ty::Func(signature));
        let code = fb.fn_addr(signature, leaf);
        fb.store(Ty::Func(signature), slot, code);
        let slot = if copy {
            let destination = fb.alloca(Ty::Func(signature));
            let length = fb.uconst(Ty::Usize, u128::from(bits / 8));
            fb.memcopy(destination, slot, length, false);
            destination
        } else {
            slot
        };
        let word = fb.load(word_ty, slot);
        let code = fb.load(Ty::Func(signature), slot);
        let answer = fb.call_indirect(code, signature, vec![]);
        fb.ret(vec![answer, word]);
        fb.build();
    }
    (mb.build().expect("function memory fixture"), root)
}

#[test]
fn scalar_function_store_load_and_copy_preserve_source_code_words() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        for copy in [false, true] {
            let (module, root) = scalar_function_memory(bits, copy);
            assert!(trust_ir_build::validate_module(&module).is_empty());
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
                assert!(errors.is_empty(), "{bits}/{copy}/{format}: {errors:?}");
                modules.push((
                    format!("function_memory_{bits}_{copy}_{format}"),
                    decoded,
                    root,
                    bits,
                ));
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, root, _)| Batch {
            label: label.clone(),
            module,
            runs: vec![(*root, vec![])],
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 20);
    for (report, (_, _, _, bits)) in reports.iter().zip(&modules) {
        let expected = Verdict::Ok(vec![
            Val::Int { width: 64, raw: 42 },
            Val::Int {
                width: *bits,
                raw: 2,
            },
        ]);
        assert_eq!(report.rust, expected, "{report:?}");
        assert_eq!(report.lean, expected, "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

#[derive(Clone)]
enum FunctionMemoryExpected {
    Ok(Vec<Val>),
    Ub,
    TypeError,
    DeclarationCall,
    WeakCmpXchg,
}

#[derive(Clone)]
struct FunctionMemoryRun {
    name: &'static str,
    root: FuncId,
    expected: FunctionMemoryExpected,
}

fn function_memory_id(id: FuncId, sparse: bool) -> FuncId {
    if !sparse {
        return FuncId::new(match id.index() {
            1 => 3,
            3 => 1,
            other => other,
        });
    }
    FuncId::new(match id.index() {
        0 => 17,
        1 => u32::MAX,
        2 => 3,
        3 => 65_537,
        other => 1000 + 17 * other,
    })
}

fn function_memory_value(signature: FuncTyId, target: FuncId, sparse: bool) -> Val {
    Val::Function {
        signature: signature.index(),
        func: function_memory_id(target, sparse).index(),
    }
}

fn function_memory_word(bits: u32, raw: u128) -> Val {
    Val::Int { width: bits, raw }
}

fn function_memory_root(
    mb: &mut ModuleBuilder,
    name: &str,
    returns: Vec<Ty>,
    body: impl FnOnce(&mut FunctionBuilder<'_>),
) -> FuncId {
    let signature = mb.add_func_type(vec![], returns);
    let mut fb = mb.function(name, signature);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    body(&mut fb);
    fb.build()
}

/// Remap only the constant forms this fixture constructs, never a callee's
/// signature. Code words remain positions in the original function vector.
fn function_memory_remap_constant(constant: &mut Constant, sparse: bool) {
    match constant {
        Constant::FnDef(target) => *target = function_memory_id(*target, sparse),
        Constant::Sequence(values) => {
            for value in values {
                function_memory_remap_constant(value, sparse);
            }
        }
        _ => {}
    }
}

fn expanded_function_memory(bits: u32, sparse: bool) -> (Module, Vec<FunctionMemoryRun>) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("expanded_function_memory_{bits}"),
        semr_target(bits),
    );
    let function_value = |signature, target| function_memory_value(signature, target, sparse);
    let signature = mb.add_func_type(vec![], vec![Ty::U64]);
    let same_shape = mb.add_func_type(vec![], vec![Ty::U64]);
    let wrong_shape = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    assert_ne!(signature, same_shape);
    let function_ty = Ty::Func(signature);
    let word_ty = if bits == 32 { Ty::U32 } else { Ty::U64 };
    // After the explicit swap below, the source slots are:
    // unused declaration=1, leaf B=2, declared-only=3, leaf A=4.
    // The sparse variant keeps ids [17,65537,3,MAX], neither dense nor sorted.
    // The canonical variant uses source-table indices and admits checked text.
    mb.declare_function("unused", signature);
    let leaf_a = mb.declare_function("leaf_a", signature);
    let declaration = mb.declare_function("declared_only", signature);
    let leaf_b = mb.declare_function("leaf_b", signature);
    for (leaf, answer) in [(leaf_a, 42), (leaf_b, 73)] {
        let mut fb = mb.define_function(leaf).unwrap();
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let answer = fb.uconst(Ty::U64, answer);
        fb.ret(vec![answer]);
        fb.build();
    }
    let element = mb.add_type(function_ty.clone());
    let sequence_ty = Ty::Sequence(element);
    let fwd_signature = mb.add_func_type(vec![Ty::RefMut(Box::new(function_ty.clone()))], vec![]);
    let mut fwds = Vec::new();
    for replace in [false, true] {
        let mut fb = mb.function(format!("map_function_{replace}"), fwd_signature);
        let entry = fb.create_block();
        let cell = fb.add_block_param(entry, Ty::RefMut(Box::new(function_ty.clone())));
        fb.switch_to_block(entry);
        let cell = fb.borrow_mut(cell);
        if replace {
            let code = fb.fn_addr(signature, leaf_b);
            fb.store(function_ty.clone(), cell, code);
        } else {
            fb.load(function_ty.clone(), cell);
        }
        fb.end_borrow(cell);
        fb.ret(vec![]);
        fwds.push(fb.build());
    }
    let forward_signature = mb.add_func_type(vec![function_ty.clone()], vec![Ty::U64]);
    let forward = {
        let mut fb = mb.function("forward_through_function_cell", forward_signature);
        let entry = fb.create_block();
        let code = fb.add_block_param(entry, function_ty.clone());
        fb.switch_to_block(entry);
        let cell = fb.alloca(function_ty.clone());
        fb.store(function_ty.clone(), cell, code);
        let loaded = fb.load(function_ty.clone(), cell);
        let answer = fb.call_indirect(loaded, signature, vec![]);
        fb.ret(vec![answer]);
        fb.build()
    };
    // Global ids are their declared append positions; all layout metadata is
    // the actual Func type/signature, not an inferred size or byte initializer.
    for (name, initializer, mutable) in [
        ("FUNCTION", Some(Constant::FnDef(leaf_a)), false),
        ("BSS_FUNCTION", None, true),
        ("DECLARATION", Some(Constant::FnDef(declaration)), false),
    ] {
        mb.add_global(Global {
            name: name.into(),
            ty: function_ty.clone(),
            initializer,
            mutable,
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
    }
    let mut runs = Vec::new();
    macro_rules! case {
        ($name:literal, $returns:expr, $expected:expr, $body:expr) => {
            runs.push(FunctionMemoryRun {
                name: $name,
                root: function_memory_root(&mut mb, $name, $returns, $body),
                expected: $expected,
            });
        };
    }
    for copy in [false, true] {
        let name = if copy {
            "source_order_copy_call_word"
        } else {
            "source_order_store_call_word"
        };
        let root = function_memory_root(&mut mb, name, vec![Ty::U64, word_ty.clone()], |fb| {
            let slot = fb.alloca(function_ty.clone());
            let code = fb.fn_addr(signature, leaf_a);
            fb.store(function_ty.clone(), slot, code);
            let slot = if copy {
                let destination = fb.alloca(function_ty.clone());
                let length = fb.uconst(Ty::Usize, u128::from(bits / 8));
                fb.memcopy(destination, slot, length, false);
                destination
            } else {
                slot
            };
            let word = fb.load(word_ty.clone(), slot);
            let loaded = fb.load(function_ty.clone(), slot);
            let answer = fb.call_indirect(loaded, signature, vec![]);
            fb.ret(vec![answer, word]);
        });
        runs.push(FunctionMemoryRun {
            name,
            root,
            expected: FunctionMemoryExpected::Ok(vec![
                function_memory_word(64, 42),
                function_memory_word(bits, 4),
            ]),
        });
    }
    for (name, word, leaf, answer) in [
        ("registered_word_a", 4, leaf_a, 42),
        ("registered_word_b", 2, leaf_b, 73),
    ] {
        let root = function_memory_root(&mut mb, name, vec![function_ty.clone(), Ty::U64], |fb| {
            let slot = fb.alloca(function_ty.clone());
            let word = fb.uconst(word_ty.clone(), word);
            fb.store(word_ty.clone(), slot, word);
            let code = fb.load(function_ty.clone(), slot);
            let answer = fb.call_indirect(code, signature, vec![]);
            fb.ret(vec![code, answer]);
        });
        runs.push(FunctionMemoryRun {
            name,
            root,
            expected: FunctionMemoryExpected::Ok(vec![
                function_value(signature, leaf),
                function_memory_word(64, answer),
            ]),
        });
    }
    case!(
        "declaration_transport",
        vec![function_ty.clone(), word_ty.clone()],
        FunctionMemoryExpected::Ok(vec![
            function_value(signature, declaration),
            function_memory_word(bits, 3)
        ]),
        |fb| {
            let slot = fb.alloca(function_ty.clone());
            let code = fb.fn_addr(signature, declaration);
            fb.store(function_ty.clone(), slot, code);
            let code = fb.load(function_ty.clone(), slot);
            let word = fb.load(word_ty.clone(), slot);
            fb.ret(vec![code, word]);
        }
    );
    case!(
        "parameter_forward",
        vec![Ty::U64],
        FunctionMemoryExpected::Ok(vec![function_memory_word(64, 42)]),
        |fb| {
            let code = fb.fn_addr(signature, leaf_a);
            let answer = fb.call(forward, vec![code]);
            fb.ret(vec![answer]);
        }
    );
    for (name, loaded_sig, call) in [
        ("retyped_signature_without_call", wrong_shape, false),
        ("distinct_same_shape_signature_call", same_shape, true),
    ] {
        let mut returns = vec![Ty::Func(loaded_sig)];
        let mut expected = vec![function_value(loaded_sig, leaf_a)];
        if call {
            returns.push(Ty::U64);
            expected.push(function_memory_word(64, 42));
        }
        let root = function_memory_root(&mut mb, name, returns, |fb| {
            let slot = fb.alloca(function_ty.clone());
            let code = fb.fn_addr(signature, leaf_a);
            fb.store(function_ty.clone(), slot, code);
            let code = fb.load(Ty::Func(loaded_sig), slot);
            let mut values = vec![code];
            if call {
                values.push(fb.call_indirect(code, loaded_sig, vec![]));
            }
            fb.ret(values);
        });
        runs.push(FunctionMemoryRun {
            name,
            root,
            expected: FunctionMemoryExpected::Ok(expected),
        });
    }
    case!(
        "global_function_cache",
        vec![Ty::Bool, word_ty.clone(), Ty::U64, function_ty.clone()],
        FunctionMemoryExpected::Ok(vec![
            Val::Bool(true),
            function_memory_word(bits, 4),
            function_memory_word(64, 42),
            function_value(signature, leaf_a)
        ]),
        |fb| {
            let first = fb.global_addr(GlobalId::new(0));
            let second = fb.global_addr(GlobalId::new(0));
            let same = fb.icmp(ICmpOp::Eq, Ty::Ptr, first, second);
            let word = fb.load(word_ty.clone(), first);
            let code = fb.load(function_ty.clone(), second);
            let answer = fb.call_indirect(code, signature, vec![]);
            fb.ret(vec![same, word, answer, code]);
        }
    );
    case!(
        "global_bss_null",
        vec![word_ty.clone(), function_ty.clone()],
        FunctionMemoryExpected::Ok(vec![function_memory_word(bits, 0), Val::Ptr { null: true }]),
        |fb| {
            let slot = fb.global_addr(GlobalId::new(1));
            let word = fb.load(word_ty.clone(), slot);
            let code = fb.load(function_ty.clone(), slot);
            fb.ret(vec![word, code]);
        }
    );
    case!(
        "global_bss_store_cached",
        vec![word_ty.clone(), Ty::U64],
        FunctionMemoryExpected::Ok(vec![
            function_memory_word(bits, 2),
            function_memory_word(64, 73)
        ]),
        |fb| {
            let slot = fb.global_addr(GlobalId::new(1));
            let code = fb.fn_addr(signature, leaf_b);
            fb.store(function_ty.clone(), slot, code);
            let cached = fb.global_addr(GlobalId::new(1));
            let word = fb.load(word_ty.clone(), cached);
            let code = fb.load(function_ty.clone(), cached);
            let answer = fb.call_indirect(code, signature, vec![]);
            fb.ret(vec![word, answer]);
        }
    );
    case!(
        "global_declaration_transport",
        vec![function_ty.clone(), word_ty.clone()],
        FunctionMemoryExpected::Ok(vec![
            function_value(signature, declaration),
            function_memory_word(bits, 3)
        ]),
        |fb| {
            let slot = fb.global_addr(GlobalId::new(2));
            let code = fb.load(function_ty.clone(), slot);
            let word = fb.load(word_ty.clone(), slot);
            fb.ret(vec![code, word]);
        }
    );
    case!(
        "atomic_function_store_load",
        vec![word_ty.clone(), Ty::U64, function_ty.clone()],
        FunctionMemoryExpected::Ok(vec![
            function_memory_word(bits, 4),
            function_memory_word(64, 42),
            function_value(signature, leaf_a)
        ]),
        |fb| {
            let slot = fb.alloca(function_ty.clone());
            let code = fb.fn_addr(signature, leaf_a);
            fb.atomic_store(function_ty.clone(), slot, code, Ordering::Release);
            let code = fb.atomic_load(function_ty.clone(), slot, Ordering::Acquire);
            let answer = fb.call_indirect(code, signature, vec![]);
            let word = fb.load(word_ty.clone(), slot);
            fb.ret(vec![word, answer, code]);
        }
    );
    case!(
        "atomic_null_transport",
        vec![word_ty.clone(), function_ty.clone()],
        FunctionMemoryExpected::Ok(vec![function_memory_word(bits, 0), Val::Ptr { null: true }]),
        |fb| {
            let source = fb.alloca(function_ty.clone());
            let zero = fb.uconst(word_ty.clone(), 0);
            fb.store(word_ty.clone(), source, zero);
            let null = fb.load(function_ty.clone(), source);
            let slot = fb.alloca(function_ty.clone());
            fb.atomic_store(function_ty.clone(), slot, null, Ordering::SeqCst);
            let code = fb.atomic_load(function_ty.clone(), slot, Ordering::SeqCst);
            let word = fb.load(word_ty.clone(), slot);
            fb.ret(vec![word, code]);
        }
    );
    for (name, mode) in [
        ("cmpxchg_success", 0),
        ("cmpxchg_reject", 1),
        ("cmpxchg_null_success", 2),
        ("cmpxchg_null_reject", 3),
        ("cmpxchg_null_null", 4),
    ] {
        let null = Val::Ptr { null: true };
        let old = if mode >= 2 && mode != 3 {
            null.clone()
        } else {
            function_value(signature, leaf_a)
        };
        let (success, now, word) = match mode {
            0 => (true, function_value(signature, leaf_b), 2),
            1 | 3 => (false, function_value(signature, leaf_a), 4),
            2 => (true, function_value(signature, leaf_a), 4),
            _ => (true, null, 0),
        };
        let root = function_memory_root(
            &mut mb,
            name,
            vec![
                function_ty.clone(),
                Ty::Bool,
                function_ty.clone(),
                word_ty.clone(),
            ],
            |fb| {
                let null_slot = fb.alloca(function_ty.clone());
                let zero = fb.uconst(word_ty.clone(), 0);
                fb.store(word_ty.clone(), null_slot, zero);
                let null = fb.load(function_ty.clone(), null_slot);
                let a = fb.fn_addr(signature, leaf_a);
                let b = fb.fn_addr(signature, leaf_b);
                let initial = if mode >= 2 && mode != 3 { null } else { a };
                let expected = match mode {
                    0 => a,
                    1 => b,
                    _ => null,
                };
                let desired = match mode {
                    0 | 1 | 3 => b,
                    2 => a,
                    _ => null,
                };
                let slot = fb.alloca(function_ty.clone());
                fb.store(function_ty.clone(), slot, initial);
                let (old, success) = fb.cmpxchg(
                    function_ty.clone(),
                    slot,
                    expected,
                    desired,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                );
                let now = fb.load(function_ty.clone(), slot);
                let word = fb.load(word_ty.clone(), slot);
                fb.ret(vec![old, success, now, word]);
            },
        );
        runs.push(FunctionMemoryRun {
            name,
            root,
            expected: FunctionMemoryExpected::Ok(vec![
                old,
                Val::Bool(success),
                now,
                function_memory_word(bits, word),
            ]),
        });
    }
    let mut seqmaps = Vec::new();
    for (name, fwd, empty, replacement) in [
        ("seqmap_identity_functions", fwds[0], false, false),
        ("seqmap_replace_functions", fwds[1], false, true),
        ("seqmap_empty_functions", fwds[1], true, true),
    ] {
        let values = if empty {
            vec![]
        } else if replacement {
            vec![function_value(signature, leaf_b); 3]
        } else {
            vec![
                function_value(signature, leaf_a),
                function_value(signature, leaf_b),
                function_value(signature, declaration),
            ]
        };
        let root = function_memory_root(&mut mb, name, vec![sequence_ty.clone()], |fb| {
            let values = if empty {
                vec![]
            } else {
                vec![
                    Constant::FnDef(leaf_a),
                    Constant::FnDef(leaf_b),
                    Constant::FnDef(declaration),
                ]
            };
            let sequence = fb.const_value(sequence_ty.clone(), Constant::Sequence(values));
            let mapped = fb.copy(sequence_ty.clone(), sequence);
            fb.ret(vec![mapped]);
        });
        seqmaps.push((root, fwd));
        runs.push(FunctionMemoryRun {
            name,
            root,
            expected: FunctionMemoryExpected::Ok(vec![Val::Sequence(values)]),
        });
    }
    assert_eq!(runs.len(), 22);
    // Func is not a partial-byte scalar. Discarding a plain/atomic load's
    // result still faults at that load, including an only-partly written word.
    for (name, atomic, partial) in [
        ("uninit_plain_func", false, false),
        ("uninit_atomic_func", true, false),
        ("partial_plain_func", false, true),
        ("partial_atomic_func", true, true),
    ] {
        let root = function_memory_root(&mut mb, name, vec![], |fb| {
            let slot = fb.alloca(function_ty.clone());
            if partial {
                let byte = fb.uconst(Ty::U8, 0);
                fb.store(Ty::U8, slot, byte);
            }
            if atomic {
                fb.atomic_load(function_ty.clone(), slot, Ordering::SeqCst);
            } else {
                fb.load(function_ty.clone(), slot);
            }
            fb.ret(vec![]);
        });
        runs.push(FunctionMemoryRun {
            name,
            root,
            expected: FunctionMemoryExpected::Ub,
        });
    }
    // Func has no scalar poison carrier. This faults at Undef even when its
    // result is ignored or merely offered to a non-strict Store.
    for (name, store) in [("undef_func_ignored", false), ("undef_func_store", true)] {
        let root = function_memory_root(&mut mb, name, vec![Ty::U64], |fb| {
            let value = fb.undef(function_ty.clone());
            if store {
                let slot = fb.alloca(function_ty.clone());
                fb.store(function_ty.clone(), slot, value);
            }
            let answer = fb.uconst(Ty::U64, 42);
            fb.ret(vec![answer]);
        });
        runs.push(FunctionMemoryRun {
            name,
            root,
            expected: FunctionMemoryExpected::Ub,
        });
    }
    for (name, mode) in [
        ("unknown_code_word", 0),
        ("data_address_as_code_word", 1),
        ("null_loaded_call", 2),
        ("loaded_signature_mismatch", 3),
        ("loaded_declaration_call", 4),
    ] {
        let root = function_memory_root(&mut mb, name, vec![], |fb| {
            let slot = fb.alloca(function_ty.clone());
            let word = match mode {
                1 => {
                    let data = fb.alloca(Ty::U8);
                    fb.cast(CastOp::PtrToInt, Ty::Ptr, word_ty.clone(), data)
                }
                _ => fb.uconst(
                    word_ty.clone(),
                    match mode {
                        0 => 999_999,
                        2 => 0,
                        4 => 3,
                        _ => 4,
                    },
                ),
            };
            fb.store(word_ty.clone(), slot, word);
            let loaded_sig = if mode == 3 { wrong_shape } else { signature };
            let code = fb.load(Ty::Func(loaded_sig), slot);
            if mode >= 2 {
                let args = if mode == 3 {
                    vec![fb.uconst(Ty::U64, 0)]
                } else {
                    vec![]
                };
                fb.call_indirect(code, loaded_sig, args);
            }
            fb.ret(vec![]);
        });
        runs.push(FunctionMemoryRun {
            name,
            root,
            expected: if mode == 4 {
                FunctionMemoryExpected::DeclarationCall
            } else {
                FunctionMemoryExpected::TypeError
            },
        });
    }
    let weak_root = function_memory_root(&mut mb, "weak_function_cmpxchg", vec![Ty::Bool], |fb| {
        let slot = fb.alloca(function_ty.clone());
        let a = fb.fn_addr(signature, leaf_a);
        let b = fb.fn_addr(signature, leaf_b);
        fb.store(function_ty.clone(), slot, a);
        let (_, success) = fb.cmpxchg(
            function_ty.clone(),
            slot,
            a,
            b,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        fb.ret(vec![success]);
    });
    runs.push(FunctionMemoryRun {
        name: "weak_function_cmpxchg",
        root: weak_root,
        expected: FunctionMemoryExpected::WeakCmpXchg,
    });
    let mut module = mb.build().expect("expanded function memory fixture");
    for (root, fwd) in seqmaps {
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
        assert_eq!(replaced, 1, "retain the actual result destination");
    }
    for node in &mut module.function_by_id_mut(weak_root).unwrap().blocks[0].body {
        if let Inst::CmpXchg { weak, .. } = &mut node.inst {
            *weak = true;
        }
    }
    for function in &mut module.functions {
        function.id = function_memory_id(function.id, sparse);
        for block in &mut function.blocks {
            for node in &mut block.body {
                match &mut node.inst {
                    Inst::Const { value, .. } => function_memory_remap_constant(value, sparse),
                    Inst::Call { callee, .. } => *callee = function_memory_id(*callee, sparse),
                    Inst::SeqMap { fwd, .. } => *fwd = function_memory_id(*fwd, sparse),
                    _ => {}
                }
            }
        }
    }
    for global in &mut module.globals {
        if let Some(value) = &mut global.initializer {
            function_memory_remap_constant(value, sparse);
        }
    }
    module.functions.swap(1, 3);
    assert_eq!(
        module.functions[..4]
            .iter()
            .map(|f| f.id.index())
            .collect::<Vec<_>>(),
        if sparse {
            [17, 65_537, 3, u32::MAX]
        } else {
            [0, 1, 2, 3]
        }
    );
    for run in &mut runs {
        run.root = function_memory_id(run.root, sparse);
    }
    assert_eq!(runs.len(), 34);
    (module, runs)
}

fn function_memory_cold_variants(module: Module, sparse: bool) -> Vec<(&'static str, Module)> {
    let binary = trust_ir::binary::serialize_module(&module).expect("encode binary");
    let text = if sparse {
        let error = trust_ir::format::text_checked(&module)
            .expect_err("checked text cannot preserve non-positional function ids");
        let expected: Vec<_> = module
            .functions
            .iter()
            .enumerate()
            .filter_map(|(index, function)| {
                let index = u32::try_from(index).unwrap();
                (function.id.index() != index).then_some(trust_ir::format::TextLoss::FunctionId {
                    index,
                    id: function.id,
                })
            })
            .collect();
        assert_eq!(error.losses, expected);
        None
    } else {
        Some(trust_ir::format::text_checked(&module).expect("encode canonical-id text"))
    };
    let json = serde_json::to_vec(&module).expect("encode JSON");
    let msgpack = rmp_serde::to_vec(&module).expect("encode MessagePack");
    let mut variants = vec![
        ("original", module),
        (
            "binary",
            trust_ir::binary::deserialize_module(&binary).expect("decode binary"),
        ),
        ("JSON", serde_json::from_slice(&json).expect("decode JSON")),
        (
            "MessagePack",
            rmp_serde::from_slice(&msgpack).expect("decode MessagePack"),
        ),
    ];
    if let Some(text) = text {
        variants.insert(
            2,
            (
                "text",
                trust_ir::parser::parse_module(&text).expect("decode text"),
            ),
        );
    }
    assert_eq!(variants.len(), if sparse { 4 } else { 5 });
    variants
}

#[test]
fn function_memory_consumers_keep_source_order_and_dynamic_refusals_across_codecs() {
    let mut modules = Vec::new();
    for (bits, sparse) in [32, 64]
        .into_iter()
        .flat_map(|bits| [false, true].map(|sparse| (bits, sparse)))
    {
        let (module, runs) = expanded_function_memory(bits, sparse);
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{bits}/original: {errors:?}");
        for (codec, decoded) in function_memory_cold_variants(module, sparse) {
            let errors = trust_ir_build::validate_module(&decoded);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            assert_eq!(
                decoded.functions[..4]
                    .iter()
                    .map(|f| f.id.index())
                    .collect::<Vec<_>>(),
                if sparse {
                    [17, 65_537, 3, u32::MAX]
                } else {
                    [0, 1, 2, 3]
                },
                "{bits}/{sparse}/{codec}: preserve source slots"
            );
            modules.push((
                format!("function_memory_expanded_{bits}_{sparse}_{codec}"),
                decoded,
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
            runs: runs.iter().map(|run| (run.root, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 612);
    let mut counts = [0; 5];
    for (report, run) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, runs)| runs))
    {
        match &run.expected {
            FunctionMemoryExpected::Ok(values) => {
                let expected = Verdict::Ok(values.clone());
                assert_eq!(report.rust, expected, "{}: {report:?}", run.name);
                assert_eq!(report.lean, expected, "{}: {report:?}", run.name);
                assert_eq!(
                    report.comparison,
                    Comparison::Agree,
                    "{}: {report:?}",
                    run.name
                );
                counts[0] += 1;
            }
            FunctionMemoryExpected::Ub => {
                assert!(
                    matches!(report.rust, Verdict::Ub(_)),
                    "{}: {report:?}",
                    run.name
                );
                assert!(
                    matches!(report.lean, Verdict::Ub(_)),
                    "{}: {report:?}",
                    run.name
                );
                assert_eq!(
                    report.comparison,
                    Comparison::Agree,
                    "{}: {report:?}",
                    run.name
                );
                counts[1] += 1;
            }
            FunctionMemoryExpected::TypeError => {
                // These validated programs forge or misapply code words at
                // runtime. The global harness deliberately never calls two
                // TypeErrors agreement; check this paired refusal explicitly.
                assert!(
                    matches!(report.rust, Verdict::TypeError(_)),
                    "{}: {report:?}",
                    run.name
                );
                assert!(
                    matches!(report.lean, Verdict::TypeError(_)),
                    "{}: {report:?}",
                    run.name
                );
                assert!(
                    matches!(report.comparison, Comparison::Mismatch(_)),
                    "{report:?}"
                );
                counts[2] += 1;
            }
            FunctionMemoryExpected::DeclarationCall => {
                assert_eq!(
                    report.rust,
                    Verdict::Unsupported("unsupported_call".into()),
                    "{report:?}"
                );
                assert_eq!(
                    report.lean,
                    Verdict::Unsupported("interprocedural_call".into()),
                    "{report:?}"
                );
                assert_eq!(
                    report.comparison,
                    Comparison::Unsupported("rust", "unsupported_call".into()),
                    "{report:?}"
                );
                counts[3] += 1;
            }
            FunctionMemoryExpected::WeakCmpXchg => {
                assert!(
                    matches!(&report.rust, Verdict::TypeError(message) if message.contains("weak")),
                    "{report:?}"
                );
                assert_eq!(
                    report.lean,
                    Verdict::Unsupported("weak_cmpxchg".into()),
                    "{report:?}"
                );
                assert_eq!(
                    report.comparison,
                    Comparison::Unsupported("lean", "weak_cmpxchg".into()),
                    "{report:?}"
                );
                counts[4] += 1;
            }
        }
    }
    assert_eq!(counts, [396, 108, 72, 18, 18]);
}

#[test]
fn malformed_function_memory_values_refuse_after_valid_codec_transport() {
    let mut modules = Vec::new();
    for (bits, sparse) in [32, 64]
        .into_iter()
        .flat_map(|bits| [false, true].map(|sparse| (bits, sparse)))
    {
        let (module, runs) = expanded_function_memory(bits, sparse);
        let store = runs
            .iter()
            .find(|run| run.name == "source_order_store_call_word")
            .unwrap()
            .root;
        let global = runs
            .iter()
            .find(|run| run.name == "global_function_cache")
            .unwrap()
            .root;
        assert!(trust_ir_build::validate_module(&module).is_empty());
        for (codec, decoded) in function_memory_cold_variants(module, sparse) {
            assert!(trust_ir_build::validate_module(&decoded).is_empty());
            // The codec transported a valid seed. The following separate raw
            // runtime mutations carry no producer/module-validation claim.
            for mutation in 0..3 {
                let mut malformed = decoded.clone();
                let root = if mutation == 2 { global } else { store };
                match mutation {
                    0 => {
                        let mut changed = 0;
                        for node in &mut malformed.function_by_id_mut(root).unwrap().blocks[0].body
                        {
                            if let Inst::Const {
                                value: Constant::FnDef(target),
                                ..
                            } = &mut node.inst
                            {
                                *target = FuncId::new(u32::MAX - 1);
                                changed += 1;
                            }
                        }
                        assert_eq!(changed, 1);
                    }
                    1 => {
                        let wrong = malformed
                            .func_types
                            .iter()
                            .position(|sig| sig.params == [Ty::U64] && sig.returns == [Ty::U64])
                            .unwrap();
                        let wrong = FuncTyId::new(u32::try_from(wrong).unwrap());
                        let mut changed = 0;
                        for node in &mut malformed.function_by_id_mut(root).unwrap().blocks[0].body
                        {
                            if let Inst::Store { ty, .. } = &mut node.inst {
                                *ty = Ty::Func(wrong);
                                changed += 1;
                            }
                        }
                        assert_eq!(changed, 1);
                    }
                    _ => {
                        malformed.globals[0].initializer =
                            Some(Constant::FnDef(FuncId::new(u32::MAX - 1)))
                    }
                }
                let errors = trust_ir_build::validate_module(&malformed);
                assert!(
                    !errors.is_empty(),
                    "{bits}/{codec}/{mutation}: raw malformed input"
                );
                modules.push((
                    format!(
                        "function_memory_postdecode_malformed_{bits}_{sparse}_{codec}_{mutation}"
                    ),
                    malformed,
                    root,
                ));
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, root)| Batch {
            label: label.clone(),
            module,
            runs: vec![(*root, vec![])],
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 54);
    for report in reports {
        assert!(matches!(report.rust, Verdict::TypeError(_)), "{report:?}");
        assert!(matches!(report.lean, Verdict::TypeError(_)), "{report:?}");
        assert!(
            matches!(report.comparison, Comparison::Mismatch(_)),
            "{report:?}"
        );
    }
}
