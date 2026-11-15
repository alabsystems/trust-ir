// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real source/expanded callees, with independently decoded lexical tables.
//! The caller observes the stored resume state and its own live SSA sentinel.
//! Low gap names and a maximum u32 parameter exercise publication retirement.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use std::collections::BTreeSet;
use trust_ir::constant::Constant as C;
use trust_ir::inst::{AllocOrigin, CastOp};
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Inst, InstrNode, Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone)]
struct Run {
    function: FuncId,
    expected: Option<Vec<Val>>,
    pair: String,
    mutant: bool,
}

struct Leaf {
    function: FuncId,
    ids: [u32; 3],
    names: [u32; 3],
    payload: Ty,
    slot: u32,
    next: i64,
    expansion: u8,
}

fn int(width: u32, raw: u128) -> Val {
    Val::Int { width, raw }
}

fn cohort(bits: u32) -> (Module, Vec<Run>) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("generic_coro_{bits}"), semr_target(bits));
    let mut leaves = Vec::new();
    let mut runs = Vec::new();
    for (payload, constant, expected) in [
        (Ty::I32, C::Int(-5), int(32, u32::MAX as u128 - 4)),
        (Ty::Char, C::Int(0x10FFFF), int(32, 0x10FFFF)),
        (Ty::Bool, C::Bool(true), Val::Bool(true)),
        (Ty::F64, C::Float(2.5), Val::Float(2.5f64.to_bits())),
    ] {
        for ids in [[0, 1, 2], [42, 65537, 0], [u32::MAX, 0, 2]] {
            // Reserve an additional unused original parameter as well.
            // Extra blocks after a returning suspend are validator-refused.
            let occupied: BTreeSet<_> = ids.into_iter().chain([7]).collect();
            let names: Vec<_> = (0..=u32::MAX)
                .filter(|id| !occupied.contains(id))
                .take(3)
                .collect();
            let names: [u32; 3] = names.try_into().unwrap();
            assert_eq!(
                names,
                match ids {
                    [0, 1, 2] => [3, 4, 5],
                    [42, 65537, 0] => [1, 2, 3],
                    _ => [1, 3, 4],
                }
            );
            for mode in 0..9 {
                let slot = match mode {
                    1 | 5 => 2,
                    6 => 1,
                    8 => 3,
                    7 => u32::MAX,
                    _ => 0,
                };
                let next = match mode {
                    0 => i64::MIN,
                    1 => i64::MAX,
                    _ => 17,
                };
                let valid = matches!(mode, 0 | 1 | 6);
                let leaf_sig = mb.add_func_type(
                    vec![Ty::Ptr, payload.clone(), Ty::U64, Ty::U32],
                    vec![payload.clone()],
                );
                let caller_sig = mb.add_func_type(vec![], vec![payload.clone(), Ty::I64, Ty::U64]);
                let pair = format!("{payload:?}_{ids:?}_{mode}");
                for expansion in 0..if valid { 3 } else { 2 } {
                    // Placeholder body is replaced below with the exact raw
                    // source graph or the four-node checked expansion.
                    let mut fb = mb.function(format!("leaf_{pair}_{expansion}"), leaf_sig);
                    let entry = fb.create_block();
                    fb.add_block_param(entry, Ty::Ptr);
                    let value = fb.add_block_param(entry, payload.clone());
                    fb.add_block_param(entry, Ty::U64);
                    fb.add_block_param(entry, Ty::U32);
                    fb.switch_to_block(entry);
                    fb.ret(vec![value]);
                    let leaf = fb.build();
                    leaves.push(Leaf {
                        function: leaf,
                        ids,
                        names,
                        payload: payload.clone(),
                        slot,
                        next,
                        expansion,
                    });

                    let mut fb = mb.function(format!("caller_{pair}_{expansion}"), caller_sig);
                    let entry = fb.create_block();
                    fb.switch_to_block(entry);
                    let sentinel = fb.iconst(Ty::U64, 1234567);
                    let count = fb.iconst(Ty::I64, if mode == 1 { 3 } else { 1 });
                    let allocated =
                        fb.heap_alloc(Ty::I64, Some(count), None, AllocOrigin::RustHeap);
                    let pointer = match mode {
                        2 => fb.null_ptr(),
                        3 => fb.undef(Ty::Ptr),
                        5 => {
                            let address = fb.iconst(Ty::U64, 4096);
                            fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, address)
                        }
                        _ => allocated,
                    };
                    let value = if mode == 4 {
                        fb.undef(payload.clone())
                    } else {
                        fb.const_value(payload.clone(), constant.clone())
                    };
                    let unused = fb.iconst(Ty::U32, 99);
                    let result = fb.call(leaf, vec![pointer, value, sentinel, unused]);
                    let index = fb.iconst(Ty::I64, i128::from(slot));
                    let address = fb.gep(Ty::I64, allocated, vec![index]);
                    let stored = fb.load(Ty::I64, address);
                    fb.ret(vec![result, stored, sentinel]);
                    let stored = if expansion == 2 {
                        u64::from(slot)
                    } else {
                        next as u64
                    };
                    runs.push(Run {
                        function: fb.build(),
                        pair: pair.clone(),
                        mutant: expansion == 2,
                        expected: valid.then(|| {
                            vec![
                                expected.clone(),
                                int(64, u128::from(stored)),
                                int(64, 1234567),
                            ]
                        }),
                    });
                }
            }
        }
    }
    let mut module = mb.build().expect("placeholder graph validates");
    for leaf in leaves {
        let [frame, value, extra] = leaf.ids.map(ValueId::new);
        let [index, pointer, state] = leaf.names.map(ValueId::new);
        let mut entry = Block::new(BlockId::new(900));
        entry.params = vec![
            (frame, Ty::Ptr),
            (value, leaf.payload.clone()),
            (extra, Ty::U64),
            (ValueId::new(7), Ty::U32),
        ];
        entry.body = if leaf.expansion == 0 {
            vec![InstrNode::new(Inst::CoroSuspend {
                frame,
                state_slot: leaf.slot,
                next_state: leaf.next,
                value,
            })]
        } else {
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: C::Int(i128::from(leaf.slot)),
                })
                .with_result(index),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: frame,
                    indices: vec![index],
                    inbounds: false,
                })
                .with_result(pointer),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: C::Int(i128::from(leaf.next)),
                })
                .with_result(state),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: pointer,
                    value: if leaf.expansion == 2 { index } else { state },
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Return {
                    values: vec![value],
                }),
            ]
        };
        let function = module
            .functions
            .iter_mut()
            .find(|f| f.id == leaf.function)
            .unwrap();
        function.entry = entry.id;
        function.blocks = vec![entry];
    }
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "actual sparse graphs: {errors:?}");
    assert_eq!(runs.len(), 252);
    (module, runs)
}

fn codecs(module: Module) -> [(String, Module); 5] {
    let binary = trust_ir::binary::serialize_module(&module).unwrap();
    let text = trust_ir::format::text_checked(&module).unwrap();
    let json = serde_json::to_vec(&module).unwrap();
    let msgpack = rmp_serde::to_vec(&module).unwrap();
    [
        ("original".into(), module),
        (
            "binary".into(),
            trust_ir::binary::deserialize_module(&binary).unwrap(),
        ),
        (
            "text".into(),
            trust_ir::parser::parse_module(&text).unwrap(),
        ),
        ("JSON".into(), serde_json::from_slice(&json).unwrap()),
        (
            "MessagePack".into(),
            rmp_serde::from_slice(&msgpack).unwrap(),
        ),
    ]
}

#[test]
fn generic_coro_expansion_preserves_call_results_memory_and_sparse_names() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, runs) = cohort(bits);
        for (codec, decoded) in codecs(module) {
            let errors = trust_ir_build::validate_module(&decoded);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((
                format!("generic_coro_{bits}_{codec}"),
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
            runs: runs.iter().map(|run| (run.function, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 2520);
    let mut counts = (0, 0, 0);
    let (groups, remainder) = reports.as_chunks::<252>();
    assert!(remainder.is_empty());
    for (report, (_, _, runs)) in groups.iter().zip(&modules) {
        for (actual, run) in report.iter().zip(runs) {
            assert_eq!(
                actual.comparison,
                Comparison::Agree,
                "{}: {actual:?}",
                run.pair
            );
            if let Some(values) = &run.expected {
                assert_eq!(
                    actual.rust,
                    Verdict::Ok(values.clone()),
                    "{}: {actual:?}",
                    run.pair
                );
                assert_eq!(
                    actual.lean,
                    Verdict::Ok(values.clone()),
                    "{}: {actual:?}",
                    run.pair
                );
                if run.mutant {
                    counts.2 += 1;
                } else {
                    counts.0 += 1;
                }
            } else {
                assert!(
                    matches!(actual.rust, Verdict::Ub(_)),
                    "{}: {actual:?}",
                    run.pair
                );
                assert!(
                    matches!(actual.lean, Verdict::Ub(_)),
                    "{}: {actual:?}",
                    run.pair
                );
                counts.1 += 1;
            }
        }
        // Every admitted Store-wiring mutant has a different observable
        // state word from its source, while each engine executes it faithfully.
        for chunk in report.iter().zip(runs).collect::<Vec<_>>().windows(3) {
            if chunk[2].1.mutant {
                assert_eq!(chunk[0].0.rust, chunk[1].0.rust);
                assert_ne!(chunk[0].0.rust, chunk[2].0.rust);
            }
        }
    }
    assert_eq!(counts, (720, 1440, 360));
    println!(
        "generic Coro: 2520 runs; 720 source/target Ok, 1440 UB, 360 observable Store mutants"
    );
}
