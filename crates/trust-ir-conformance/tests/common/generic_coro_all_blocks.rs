// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Connected all-block and module factory evidence. The kernel theorem states
//! framed call equality; these are ordinary unverified execution controls.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use std::path::{Path, PathBuf};
use trust_ir::constant::Constant as C;
use trust_ir::inst::{AllocOrigin, BinOp, ICmpOp, SwitchCase};
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Inst, InstrNode, Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy, Debug)]
enum Family {
    Br,
    CondBr,
    Switch,
    SeqMapSwitch,
}

#[derive(Clone, Copy, Debug)]
enum Variant {
    Source,
    Correct,
    WrongStore,
    WrongIndex,
}

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}

fn int(width: u32, raw: u128) -> Val {
    Val::Int { width, raw }
}

fn evidence_dir() -> PathBuf {
    std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir()
                .join(".ubd")
                .join(format!("coro-all-blocks-{}", std::process::id()))
        })
}

fn module(bits: u32, family: Family, identity: bool) -> (Module, FuncId, Vec<FuncId>) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("coro_all_blocks_{bits}_{family:?}_{identity}"),
        semr_target(bits),
    );
    let element = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    let element_id = mb.add_type(element.clone());
    let sequence = Ty::Sequence(element_id);
    let mapped = matches!(family, Family::SeqMapSwitch);
    let value_ty = if mapped { sequence.clone() } else { Ty::I32 };
    let signature = mb.add_func_type(
        vec![Ty::Ptr, value_ty.clone(), Ty::U32, Ty::I64],
        vec![value_ty.clone()],
    );
    let selected = {
        let mut fb = mb.function("selected", signature);
        let entry = fb.create_block();
        fb.add_block_param(entry, Ty::Ptr);
        let value = fb.add_block_param(entry, value_ty.clone());
        fb.add_block_param(entry, Ty::U32);
        fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        fb.ret(vec![value]);
        fb.build()
    };
    let helper = if mapped {
        let reference = Ty::RefMut(Box::new(element.clone()));
        let signature = mb.add_func_type(vec![reference.clone()], vec![]);
        let mut fb = mb.function("forward", signature);
        let entry = fb.create_block();
        let pointer = fb.add_block_param(entry, reference);
        fb.switch_to_block(entry);
        let old = fb.load(element.clone(), pointer);
        let field = fb.extract_field(Ty::U64, old, 1);
        let one = fb.uconst(Ty::U64, 1);
        let new = fb.binop(BinOp::Add, Ty::U64, field, one);
        let changed = fb.insert_field(element.clone(), old, 1, new);
        fb.store(element, pointer, changed);
        fb.ret(vec![]);
        fb.build()
    } else {
        let signature = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("increment", signature);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I32, 1);
        let result = fb.binop(BinOp::Add, Ty::I32, value, one);
        fb.ret(vec![result]);
        fb.build()
    };
    let caller_signature = mb.add_func_type(
        vec![],
        vec![value_ty.clone(), Ty::I64, Ty::I64, Ty::I64, Ty::U64],
    );
    let mut callers = Vec::new();
    for selector in 0..3 {
        let mut fb = mb.function(format!("caller_{selector}"), caller_signature);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let sentinel = fb.uconst(Ty::U64, 1234567);
        let three = fb.iconst(Ty::I64, 3);
        let frame = fb.heap_alloc(Ty::I64, Some(three), None, AllocOrigin::RustHeap);
        let zero = fb.iconst(Ty::I64, 0);
        let one = fb.iconst(Ty::I64, 1);
        let two = fb.iconst(Ty::I64, 2);
        let second = fb.gep(Ty::I64, frame, vec![one]);
        let third = fb.gep(Ty::I64, frame, vec![two]);
        fb.store(Ty::I64, frame, zero);
        fb.store(Ty::I64, second, zero);
        fb.store(Ty::I64, third, zero);
        let value = if mapped {
            fb.const_value(
                sequence.clone(),
                C::Sequence(vec![
                    C::Aggregate(vec![C::Int(7), C::Int(42)]),
                    C::Aggregate(vec![C::Int(9), C::Int(99)]),
                ]),
            )
        } else {
            fb.iconst(Ty::I32, 42)
        };
        let selector = fb.uconst(Ty::U32, selector);
        let result = fb.call(selected, vec![frame, value, selector, two]);
        let first = fb.load(Ty::I64, frame);
        let second = fb.load(Ty::I64, second);
        let third = fb.load(Ty::I64, third);
        fb.ret(vec![result, first, second, third, sentinel]);
        callers.push(fb.build());
    }
    let mut module = mb.build().expect("placeholder module validates");
    let mut entry = Block::new(BlockId::new(900));
    entry.params = vec![
        (v(42), Ty::Ptr),
        (v(0), value_ty.clone()),
        (v(u32::MAX), Ty::U32),
        (v(7), Ty::I64),
    ];
    let entry_value = if mapped {
        Inst::Copy {
            ty: value_ty.clone(),
            operand: v(0),
        }
    } else {
        Inst::Call {
            callee: helper,
            args: vec![v(0)],
        }
    };
    entry.body = vec![
        InstrNode::new(entry_value).with_result(v(65537)),
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: C::Int(0),
        })
        .with_result(v(19)),
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ne,
            ty: Ty::U32,
            lhs: v(u32::MAX),
            rhs: v(19),
        })
        .with_result(v(20)),
        InstrNode::new(match family {
            Family::Br => Inst::Br {
                target: BlockId::new(901),
                args: vec![],
            },
            Family::CondBr => Inst::CondBr {
                cond: v(20),
                then_target: BlockId::new(70),
                then_args: vec![],
                else_target: BlockId::new(901),
                else_args: vec![],
            },
            Family::Switch | Family::SeqMapSwitch => Inst::Switch {
                value: v(u32::MAX),
                default: BlockId::new(500),
                default_args: vec![],
                cases: vec![
                    SwitchCase {
                        value: C::Int(0),
                        target: BlockId::new(70),
                        args: vec![],
                    },
                    SwitchCase {
                        value: C::Int(1),
                        target: BlockId::new(11),
                        args: vec![],
                    },
                ],
                exhaustive_enum_unreachable: false,
            },
        }),
    ];
    let mut blocks = vec![entry];
    // Serialization order differs from dispatch order. Every suspend
    // occurrence receives its own triple, before the trailing dispatch row.
    for (label, slot, next, result) in [(11, 1, 33, 29), (500, 0, 49, 31), (70, 0, 17, 23)] {
        let mut block = Block::new(BlockId::new(label));
        let prefix = if mapped {
            Inst::SeqMap {
                ty: sequence.clone(),
                seq: v(65537),
                fwd: helper,
            }
        } else {
            Inst::Call {
                callee: helper,
                args: vec![v(65537)],
            }
        };
        block.body = vec![
            InstrNode::new(prefix).with_result(v(result)),
            InstrNode::new(if identity {
                Inst::Return {
                    values: vec![v(result)],
                }
            } else {
                Inst::CoroSuspend {
                    frame: v(42),
                    state_slot: slot,
                    next_state: next,
                    value: v(result),
                }
            }),
        ];
        blocks.push(block);
    }
    if matches!(family, Family::Br | Family::CondBr) {
        let mut dispatch = Block::new(BlockId::new(901));
        dispatch.body = vec![InstrNode::new(Inst::Switch {
            value: v(u32::MAX),
            default: BlockId::new(500),
            default_args: vec![],
            cases: vec![
                SwitchCase {
                    value: C::Int(0),
                    target: BlockId::new(if matches!(family, Family::Br) { 70 } else { 11 }),
                    args: vec![],
                },
                SwitchCase {
                    value: C::Int(1),
                    target: BlockId::new(if matches!(family, Family::Br) { 11 } else { 70 }),
                    args: vec![],
                },
            ],
            exhaustive_enum_unreachable: false,
        })];
        blocks.push(dispatch);
    }
    let function = module.function_by_id_mut(selected).unwrap();
    function.entry = BlockId::new(900);
    function.blocks = blocks;
    (module, selected, callers)
}

fn expand(source: &Module, selected: FuncId, variant: Variant) -> Module {
    let mut target = source.clone();
    if matches!(variant, Variant::Source) {
        return target;
    }
    let function = target.function_by_id_mut(selected).unwrap();
    for (position, names) in [(1, [1, 2, 3]), (2, [4, 5, 6]), (3, [8, 9, 10])] {
        let block = &mut function.blocks[position];
        let last = block.body.pop().unwrap();
        let Inst::CoroSuspend {
            frame,
            state_slot,
            next_state,
            value,
        } = last.inst
        else {
            panic!("manual expansion requires the actual source suspend")
        };
        let [index, pointer, state] = names.map(v);
        block.body.extend([
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: C::Int(i128::from(state_slot)),
            })
            .with_result(index),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: frame,
                indices: vec![if matches!(variant, Variant::WrongIndex) {
                    v(7)
                } else {
                    index
                }],
                inbounds: false,
            })
            .with_result(pointer),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: C::Int(i128::from(next_state)),
            })
            .with_result(state),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: pointer,
                value: if matches!(variant, Variant::WrongStore) {
                    index
                } else {
                    state
                },
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return {
                values: vec![value],
            }),
        ]);
    }
    target
}

fn expected(family: Family, selector: usize, variant: Variant, identity: bool) -> Verdict {
    let (slot, state) = match family {
        Family::CondBr if selector != 0 => (0, 17),
        Family::CondBr => (1, 33),
        Family::Br | Family::Switch | Family::SeqMapSwitch => match selector {
            0 => (0, 17),
            1 => (1, 33),
            _ => (0, 49),
        },
    };
    let mut cells = [0; 3];
    if !identity {
        match variant {
            Variant::Source | Variant::Correct => cells[slot] = state,
            Variant::WrongStore => cells[slot] = slot,
            Variant::WrongIndex => cells[2] = state,
        }
    }
    let value = if matches!(family, Family::SeqMapSwitch) {
        Val::Sequence(vec![
            Val::Aggregate(vec![int(8, 7), int(64, 43)]),
            Val::Aggregate(vec![int(8, 9), int(64, 100)]),
        ])
    } else {
        int(32, 44)
    };
    Verdict::Ok(vec![
        value,
        int(64, cells[0] as u128),
        int(64, cells[1] as u128),
        int(64, cells[2] as u128),
        int(64, 1234567),
    ])
}

fn codecs(module: Module, directory: &Path, label: &str) -> [(&'static str, Module); 5] {
    let binary = trust_ir::binary::serialize_module(&module).unwrap();
    let text = trust_ir::format::text_checked(&module).unwrap();
    let json = serde_json::to_vec(&module).unwrap();
    let msgpack = rmp_serde::to_vec(&module).unwrap();
    std::fs::create_dir_all(directory).unwrap();
    for (extension, bytes) in [
        ("binary", binary.as_slice()),
        ("tir", text.as_bytes()),
        ("wire.json", json.as_slice()),
        ("msgpack", msgpack.as_slice()),
    ] {
        std::fs::write(directory.join(format!("{label}.{extension}")), bytes).unwrap();
    }
    [
        ("original", module),
        (
            "binary",
            trust_ir::binary::deserialize_module(&binary).unwrap(),
        ),
        ("text", trust_ir::parser::parse_module(&text).unwrap()),
        ("JSON", serde_json::from_slice(&json).unwrap()),
        ("MessagePack", rmp_serde::from_slice(&msgpack).unwrap()),
    ]
}

fn assert_only_graph_changes(source: &Module, target: &Module, selected: FuncId) {
    let mut expected = source.clone();
    expected.function_by_id_mut(selected).unwrap().blocks =
        target.function_by_id(selected).unwrap().blocks.clone();
    assert_eq!(&expected, target, "only the selected graph may change");
}

fn pair(source: &Module, target: &Module, selected: FuncId, kind: &str) -> serde_json::Value {
    serde_json::json!({"source":source,"target":target,"selected":selected.0,
        "kind":kind,"probe_domain":1})
}

fn query(pairs: &[serde_json::Value], directory: &Path) {
    let input = directory.join("coro-all-blocks-factory.request.json");
    std::fs::write(
        &input,
        serde_json::to_vec(&serde_json::json!({"pairs":pairs})).unwrap(),
    )
    .unwrap();
    let lake = super::find_lake().expect("required pinned Lean oracle");
    let package = super::lean_dir();
    for module in [
        "TrustIr.Proofs.GenericCoroAllBlocksFactory",
        "TrustIrEval.Run",
    ] {
        let output = super::lake_build_command(&lake, &package, module)
            .output()
            .unwrap();
        std::fs::write(
            directory.join(format!("build-{module}.stdout.txt")),
            &output.stdout,
        )
        .unwrap();
        std::fs::write(
            directory.join(format!("build-{module}.stderr.txt")),
            &output.stderr,
        )
        .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let output = super::lake_run_command(&lake, &package, "TrustIrEval/CoroAllBlocksFactory.lean")
        .arg(&input)
        .output()
        .expect("query the actual all-block functions factory");
    std::fs::write(
        directory.join("coro-all-blocks-factory.response.json"),
        &output.stdout,
    )
    .unwrap();
    std::fs::write(
        directory.join("coro-all-blocks-factory.stderr.txt"),
        &output.stderr,
    )
    .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let answers: Vec<serde_json::Value> = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(answers.len(), pairs.len());
    let trace = serde_json::json!([
        {"block":11,"names":[1,2,3]},
        {"block":500,"names":[4,5,6]},
        {"block":70,"names":[8,9,10]},
    ]);
    for (pair, answer) in pairs.iter().zip(&answers) {
        let kind = pair["kind"].as_str().unwrap();
        if kind == "source_error" {
            assert_eq!(answer["status"], "source_error", "{answer}");
            assert!(
                answer["error"]
                    .as_str()
                    .unwrap()
                    .contains("duplicate value declaration"),
                "{answer}"
            );
            assert_eq!(answer["capacity_probe"]["status"], "source_error");
            continue;
        }
        if kind == "identity" {
            assert_eq!(answer["status"], "unchanged", "{answer}");
            assert_eq!(answer["trace"], serde_json::json!([]));
            assert_eq!(answer["capacity_probe"]["status"], "unchanged");
        } else {
            assert_eq!(answer["status"], "expanded", "{answer}");
            assert_eq!(answer["trace"], trace, "{answer}");
            assert_eq!(answer["capacity_probe"]["status"], "capacity");
        }
        assert_eq!(
            answer["actual_target_ast_equal"],
            matches!(kind, "correct" | "identity"),
            "{kind}: {answer}"
        );
        if kind == "collision" {
            assert!(answer["manual_metadata_error"].is_string(), "{answer}");
            continue;
        }
        assert_eq!(answer["factory_cfg_matches_rows"], true, "{kind}: {answer}");
        assert_eq!(
            answer["original_metadata_preserved"], true,
            "{kind}: {answer}"
        );
        assert_eq!(answer["generated_metadata_typed"], true, "{kind}: {answer}");
        assert_eq!(answer["header_equal"], kind != "header", "{kind}: {answer}");
        assert_eq!(
            answer["manual_metadata_equal"],
            !matches!(kind, "partial" | "type"),
            "{kind}: {answer}"
        );
        if kind == "reorder" {
            assert_eq!(answer["cfg_equal"], true);
            assert_eq!(answer["literal_rows_equal"], false);
        }
    }
}

#[test]
fn generic_coro_all_blocks_connects_actual_factory_to_nonentry_dispatch() {
    let directory = evidence_dir();
    std::fs::create_dir_all(&directory).unwrap();
    let mut modules = Vec::new();
    let mut pairs = Vec::new();
    for bits in [32, 64] {
        for family in [
            Family::Br,
            Family::CondBr,
            Family::Switch,
            Family::SeqMapSwitch,
        ] {
            let (source, selected, callers) = module(bits, family, false);
            let mut group = Vec::new();
            for variant in [
                Variant::Source,
                Variant::Correct,
                Variant::WrongStore,
                Variant::WrongIndex,
            ] {
                let target = expand(&source, selected, variant);
                assert_only_graph_changes(&source, &target, selected);
                let label = format!("{bits}-{family:?}-{variant:?}");
                for (codec, decoded) in codecs(target, &directory.join("codecs"), &label) {
                    let errors = trust_ir_build::validate_module(&decoded);
                    assert!(errors.is_empty(), "{label}/{codec}: {errors:?}");
                    group.push((
                        format!("all_blocks_{label}_{codec}"),
                        decoded,
                        callers.clone(),
                        (0..3)
                            .map(|selector| expected(family, selector, variant, false))
                            .collect::<Vec<_>>(),
                    ));
                }
            }
            for codec in 0..5 {
                let source = &group[codec].1;
                let correct = &group[5 + codec].1;
                for variant in [1, 2, 3] {
                    assert_only_graph_changes(source, &group[variant * 5 + codec].1, selected);
                }
                pairs.push(pair(source, correct, selected, "correct"));
                pairs.push(pair(source, &group[10 + codec].1, selected, "wrong_store"));
                pairs.push(pair(source, &group[15 + codec].1, selected, "wrong_index"));
                let mut partial = correct.clone();
                partial.function_by_id_mut(selected).unwrap().blocks[3] =
                    source.function_by_id(selected).unwrap().blocks[3].clone();
                assert!(trust_ir_build::validate_module(&partial).is_empty());
                pairs.push(pair(source, &partial, selected, "partial"));
                let mut header = correct.clone();
                header.function_by_id_mut(selected).unwrap().calling_conv =
                    trust_ir::CallingConv::Fast;
                pairs.push(pair(source, &header, selected, "header"));
                let mut different_type = correct.clone();
                let node =
                    &mut different_type.function_by_id_mut(selected).unwrap().blocks[1].body[1];
                let Inst::Const { ty, .. } = &mut node.inst else {
                    panic!("actual generated index constant")
                };
                *ty = Ty::U64;
                assert!(trust_ir_build::validate_module(&different_type).is_empty());
                pairs.push(pair(source, &different_type, selected, "type"));
                let mut reordered = correct.clone();
                reordered
                    .function_by_id_mut(selected)
                    .unwrap()
                    .blocks
                    .swap(1, 2);
                assert!(trust_ir_build::validate_module(&reordered).is_empty());
                pairs.push(pair(source, &reordered, selected, "reorder"));
                if codec == 0 {
                    let mut collision = correct.clone();
                    collision.function_by_id_mut(selected).unwrap().blocks[1].body[1].results =
                        vec![v(0)];
                    assert!(!trust_ir_build::validate_module(&collision).is_empty());
                    pairs.push(pair(source, &collision, selected, "collision"));
                    let mut bad_source = source.clone();
                    let body = &mut bad_source.function_by_id_mut(selected).unwrap().blocks[0].body;
                    for ty in [Ty::I32, Ty::U64] {
                        body.insert(
                            0,
                            InstrNode::new(Inst::Const {
                                ty,
                                value: C::Int(0),
                            })
                            .with_result(v(600)),
                        );
                    }
                    assert!(!trust_ir_build::validate_module(&bad_source).is_empty());
                    pairs.push(pair(&bad_source, correct, selected, "source_error"));
                }
            }
            modules.extend(group);
        }
        let (identity, selected, callers) = module(bits, Family::Switch, true);
        for (codec, decoded) in codecs(
            identity,
            &directory.join("codecs"),
            &format!("{bits}-identity"),
        ) {
            assert!(trust_ir_build::validate_module(&decoded).is_empty());
            pairs.push(pair(&decoded, &decoded, selected, "identity"));
            modules.push((
                format!("all_blocks_{bits}_identity_{codec}"),
                decoded,
                callers.clone(),
                (0..3)
                    .map(|selector| expected(Family::Switch, selector, Variant::Source, true))
                    .collect(),
            ));
        }
    }
    assert_eq!(pairs.len(), 306);
    assert_eq!(modules.len(), 170);
    let Oracle::Ready(exe) = oracle() else { return };
    query(&pairs, &directory);
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, callers, _)| Batch {
            label: label.clone(),
            module,
            runs: callers.iter().map(|caller| (*caller, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 510);
    let mut observed = 0;
    let (groups, remainder) = reports.as_chunks::<3>();
    assert!(remainder.is_empty());
    for ((label, _, _, expected), actual) in modules.iter().zip(groups) {
        for (expected, actual) in expected.iter().zip(actual) {
            assert_eq!(actual.comparison, Comparison::Agree, "{label}: {actual:?}");
            assert_eq!(&actual.rust, expected, "{label}: {actual:?}");
            assert_eq!(&actual.lean, expected, "{label}: {actual:?}");
            observed += 1;
        }
    }
    assert_eq!(observed, 510);
    println!(
        "all-block factory: 510 Ok executions, 2 targets x 5 cold codecs, Br/CondBr/Switch and Call/aggregate SeqMap prefixes; 306 actual factory queries including identity/source-error/small-domain capacity, independent AST/header/type/row-order/collision controls; execution controls for the separately proved framed call equality"
    );
}

/// Both entries have a finite path through the other function, and both
/// original definitions contain two nonentry suspend terminators. The caller
/// reads both shared frame cells after the real call boundary has restored its
/// own SSA locals. No manual target module participates in this corpus.
fn mutual_module(bits: u32) -> (Module, Vec<FuncId>) {
    let mut mb = ModuleBuilder::new_with_target_info("coro_module_mutual", semr_target(bits));
    let signature = mb.add_func_type(vec![Ty::Ptr, Ty::Bool, Ty::I32], vec![Ty::I32]);
    let mut frames = Vec::new();
    for slot in 0..2 {
        let mut fb = mb.function(format!("mutual_{slot}"), signature);
        let entry = fb.create_block();
        let frame = fb.add_block_param(entry, Ty::Ptr);
        let recurse = fb.add_block_param(entry, Ty::Bool);
        let value = fb.add_block_param(entry, Ty::I32);
        let call = fb.create_block();
        let base = fb.create_block();
        fb.switch_to_block(entry);
        fb.condbr(recurse, call, vec![], base, vec![]);
        fb.switch_to_block(call);
        let stop = fb.bool_const(false);
        let result = fb.call(FuncId::new(1 - slot), vec![frame, stop, value]);
        fb.ret(vec![result]);
        fb.switch_to_block(base);
        fb.ret(vec![value]);
        let id = fb.build();
        assert_eq!(id, FuncId::new(slot));
        frames.push((id, frame));
    }
    let caller_signature = mb.add_func_type(vec![], vec![Ty::I32, Ty::I64, Ty::I64, Ty::U64]);
    let mut callers = Vec::new();
    for selected in 0..2 {
        let mut fb = mb.function(format!("entry_{selected}"), caller_signature);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let sentinel = fb.uconst(Ty::U64, 1234567);
        let count = fb.iconst(Ty::I64, 2);
        let frame = fb.heap_alloc(Ty::I64, Some(count), None, AllocOrigin::RustHeap);
        let zero = fb.iconst(Ty::I64, 0);
        let one = fb.iconst(Ty::I64, 1);
        let second = fb.gep(Ty::I64, frame, vec![one]);
        fb.store(Ty::I64, frame, zero);
        fb.store(Ty::I64, second, zero);
        let recurse = fb.bool_const(true);
        let value = fb.iconst(Ty::I32, 42);
        let result = fb.call(FuncId::new(selected), vec![frame, recurse, value]);
        let first = fb.load(Ty::I64, frame);
        let second = fb.load(Ty::I64, second);
        fb.ret(vec![result, first, second, sentinel]);
        callers.push(fb.build());
    }
    let mut module = mb
        .build()
        .expect("finite mutually recursive source validates");
    for (slot, (function, frame)) in frames.into_iter().enumerate() {
        let function = module.function_by_id_mut(function).unwrap();
        let mut changed = 0;
        for block in &mut function.blocks {
            let Some(node) = block.body.last_mut() else {
                continue;
            };
            if let Inst::Return { values } = &node.inst {
                assert_eq!(values.len(), 1);
                node.inst = Inst::CoroSuspend {
                    frame,
                    state_slot: slot as u32,
                    next_state: 17 + 2 * slot as i64,
                    value: values[0],
                };
                changed += 1;
            }
        }
        assert_eq!(changed, 2);
    }
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (module, callers)
}

fn module_query(request: &serde_json::Value, directory: &Path, label: &str) -> serde_json::Value {
    let input = directory.join(format!("{label}.request.json"));
    std::fs::write(&input, serde_json::to_vec(request).unwrap()).unwrap();
    let lake = super::find_lake().expect("required pinned Lean oracle");
    let output = super::lake_run_command(
        &lake,
        &super::lean_dir(),
        "TrustIrEval/CoroModuleFactory.lean",
    )
    .arg(&input)
    .output()
    .expect("execute actual produced module");
    std::fs::write(
        directory.join(format!("{label}.response.json")),
        &output.stdout,
    )
    .unwrap();
    std::fs::write(
        directory.join(format!("{label}.stderr.txt")),
        &output.stderr,
    )
    .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).expect("module producer reply")
}

#[test]
fn generic_coro_module_factory_executes_actual_mutual_module() {
    let directory = evidence_dir().join("produced-module");
    std::fs::create_dir_all(&directory).unwrap();
    let mut cases = Vec::new();
    for bits in [32, 64] {
        let (source, callers) = mutual_module(bits);
        for (codec, module) in codecs(source, &directory.join("codecs"), &format!("mutual_{bits}"))
        {
            assert!(trust_ir_build::validate_module(&module).is_empty());
            cases.push((format!("mutual_{bits}_{codec}"), module, callers.clone()));
        }
    }
    assert_eq!(cases.len(), 10);
    let Oracle::Ready(_) = oracle() else { return };
    let lake = super::find_lake().expect("required pinned Lean oracle");
    let output =
        super::lake_build_command(&lake, &super::lean_dir(), "TrustIrEval.CoroModuleFactory")
            .output()
            .unwrap();
    std::fs::write(directory.join("build.stdout.txt"), &output.stdout).unwrap();
    std::fs::write(directory.join("build.stderr.txt"), &output.stderr).unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let expected = Verdict::Ok(vec![
        int(32, 42),
        int(64, 17),
        int(64, 19),
        int(64, 1234567),
    ]);
    let mut pairs = 0;
    for (strategy, rust_strategy) in [
        ("abort", trust_ir::interpret::PanicStrategy::Abort),
        ("unwind", trust_ir::interpret::PanicStrategy::Unwind),
    ] {
        let batches: Vec<_> = cases.iter().map(|(_, module, callers)| serde_json::json!({
            "module": module,
            "runs": callers.iter().map(|id| serde_json::json!({"function":id.0,"args":[]})).collect::<Vec<_>>()
        })).collect();
        let request = serde_json::json!({
            "fuel":super::FUEL,"call_depth":super::CALL_DEPTH,"panic_strategy":strategy,"batches":batches
        });
        let reply = module_query(&request, &directory, strategy);
        let answers = reply.as_array().unwrap();
        assert_eq!(answers.len(), cases.len());
        for ((label, module, callers), answer) in cases.iter().zip(answers) {
            assert_eq!(answer["status"], "ready", "{label}: {answer}");
            assert_eq!(answer["headers_equal"], true, "{label}: {answer}");
            assert_eq!(answer["source_suspend_count"], 4, "{label}: {answer}");
            assert_eq!(answer["target_suspend_count"], 0, "{label}: {answer}");
            let source = answer["source_functions"].as_array().unwrap();
            let target = answer["target_functions"].as_array().unwrap();
            assert_eq!(source.len(), 4);
            assert_eq!(target.len(), 4);
            for (index, (source, target)) in source.iter().zip(target).enumerate() {
                assert_eq!(source["id"], target["id"]);
                assert_eq!(source["header"], target["header"]);
                if index < 2 {
                    assert_ne!(source["body"], target["body"]);
                } else {
                    assert_eq!(source["body"], target["body"]);
                }
            }
            let before = answer["source_runs"].as_array().unwrap();
            let after = answer["target_runs"].as_array().unwrap();
            assert_eq!(before.len(), 2);
            assert_eq!(after.len(), 2);
            for ((caller, source), target) in callers.iter().zip(before).zip(after) {
                let rust = super::run_rust_under(module, *caller, &[], rust_strategy);
                assert_eq!(rust, expected, "{label}/{strategy}: Rust");
                assert_eq!(
                    super::lean_verdict(source),
                    expected,
                    "{label}/{strategy}: source"
                );
                assert_eq!(
                    super::lean_verdict(target),
                    expected,
                    "{label}/{strategy}: actual target"
                );
                pairs += 1;
            }
        }
    }
    assert_eq!(pairs, 40);
    // The first two function bodies would already have changed before the
    // final function fails. Rejection must expose the original module only.
    // These malformed inputs receive no execution or admission credit.
    let mut bad_metadata = cases[0].1.clone();
    for ty in [Ty::I32, Ty::U64] {
        bad_metadata.functions[3].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const {
                ty,
                value: C::Int(0),
            })
            .with_result(v(600)),
        );
    }
    let mut bad_signature = cases[0].1.clone();
    bad_signature.functions[3].ty = trust_ir::value::FuncTyId::new(u32::MAX);
    for invalid in [&bad_metadata, &bad_signature] {
        assert!(!trust_ir_build::validate_module(invalid).is_empty());
    }
    let rejected = module_query(
        &serde_json::json!({
            "fuel":super::FUEL,"call_depth":super::CALL_DEPTH,
            "batches":[{"module":bad_metadata,"runs":[]},{"module":bad_signature,"runs":[]}]
        }),
        &directory,
        "atomic-rejections",
    );
    let rejected = rejected.as_array().unwrap();
    assert_eq!(rejected.len(), 2);
    for (answer, kind) in rejected.iter().zip(["inference", "decode"]) {
        assert_eq!(answer["status"], "rejected", "{answer}");
        assert_eq!(answer["problem"]["kind"], kind, "{answer}");
        assert_eq!(answer["problem"]["function"], 3, "{answer}");
        assert_eq!(answer["original_functions"], answer["source_functions"]);
        assert!(answer.get("target_functions").is_none());
        assert!(answer.get("source_runs").is_none());
        assert!(answer.get("target_runs").is_none());
    }
    println!(
        "actual module producer: 20 successful module publications, 40 source/produced-target execution pairs and 40 Rust source controls; two mutually recursive definitions/four nonentry suspend sites, both entries, two pointer widths/five cold codecs/two panic strategies; return/frame-cell/caller-local observations checked; two atomic source rejections with zero execution/admission credit"
    );
}
