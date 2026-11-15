// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source and target are separate modules with identical function IDs. The
//! unchanged helper calls the selected function again, so recursive prefixes
//! exercise the actual changed function table rather than two unrelated leaves.

use super::{
    Batch, Comparison, Oracle, Val, Verdict, differential, on_a_deep_stack, oracle, semr_target,
};
use trust_ir::constant::Constant as C;
use trust_ir::inst::{AllocOrigin, BinOp, ICmpOp};
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Inst, InstrNode, Module, Ty};
use trust_ir_build::ModuleBuilder;

fn audit_actual_factory(modules: &[(String, Module, Vec<Run>)]) {
    let mut pairs = Vec::new();
    let (groups, remainder) = modules.as_chunks::<20>();
    assert!(remainder.is_empty());
    for group in groups {
        for codec in 0..5 {
            let source = &group[codec].1;
            let selected = source
                .functions
                .iter()
                .find(|function| function.name == "selected")
                .unwrap()
                .id;
            for variant in 1..4 {
                let target = &group[variant * 5 + codec].1;
                assert_eq!(source.func_types, target.func_types);
                assert_eq!(source.functions.len(), target.functions.len());
                for function in source
                    .functions
                    .iter()
                    .filter(|function| function.id != selected)
                {
                    assert_eq!(
                        Some(function),
                        target
                            .functions
                            .iter()
                            .find(|target| target.id == function.id)
                    );
                }
                pairs.push(serde_json::json!({
                    "source": source,
                    "target": target,
                    "selected": selected.0,
                    "expected_ast_equal": variant == 1,
                }));
                if variant == 1 && codec == 0 {
                    // A CFG-only observer would silently accept this foreign
                    // selected-function header. This is an observer control;
                    // it is not counted as an executed/admitted module.
                    let mut foreign_header = target.clone();
                    foreign_header
                        .function_by_id_mut(selected)
                        .unwrap()
                        .calling_conv = trust_ir::CallingConv::Fast;
                    pairs.push(serde_json::json!({
                        "source": source,
                        "target": foreign_header,
                        "selected": selected.0,
                        "expected_ast_equal": false,
                        "observer_header_mutant": true,
                    }));
                }
            }
        }
    }
    assert_eq!(pairs.len(), 192);
    let request = serde_json::json!({"pairs": &pairs});
    let directory = std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir()
                .join(".ubd")
                .join(format!("coro-prefix-factory-{}", std::process::id()))
        });
    std::fs::create_dir_all(&directory).unwrap();
    let input = directory.join("coro-prefix-factory.request.json");
    std::fs::write(&input, serde_json::to_vec(&request).unwrap()).unwrap();
    let lake = super::find_lake().expect("the required oracle already found pinned Lean");
    let package = super::lean_dir();
    let build = super::lake_build_command(&lake, &package, "TrustIr.Proofs.GenericCoroProps")
        .output()
        .expect("compile actual factory dependency");
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let output = super::lake_run_command(&lake, &package, "TrustIrEval/CoroPrefixFactory.lean")
        .arg(&input)
        .output()
        .expect("run actual expansion factory on cold source graphs");
    std::fs::write(
        directory.join("coro-prefix-factory.response.json"),
        &output.stdout,
    )
    .unwrap();
    std::fs::write(
        directory.join("coro-prefix-factory.stderr.txt"),
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
    for (pair, answer) in pairs.iter().zip(&answers) {
        assert_eq!(answer["status"], "expanded", "{answer}");
        assert_eq!(
            answer["actual_target_ast_equal"], pair["expected_ast_equal"],
            "{answer}"
        );
        assert_eq!(answer["original_and_generated_metadata"], true, "{answer}");
        assert_eq!(answer["names"], serde_json::json!([1, 2, 3]));
    }
}

#[derive(Clone, Copy, Debug)]
enum Prefix {
    Copy,
    Direct,
    Indirect,
    Mutual,
    MutualIndirect,
    StoreThenCall,
}

#[derive(Clone, Copy, Debug)]
enum Expansion {
    Source,
    Correct,
    WrongStore,
    WrongIndex,
    Collision,
}

#[derive(Clone)]
struct Run {
    function: FuncId,
    expected: Verdict,
}

fn int(width: u32, raw: u128) -> Val {
    Val::Int { width, raw }
}

fn cohort(bits: u32, kind: Prefix, expansion: Expansion) -> (Module, Vec<Run>) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("coro_prefix_{bits}_{kind:?}_{expansion:?}"),
        semr_target(bits),
    );
    let signature = mb.add_func_type(vec![Ty::Ptr, Ty::I64, Ty::I32, Ty::I64], vec![Ty::I32]);
    let caller_signature =
        mb.add_func_type(vec![], vec![Ty::I32, Ty::I64, Ty::I64, Ty::I64, Ty::U64]);
    let selected = {
        let mut fb = mb.function("selected", signature);
        let entry = fb.create_block();
        fb.add_block_param(entry, Ty::Ptr);
        fb.add_block_param(entry, Ty::I64);
        let value = fb.add_block_param(entry, Ty::I32);
        fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        fb.ret(vec![value]);
        fb.build()
    };
    let recursive = matches!(kind, Prefix::Mutual | Prefix::MutualIndirect);
    let helper = {
        let mut fb = mb.function("unchanged_helper", signature);
        let entry = fb.create_block();
        let frame = fb.add_block_param(entry, Ty::Ptr);
        let count = fb.add_block_param(entry, Ty::I64);
        let value = fb.add_block_param(entry, Ty::I32);
        let spare = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        if recursive {
            let again = fb.create_block();
            let done = fb.create_block();
            let zero = fb.iconst(Ty::I64, 0);
            let positive = fb.icmp(ICmpOp::Sgt, Ty::I64, count, zero);
            fb.condbr(positive, again, vec![], done, vec![]);
            fb.switch_to_block(again);
            let one = fb.iconst(Ty::I64, 1);
            let less = fb.binop(BinOp::Sub, Ty::I64, count, one);
            let answer = fb.call(selected, vec![frame, less, value, spare]);
            fb.ret(vec![answer]);
            fb.switch_to_block(done);
        }
        fb.ret(vec![value]);
        fb.build()
    };
    let mut runs = Vec::new();
    for count in [0, 2, -1, 100] {
        for mode in 0..4 {
            let mut fb = mb.function(format!("caller_{count}_{mode}"), caller_signature);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let sentinel = fb.uconst(Ty::U64, 1234567);
            let cells = fb.iconst(Ty::I64, 3);
            let allocation = fb.heap_alloc(Ty::I64, Some(cells), None, AllocOrigin::RustHeap);
            let zero = fb.iconst(Ty::I64, 0);
            let one = fb.iconst(Ty::I64, 1);
            let two = fb.iconst(Ty::I64, 2);
            let slot_one = fb.gep(Ty::I64, allocation, vec![one]);
            let slot_two = fb.gep(Ty::I64, allocation, vec![two]);
            fb.store(Ty::I64, allocation, zero);
            fb.store(Ty::I64, slot_one, zero);
            fb.store(Ty::I64, slot_two, zero);
            let frame = match mode {
                1 => fb.null_ptr(),
                2 => fb.undef(Ty::Ptr),
                _ => allocation,
            };
            let n = fb.iconst(Ty::I64, count);
            let value = if mode == 3 {
                fb.undef(Ty::I32)
            } else {
                fb.iconst(Ty::I32, -5)
            };
            let answer = fb.call(selected, vec![frame, n, value, one]);
            let stored_zero = fb.load(Ty::I64, allocation);
            let stored_one = fb.load(Ty::I64, slot_one);
            let stored_two = fb.load(Ty::I64, slot_two);
            fb.ret(vec![answer, stored_zero, stored_one, stored_two, sentinel]);
            let expected = if mode == 2 || mode == 3 {
                // UB diagnostics differ in text, and the harness preserves
                // the class without conflating it with a layout refusal.
                Verdict::Ub(String::new())
            } else if recursive && count == 100 {
                Verdict::OutOfFuel
            } else if mode == 1 {
                Verdict::Ub(String::new())
            } else {
                let (slot_zero, slot_one) = match expansion {
                    Expansion::Source | Expansion::Correct => (17, 0),
                    Expansion::WrongStore => (0, 0),
                    Expansion::WrongIndex => (0, 17),
                    Expansion::Collision => (17, 0),
                };
                Verdict::Ok(vec![
                    int(32, u128::from(u32::MAX - 4)),
                    int(64, slot_zero),
                    int(64, slot_one),
                    int(
                        64,
                        if matches!(kind, Prefix::StoreThenCall) {
                            1
                        } else {
                            0
                        },
                    ),
                    int(64, 1234567),
                ])
            };
            runs.push(Run {
                function: fb.build(),
                expected,
            });
        }
    }
    let mut module = mb.build().expect("placeholder source validates");
    let frame = ValueId::new(42);
    let count = ValueId::new(u32::MAX);
    let value = ValueId::new(0);
    let spare = ValueId::new(7);
    let result = ValueId::new(65537);
    let code = ValueId::new(11);
    let mut body = Vec::new();
    if matches!(kind, Prefix::StoreThenCall) {
        let address = ValueId::new(19);
        let index = ValueId::new(23);
        body.extend([
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: C::Int(2),
            })
            .with_result(index),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: frame,
                indices: vec![index],
                inbounds: false,
            })
            .with_result(address),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: address,
                value: spare,
                volatile: false,
                align: None,
            }),
        ]);
    }
    let prefix_result = match kind {
        Prefix::Copy => InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand: value,
        })
        .with_result(result),
        Prefix::Indirect | Prefix::MutualIndirect => {
            body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::Func(signature),
                    value: C::FnDef(helper),
                })
                .with_result(code),
            );
            InstrNode::new(Inst::CallIndirect {
                callee: code,
                sig: signature,
                args: vec![frame, count, value, spare],
                calling_conv: trust_ir::CallingConv::default(),
            })
            .with_result(result)
        }
        _ => InstrNode::new(Inst::Call {
            callee: helper,
            args: vec![frame, count, value, spare],
        })
        .with_result(result),
    };
    body.push(prefix_result);
    if matches!(expansion, Expansion::Source) {
        body.push(InstrNode::new(Inst::CoroSuspend {
            frame,
            state_slot: 0,
            next_state: 17,
            value: result,
        }));
    } else {
        // Full source census occupies 0,7,11?,19?,23?,42,65537,u32::MAX;
        // its first three gaps are exactly 1,2,3 in every family.
        let index = ValueId::new(if matches!(expansion, Expansion::Collision) {
            0
        } else {
            1
        });
        let pointer = ValueId::new(2);
        let state = ValueId::new(3);
        body.extend([
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: C::Int(0),
            })
            .with_result(index),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: frame,
                indices: vec![if matches!(expansion, Expansion::WrongIndex) {
                    spare
                } else {
                    index
                }],
                inbounds: false,
            })
            .with_result(pointer),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: C::Int(17),
            })
            .with_result(state),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: pointer,
                value: if matches!(expansion, Expansion::WrongStore) {
                    index
                } else {
                    state
                },
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return {
                values: vec![result],
            }),
        ]);
    }
    let mut entry = Block::new(BlockId::new(900));
    entry.params = vec![
        (frame, Ty::Ptr),
        (count, Ty::I64),
        (value, Ty::I32),
        (spare, Ty::I64),
    ];
    entry.body = body;
    let selected = module
        .functions
        .iter_mut()
        .find(|function| function.id == selected)
        .unwrap();
    selected.entry = entry.id;
    selected.blocks = vec![entry];
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
fn generic_coro_nonempty_prefixes_retain_real_recursive_call_tables() {
    // Use the existing direct-call harness stack for 65 debug interpreter
    // frames. Both engines retain the ordinary fuel and call-depth budgets.
    on_a_deep_stack(generic_coro_prefix_body);
}

fn generic_coro_prefix_body() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        for kind in [
            Prefix::Copy,
            Prefix::Direct,
            Prefix::Indirect,
            Prefix::Mutual,
            Prefix::MutualIndirect,
            Prefix::StoreThenCall,
        ] {
            for expansion in [
                Expansion::Source,
                Expansion::Correct,
                Expansion::WrongStore,
                Expansion::WrongIndex,
            ] {
                let (module, runs) = cohort(bits, kind, expansion);
                for (codec, decoded) in codecs(module) {
                    let errors = trust_ir_build::validate_module(&decoded);
                    assert!(
                        errors.is_empty(),
                        "{bits}/{kind:?}/{expansion:?}/{codec}: {errors:?}"
                    );
                    modules.push((
                        format!("coro_prefix_{bits}_{kind:?}_{expansion:?}_{codec}"),
                        decoded,
                        runs.clone(),
                    ));
                }
            }
            let (collision, _) = cohort(bits, kind, Expansion::Collision);
            let errors = trust_ir_build::validate_module(&collision);
            assert!(
                errors.iter().any(|error| matches!(
                    error,
                    trust_ir_build::validate::ValidationError::DuplicateValueDef { value: 0, .. }
                )),
                "fresh-ID collision must report the duplicated source parameter: {errors:?}"
            );
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    audit_actual_factory(&modules);
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs.iter().map(|run| (run.function, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 3840);
    let (reports, remainder) = reports.as_chunks::<16>();
    assert!(remainder.is_empty());
    for ((label, _, runs), reports) in modules.iter().zip(reports) {
        for (run, actual) in runs.iter().zip(reports) {
            assert_eq!(actual.comparison, Comparison::Agree, "{label}: {actual:?}");
            if matches!(run.expected, Verdict::Ub(_)) {
                assert!(matches!(actual.rust, Verdict::Ub(_)), "{label}: {actual:?}");
                assert!(matches!(actual.lean, Verdict::Ub(_)), "{label}: {actual:?}");
            } else {
                assert_eq!(actual.rust, run.expected, "{label}: {actual:?}");
                assert_eq!(actual.lean, run.expected, "{label}: {actual:?}");
            }
        }
    }
    println!(
        "generic prefix: 3840 runs, 2 targets × 5 codecs; actual direct/indirect mutual call tables, UB/depth and observable store/index mutants"
    );
}
