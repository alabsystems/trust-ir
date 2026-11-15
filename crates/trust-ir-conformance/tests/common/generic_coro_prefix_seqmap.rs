// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole-factory controls for aggregate SeqMap prefixes. Paired declaration
//! refusals remain controls and receive no execution-agreement credit.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::inst::{AllocOrigin, BinOp};
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Inst, InstrNode, Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy, Debug)]
enum Kind {
    Aggregate,
    EmptyDefined,
    EmptyDeclared,
    NonemptyDeclared,
}

#[derive(Clone, Copy, Debug)]
enum Expansion {
    Source,
    Correct,
    WrongStore,
    WrongIndex,
}

fn int(width: u32, raw: u128) -> Val {
    Val::Int { width, raw }
}

fn cohort(bits: u32, kind: Kind, expansion: Expansion) -> (Module, FuncId, Verdict) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("coro_prefix_seqmap_{bits}_{kind:?}"),
        semr_target(bits),
    );
    let element = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    let element_id = mb.add_type(element.clone());
    let sequence = Ty::Sequence(element_id);
    let signature = mb.add_func_type(
        vec![Ty::Ptr, sequence.clone(), Ty::I64, Ty::I64],
        vec![sequence.clone()],
    );
    let selected = {
        let mut fb = mb.function("selected", signature);
        let entry = fb.create_block();
        fb.add_block_param(entry, Ty::Ptr);
        let value = fb.add_block_param(entry, sequence.clone());
        fb.add_block_param(entry, Ty::I64);
        fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        fb.ret(vec![value]);
        fb.build()
    };
    let reference = Ty::RefMut(Box::new(element.clone()));
    let forward_signature = mb.add_func_type(vec![reference.clone()], vec![]);
    let declared = matches!(kind, Kind::EmptyDeclared | Kind::NonemptyDeclared);
    let forward = if declared {
        mb.declare_function("forward", forward_signature)
    } else {
        let mut fb = mb.function("forward", forward_signature);
        let entry = fb.create_block();
        let pointer = fb.add_block_param(entry, reference);
        fb.switch_to_block(entry);
        let value = fb.load(element.clone(), pointer);
        let old = fb.extract_field(Ty::U64, value, 1);
        let one = fb.uconst(Ty::U64, 1);
        let incremented = fb.binop(BinOp::Add, Ty::U64, old, one);
        let changed = fb.insert_field(element.clone(), value, 1, incremented);
        fb.store(element.clone(), pointer, changed);
        fb.ret(vec![]);
        fb.build()
    };
    let empty = matches!(kind, Kind::EmptyDefined | Kind::EmptyDeclared);
    let values = if empty {
        vec![]
    } else {
        vec![
            C::Aggregate(vec![C::Int(7), C::Int(42)]),
            C::Aggregate(vec![C::Int(9), C::Int(99)]),
        ]
    };
    let caller_signature =
        mb.add_func_type(vec![], vec![sequence.clone(), Ty::I64, Ty::I64, Ty::U64]);
    let caller = {
        let mut fb = mb.function("caller", caller_signature);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let sentinel = fb.uconst(Ty::U64, 1234567);
        let two = fb.iconst(Ty::I64, 2);
        let frame = fb.heap_alloc(Ty::I64, Some(two), None, AllocOrigin::RustHeap);
        let zero = fb.iconst(Ty::I64, 0);
        let one = fb.iconst(Ty::I64, 1);
        let second = fb.gep(Ty::I64, frame, vec![one]);
        fb.store(Ty::I64, frame, zero);
        fb.store(Ty::I64, second, zero);
        let input = fb.const_value(sequence.clone(), C::Sequence(values));
        let result = fb.call(selected, vec![frame, input, one, one]);
        let first_state = fb.load(Ty::I64, frame);
        let second_state = fb.load(Ty::I64, second);
        fb.ret(vec![result, first_state, second_state, sentinel]);
        fb.build()
    };
    let mut module = mb.build().expect("placeholder module validates");
    let frame = ValueId::new(42);
    let input = ValueId::new(0);
    let spare = ValueId::new(7);
    let result = ValueId::new(65537);
    let mut body = vec![
        InstrNode::new(Inst::SeqMap {
            ty: sequence.clone(),
            seq: input,
            fwd: forward,
        })
        .with_result(result),
    ];
    if matches!(expansion, Expansion::Source) {
        body.push(InstrNode::new(Inst::CoroSuspend {
            frame,
            state_slot: 0,
            next_state: 17,
            value: result,
        }));
    } else {
        let index = ValueId::new(1);
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
        (input, sequence),
        (spare, Ty::I64),
        (ValueId::new(u32::MAX), Ty::I64),
    ];
    entry.body = body;
    let selected = module.function_by_id_mut(selected).unwrap();
    selected.entry = entry.id;
    selected.blocks = vec![entry];
    let expected = if matches!(kind, Kind::NonemptyDeclared) {
        Verdict::Unsupported(String::new())
    } else {
        let output = if empty {
            vec![]
        } else {
            vec![
                Val::Aggregate(vec![int(8, 7), int(64, 43)]),
                Val::Aggregate(vec![int(8, 9), int(64, 100)]),
            ]
        };
        let (first, second) = match expansion {
            Expansion::Source | Expansion::Correct => (17, 0),
            Expansion::WrongStore => (0, 0),
            Expansion::WrongIndex => (0, 17),
        };
        Verdict::Ok(vec![
            Val::Sequence(output),
            int(64, first),
            int(64, second),
            int(64, 1234567),
        ])
    };
    (module, caller, expected)
}

fn codecs(module: Module) -> [(&'static str, Module); 5] {
    let binary = trust_ir::binary::serialize_module(&module).unwrap();
    let text = trust_ir::format::text_checked(&module).unwrap();
    let json = serde_json::to_vec(&module).unwrap();
    let msgpack = rmp_serde::to_vec(&module).unwrap();
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

fn audit_factory(pairs: &[serde_json::Value]) {
    let directory = std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir()
                .join(".ubd")
                .join(format!("coro-prefix-seqmap-{}", std::process::id()))
        });
    std::fs::create_dir_all(&directory).unwrap();
    let input = directory.join("coro-prefix-seqmap-factory.request.json");
    std::fs::write(
        &input,
        serde_json::to_vec(&serde_json::json!({"pairs": pairs})).unwrap(),
    )
    .unwrap();
    let lake = super::find_lake().expect("required pinned Lean oracle");
    let package = super::lean_dir();
    let build = super::lake_build_command(&lake, &package, "TrustIr.Proofs.GenericCoroProps")
        .output()
        .expect("build actual factory dependency");
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let output = super::lake_run_command(&lake, &package, "TrustIrEval/CoroPrefixFactory.lean")
        .arg(&input)
        .output()
        .expect("query actual prefix factory");
    std::fs::write(
        directory.join("coro-prefix-seqmap-factory.response.json"),
        &output.stdout,
    )
    .unwrap();
    std::fs::write(
        directory.join("coro-prefix-seqmap-factory.stderr.txt"),
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

#[test]
fn generic_coro_seqmap_prefixes_use_aggregate_cells_and_empty_headers() {
    let mut modules = Vec::new();
    let mut pairs = Vec::new();
    for bits in [32, 64] {
        for kind in [
            Kind::Aggregate,
            Kind::EmptyDefined,
            Kind::EmptyDeclared,
            Kind::NonemptyDeclared,
        ] {
            let mut group = Vec::new();
            for expansion in [
                Expansion::Source,
                Expansion::Correct,
                Expansion::WrongStore,
                Expansion::WrongIndex,
            ] {
                let (module, caller, expected) = cohort(bits, kind, expansion);
                for (codec, decoded) in codecs(module) {
                    let errors = trust_ir_build::validate_module(&decoded);
                    assert!(
                        errors.is_empty(),
                        "{bits}/{kind:?}/{expansion:?}/{codec}: {errors:?}"
                    );
                    group.push((
                        format!("coro_prefix_seqmap_{bits}_{kind:?}_{expansion:?}_{codec}"),
                        decoded,
                        caller,
                        expected.clone(),
                    ));
                }
            }
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
                    let mut expected_module = source.clone();
                    let target_function = target.function_by_id(selected).unwrap();
                    let expected_function = expected_module.function_by_id_mut(selected).unwrap();
                    expected_function.entry = target_function.entry;
                    expected_function.blocks = target_function.blocks.clone();
                    assert_eq!(
                        &expected_module, target,
                        "only the selected graph may change"
                    );
                    assert_eq!(source.func_types, target.func_types);
                    assert_eq!(source.types, target.types);
                    for function in source
                        .functions
                        .iter()
                        .filter(|function| function.id != selected)
                    {
                        assert_eq!(Some(function), target.function_by_id(function.id));
                    }
                    pairs.push(serde_json::json!({"source": source, "target": target, "selected": selected.0, "expected_ast_equal": variant == 1}));
                }
            }
            modules.extend(group);
        }
    }
    assert_eq!(pairs.len(), 120);
    let Oracle::Ready(exe) = oracle() else { return };
    audit_factory(&pairs);
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, caller, _)| Batch {
            label: label.clone(),
            module,
            runs: vec![(*caller, vec![])],
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 160);
    let mut agreements = 0;
    let mut refusals = 0;
    for ((label, _, _, expected), actual) in modules.iter().zip(&reports) {
        if matches!(expected, Verdict::Unsupported(_)) {
            assert_eq!(
                actual.rust,
                Verdict::Unsupported("unsupported_call".into()),
                "{label}: {actual:?}"
            );
            assert_eq!(
                actual.lean,
                Verdict::Unsupported("interprocedural_call".into()),
                "{label}: {actual:?}"
            );
            assert!(
                matches!(actual.comparison, Comparison::Unsupported(_, _)),
                "{label}: {actual:?}"
            );
            refusals += 1;
        } else {
            assert_eq!(actual.comparison, Comparison::Agree, "{label}: {actual:?}");
            assert_eq!(&actual.rust, expected, "{label}: {actual:?}");
            assert_eq!(&actual.lean, expected, "{label}: {actual:?}");
            agreements += 1;
        }
    }
    assert_eq!((agreements, refusals), (120, 40));
    println!(
        "SeqMap prefix: 160 executions = 120 Ok agreements + 40 paired declaration refusals (zero agreement credit); 120 actual factory queries = 40 target matches + 80 AST mutant controls; 60 successful macro-mutant executions are observably different from source"
    );
}
