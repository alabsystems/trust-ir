// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Char Unicode validity is UB at external entry and internal SSA binding.
//! Integer representation errors remain a separate carrier TypeError.
//! Invalid constants below have integer types; every module validates.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::constant::Constant as C;
use trust_ir::inst::CastOp;
use trust_ir::interpret::InterpretValue;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, FuncTy, Function, Inst, InstrNode, Module, Ty};
use trust_ir_build::ModuleBuilder;

#[derive(Clone)]
enum Expected {
    Ok(Val),
    Ub,
}

impl Expected {
    fn binding(value: Option<Val>) -> Self {
        value.map_or(Self::Ub, Self::Ok)
    }
}

#[derive(Clone)]
struct Run {
    function: FuncId,
    args: Vec<InterpretValue>,
    expected: Expected,
    label: String,
}

fn integer(raw: u128) -> Val {
    Val::Int { width: 32, raw }
}

fn scalar(raw: u32) -> bool {
    char::from_u32(raw).is_some()
}

fn cohort(bits: u32) -> (Module, Vec<Run>) {
    let mut mb = ModuleBuilder::new_with_target_info(format!("ssa_char_{bits}"), semr_target(bits));
    let char_sig = mb.add_func_type(vec![], vec![Ty::Char]);
    let answer_sig = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut runs = Vec::new();
    let rows = [
        (
            CastOp::Trunc,
            Ty::U64,
            vec![
                0,
                65,
                0xD7FF,
                0xD800,
                0xDFFF,
                0xE000,
                0xFFFF,
                0x10FFFF,
                0x110000,
                0xFFFF_FFFF,
                0x1_0000_0041,
                0x1_0000_D800,
            ],
        ),
        (
            CastOp::ZExt,
            Ty::U16,
            vec![0, 65, 0xD7FF, 0xD800, 0xDFFF, 0xE000, 0xFFFF],
        ),
        (CastOp::SExt, Ty::I16, vec![-32768, -1, 0, 65, 32767]),
    ];
    for (op, source, values) in rows {
        for raw in values {
            let out = raw as u32;
            let expected = scalar(out).then(|| integer(u128::from(out)));
            let label = format!("{op:?}_{source:?}_{raw}");
            let mut fb = mb.function(format!("return_{label}"), char_sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let input = fb.const_value(source.clone(), C::Int(raw));
            let value = fb.cast(op, source.clone(), Ty::Char, input);
            fb.ret(vec![value]);
            let leaf = fb.build();
            runs.push(Run {
                function: leaf,
                args: vec![],
                expected: Expected::binding(expected.clone()),
                label: format!("return_{label}"),
            });

            let mut fb = mb.function(format!("discard_{label}"), answer_sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let input = fb.const_value(source.clone(), C::Int(raw));
            fb.cast(op, source.clone(), Ty::Char, input);
            let answer = fb.const_value(Ty::I32, C::Int(42));
            fb.ret(vec![answer]);
            runs.push(Run {
                function: fb.build(),
                args: vec![],
                expected: Expected::binding(expected.as_ref().map(|_| integer(42))),
                label: format!("discard_{label}"),
            });

            for indirect in [false, true] {
                let mut fb = mb.function(format!("call_{indirect}_{label}"), answer_sig);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                if indirect {
                    let code = fb.fn_addr(char_sig, leaf);
                    fb.call_indirect(code, char_sig, vec![]);
                } else {
                    fb.call(leaf, vec![]);
                }
                let answer = fb.const_value(Ty::I32, C::Int(42));
                fb.ret(vec![answer]);
                runs.push(Run {
                    function: fb.build(),
                    args: vec![],
                    expected: Expected::binding(expected.as_ref().map(|_| integer(42))),
                    label: format!("call_{indirect}_{label}"),
                });
            }
        }
    }

    for forward in [false, true] {
        let sig = mb.add_func_type(
            vec![Ty::Char],
            vec![if forward { Ty::Char } else { Ty::I32 }],
        );
        let mut fb = mb.function(format!("entry_char_{forward}"), sig);
        let entry = fb.create_block();
        let input = fb.add_block_param(entry, Ty::Char);
        let join = fb.create_block();
        let joined = fb.add_block_param(join, Ty::Char);
        fb.switch_to_block(entry);
        let copied = fb.copy(Ty::Char, input);
        fb.br(join, vec![copied]);
        fb.switch_to_block(join);
        let result = if forward {
            let condition = fb.const_value(Ty::Bool, C::Bool(true));
            let alternative = fb.const_value(Ty::Char, C::Int(65));
            fb.select(Ty::Char, condition, joined, alternative)
        } else {
            fb.const_value(Ty::I32, C::Int(42))
        };
        fb.ret(vec![result]);
        let function = fb.build();
        for raw in [
            0,
            0xD7FF,
            0xD800,
            0xDFFF,
            0xE000,
            0x10FFFF,
            0x110000,
            0xFFFF_FFFF,
        ] {
            runs.push(Run {
                function,
                args: vec![
                    InterpretValue::int(Ty::Char, i128::from(raw)).expect("32-bit Char carrier"),
                ],
                expected: if scalar(raw) {
                    Expected::Ok(integer(if forward { u128::from(raw) } else { 42 }))
                } else {
                    Expected::Ub
                },
                label: format!("entry_{forward}_{raw}"),
            });
        }
    }

    // Char poison is transported by binding, Copy, block arguments and
    // Select. A returned poison still faults at the existing strict use.
    for mode in 0..6 {
        let sig = if mode >= 4 { char_sig } else { answer_sig };
        let mut fb = mb.function(format!("char_poison_{mode}"), sig);
        let entry = fb.create_block();
        let join = fb.create_block();
        let joined = fb.add_block_param(join, Ty::Char);
        fb.switch_to_block(entry);
        let poison = fb.undef(Ty::Char);
        let transported = match mode {
            1 => fb.copy(Ty::Char, poison),
            2 => {
                let aggregate = fb.make_aggregate(Ty::Tuple(vec![Ty::Char]), vec![poison]);
                fb.copy(Ty::Tuple(vec![Ty::Char]), aggregate);
                poison
            }
            3 | 4 => {
                let cond = fb.const_value(Ty::Bool, C::Bool(mode == 3));
                let valid = fb.const_value(Ty::Char, C::Int(65));
                fb.select(Ty::Char, cond, poison, valid)
            }
            _ => poison,
        };
        fb.br(join, vec![transported]);
        fb.switch_to_block(join);
        let answer = if mode >= 4 {
            joined
        } else {
            fb.const_value(Ty::I32, C::Int(42))
        };
        fb.ret(vec![answer]);
        runs.push(Run {
            function: fb.build(),
            args: vec![],
            expected: match mode {
                2 | 5 => Expected::Ub,
                4 => Expected::Ok(integer(65)),
                _ => Expected::Ok(integer(42)),
            },
            label: format!("poison_{mode}"),
        });
    }
    for raw in [0xD800, 0x110000, 0xFFFF_FFFF] {
        let sig = mb.add_func_type(vec![], vec![Ty::U32]);
        let mut fb = mb.function(format!("u32_control_{raw}"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let input = fb.const_value(Ty::U64, C::Int(raw));
        let value = fb.cast(CastOp::Trunc, Ty::U64, Ty::U32, input);
        fb.ret(vec![value]);
        runs.push(Run {
            function: fb.build(),
            args: vec![],
            expected: Expected::Ok(integer(raw as u128)),
            label: format!("u32_{raw}"),
        });
    }
    assert_eq!(runs.len(), 121);
    (mb.build().expect("valid Char SSA modules"), runs)
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
fn char_ssa_bindings_check_unicode_at_results_and_parameters_across_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, runs) = cohort(bits);
        for (codec, decoded) in codecs(module) {
            let errors = trust_ir_build::validate_module(&decoded);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            modules.push((format!("char_ssa_{bits}_{codec}"), decoded, runs.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs
                .iter()
                .map(|run| (run.function, run.args.clone()))
                .collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 1210);
    let mut mismatches = Vec::new();
    let mut ub = 0;
    let mut ok = 0;
    for (report, run) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, runs)| runs))
    {
        match &run.expected {
            Expected::Ok(value) => {
                ok += 1;
                assert_eq!(
                    report.rust,
                    Verdict::Ok(vec![value.clone()]),
                    "{}: {report:?}",
                    run.label
                );
                assert_eq!(
                    report.lean,
                    Verdict::Ok(vec![value.clone()]),
                    "{}: {report:?}",
                    run.label
                );
            }
            Expected::Ub => {
                ub += 1;
                assert!(
                    matches!(report.rust, Verdict::Ub(_)),
                    "{}: {report:?}",
                    run.label
                );
                assert!(
                    matches!(report.lean, Verdict::Ub(_)),
                    "{}: {report:?}",
                    run.label
                );
            }
        }
        if report.comparison != Comparison::Agree {
            mismatches.push(format!("{}: {report:?}", run.label));
        }
    }
    assert_eq!((ok, ub), (750, 460));
    println!(
        "Char SSA: {} checked runs, {ok} exact Ok, {ub} Unicode/strict-use UB, {} disagreements",
        reports.len(),
        mismatches.len()
    );
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}

#[test]
fn single_result_publication_keeps_actual_sparse_source_names_across_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut module = Module::new(format!("sparse_publication_{bits}"));
        module.target_info = Some(semr_target(bits));
        let sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::U64, Ty::U64, Ty::U64],
                abi: None,
                is_vararg: false,
            })
            .unwrap();
        let mut function =
            Function::new(FuncId::new(0), "sparse_publication", sig, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: C::Int(7),
            })
            .with_result(ValueId::new(42)),
            // Zero is an actual later declaration, although the first
            // instruction's private evaluator temporary also used zero.
            InstrNode::new(Inst::Copy {
                ty: Ty::U64,
                operand: ValueId::new(42),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: C::Int(9),
            })
            .with_result(ValueId::new(65537)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(42), ValueId::new(0), ValueId::new(65537)],
            }),
        ];
        function.blocks.push(block);
        module.try_add_function(function).unwrap();
        assert!(trust_ir_build::validate_module(&module).is_empty());
        for (codec, decoded) in codecs(module) {
            let errors = trust_ir_build::validate_module(&decoded);
            assert!(errors.is_empty(), "{bits}/{codec}: {errors:?}");
            let ids: Vec<_> = decoded.functions[0].blocks[0]
                .body
                .iter()
                .flat_map(|node| &node.results)
                .map(|id| id.index())
                .collect();
            assert_eq!(
                ids,
                [42, 0, 65537],
                "{bits}/{codec}: preserve actual source names"
            );
            modules.push((format!("sparse_publication_{bits}_{codec}"), decoded));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module)| Batch {
            label: label.clone(),
            module,
            runs: vec![(FuncId::new(0), vec![])],
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 10);
    let expected = Verdict::Ok(vec![
        Val::Int { width: 64, raw: 7 },
        Val::Int { width: 64, raw: 7 },
        Val::Int { width: 64, raw: 9 },
    ]);
    for report in reports {
        assert_eq!(report.rust, expected, "{report:?}");
        assert_eq!(report.lean, expected, "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}
