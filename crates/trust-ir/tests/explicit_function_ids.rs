// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![cfg(all(feature = "parser", feature = "fmt"))]

use trust_ir::inst::BinOp;
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, InterpretValue,
    Interpreter, Module, Ty, ValueId,
};

fn module(ids: &[u32]) -> Module {
    let mut module = Module::new("dense");
    let signature = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![], false))
        .unwrap();
    for (position, id) in ids.iter().enumerate() {
        let mut function = Function::new(
            FuncId::new(*id),
            if position == 0 { "first" } else { "second" },
            signature,
            BlockId::new(0),
        );
        function.blocks.push(Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        });
        module.functions.push(function);
    }
    module
}

#[test]
fn explicit_function_ids_leave_dense_legacy_text_byte_exact() {
    let module = module(&[0, 1]);
    let expected = concat!(
        "; TrustIr text format v1\nmodule \"dense\"\n",
        "\nfuncty.0 = () -> ()\n",
        "\nfn @first(functy.0) {\nbb0:\n    ret\n}\n",
        "\nfn @second(functy.0) {\nbb0:\n    ret\n}\n"
    );
    assert_eq!(trust_ir::format::text_checked(&module).unwrap(), expected);
    assert_eq!(trust_ir::parser::parse_module(expected).unwrap(), module);
}

#[test]
fn explicit_function_ids_preserve_sparse_item_and_forward_call_identity() {
    let mut module = Module::new("sparse-items");
    let signature = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![Ty::U32], false))
        .unwrap();
    module.types.push(Ty::Tuple(vec![
        Ty::FnItem(FuncId::new(11)),
        Ty::FnItem(FuncId::new(53)),
    ]));
    let value = |id| ValueId::new(id);
    let node = |inst, id| InstrNode::new(inst).with_result(value(id));
    let mut entry = Function::new(FuncId::new(201), "entry", signature, BlockId::new(0));
    entry.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            node(
                Inst::Const {
                    ty: Ty::FnItem(FuncId::new(11)),
                    value: Constant::FnItem(FuncId::new(11)),
                },
                0,
            ),
            node(
                Inst::CallIndirect {
                    callee: value(0),
                    sig: signature,
                    args: vec![],
                    calling_conv: trust_ir::CallingConv::C,
                },
                1,
            ),
            node(
                Inst::Call {
                    callee: FuncId::new(53),
                    args: vec![],
                },
                2,
            ),
            node(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::U32,
                    lhs: value(1),
                    rhs: value(2),
                },
                3,
            ),
            InstrNode::new(Inst::Return {
                values: vec![value(3)],
            }),
        ],
    });
    module.functions.push(entry);
    for (id, answer, name) in [(53, 2, "second"), (11, 1, "target \"one\" é")] {
        let mut function = Function::new(FuncId::new(id), name, signature, BlockId::new(0));
        function.blocks.push(Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                node(
                    Inst::Const {
                        ty: Ty::U32,
                        value: Constant::Int(answer),
                    },
                    0,
                ),
                InstrNode::new(Inst::Return {
                    values: vec![value(0)],
                }),
            ],
        });
        module.functions.push(function);
    }
    assert!(trust_ir::text_loss::text_losses(&module).is_empty());
    let text = trust_ir::format::text_checked(&module).unwrap();
    assert!(text.contains("fn @entry(functy.0, func.201)"));
    let decoded = trust_ir::parser::parse_module(&text).unwrap();
    assert_eq!(decoded, module);
    assert_eq!(
        Interpreter::with_module(&decoded)
            .execute_func(FuncId::new(201), [])
            .unwrap()
            .returns,
        vec![InterpretValue::int(Ty::U32, 3).unwrap()]
    );
}

#[test]
fn explicit_function_ids_keep_implicit_source_ordinals_and_u32_max() {
    let text = "module \"mixed\"\nfuncty.0 = () -> ()\nfn @first(functy.0, func.4294967295) {}\nfn @second(functy.0) {}\n";
    let parsed = trust_ir::parser::parse_module(text).unwrap();
    assert_eq!(
        parsed
            .functions
            .iter()
            .map(|function| function.id.index())
            .collect::<Vec<_>>(),
        [u32::MAX, 1]
    );
    assert_eq!(
        trust_ir::parser::parse_module(&trust_ir::format::text_checked(&parsed).unwrap()).unwrap(),
        parsed
    );
    assert_eq!(
        trust_ir::parser::parse_function("fn @alone(functy.0, func.53) {}")
            .unwrap()
            .id,
        FuncId::new(53)
    );
}

#[test]
fn explicit_function_ids_refuse_duplicate_and_implicit_collisions() {
    for headers in [
        "fn @a(functy.0, func.11) {}\nfn @b(functy.0, func.11) {}",
        "fn @a(functy.0) {}\nfn @b(functy.0, func.0) {}",
        "fn @a(functy.0, func.1) {}\nfn @b(functy.0) {}",
    ] {
        let text = format!("module \"bad\"\nfuncty.0 = () -> ()\n{headers}\n");
        assert!(
            trust_ir::parser::parse_module(&text)
                .unwrap_err()
                .message
                .contains("duplicate function id")
        );
    }
}

#[test]
fn explicit_function_ids_refuse_malformed_or_overflowing_headers() {
    for suffix in [
        ", func.-1",
        ", func.4294967296",
        ", func.",
        ", functy.11",
        ", func.11, func.12",
    ] {
        let text = format!("module \"bad\"\nfuncty.0 = () -> ()\nfn @a(functy.0{suffix}) {{}}\n");
        assert!(trust_ir::parser::parse_module(&text).is_err(), "{suffix}");
    }
}

#[test]
fn explicit_function_ids_report_duplicates_without_retiring_entry_loss() {
    let duplicate = module(&[11, 11]);
    assert_eq!(
        trust_ir::text_loss::text_losses(&duplicate),
        vec![trust_ir::format::TextLoss::DuplicateFunctionId {
            index: 1,
            id: FuncId::new(11)
        }]
    );
    assert!(trust_ir::format::text_checked(&duplicate).is_err());
    assert!(trust_ir::parser::parse_module(&duplicate.to_string()).is_err());
    let mut entry = module(&[11]);
    entry.functions[0].entry = BlockId::new(3);
    assert_eq!(
        trust_ir::text_loss::text_losses(&entry),
        vec![trust_ir::format::TextLoss::EntryBlock {
            func: FuncId::new(11)
        }]
    );
}
