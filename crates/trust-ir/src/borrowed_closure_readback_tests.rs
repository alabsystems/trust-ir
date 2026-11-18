// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use crate::{ClosureLayoutDescriptor, ClosureTy, Constant, FuncTy, Function, InstrNode};

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn f(id: u32) -> FuncId {
    FuncId::new(id)
}
fn node(inst: Inst, result: Option<u32>) -> InstrNode {
    let node = InstrNode::new(inst);
    match result {
        Some(id) => node.with_result(v(id)),
        None => node,
    }
}
fn fixture(captured: bool, result: i128) -> Module {
    let mut module = Module::new("original_borrowed_closure");
    module.target_info = Some(crate::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: crate::Endianness::Little,
        abi: None,
        struct_passing: crate::StructPassingPolicy::Unclassified,
    });
    let nominal = ClosureTyId::new(0);
    let captures = if captured { vec![Ty::U64] } else { vec![] };
    let apparent = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let target = module
        .add_func_type(FuncTy {
            params: captures.clone(),
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let borrower = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Closure(nominal)],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let caller = module
        .add_func_type(FuncTy {
            params: captures.clone(),
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    module.closure_types.push(ClosureTy {
        func: apparent,
        captures,
    });
    let align = if captured { 8 } else { 1 };
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: nominal,
        size: if captured { 8 } else { 0 },
        align,
        capture_offsets: if captured { vec![0] } else { vec![] },
    });
    let mut entry = Function::new(f(0), "entry", caller, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    if captured {
        block.params.push((v(0), Ty::U64));
    }
    block.body = vec![
        node(
            Inst::MakeClosure {
                ty: nominal,
                func: f(1),
                captures: if captured { vec![v(0)] } else { vec![] },
            },
            Some(1),
        ),
        node(
            Inst::Alloca {
                ty: Ty::Closure(nominal),
                count: None,
                align: Some(align),
            },
            Some(2),
        ),
        node(
            Inst::Store {
                ty: Ty::Closure(nominal),
                ptr: v(2),
                value: v(1),
                volatile: false,
                align: Some(align),
            },
            None,
        ),
        node(
            Inst::Call {
                callee: f(2),
                args: vec![v(2)],
            },
            Some(3),
        ),
        node(
            Inst::CallIndirect {
                callee: v(3),
                sig: apparent,
                args: vec![],
                calling_conv: crate::CallingConv::C,
            },
            Some(4),
        ),
        node(Inst::Return { values: vec![v(4)] }, None),
    ];
    entry.blocks.push(block);
    let mut code = Function::new(f(1), "closure_body", target, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    if captured {
        block.params.push((v(0), Ty::U64));
        block
            .body
            .push(node(Inst::Return { values: vec![v(0)] }, None));
    } else {
        block.body.push(node(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(result),
            },
            Some(0),
        ));
        block
            .body
            .push(node(Inst::Return { values: vec![v(0)] }, None));
    }
    code.blocks.push(block);
    let mut readback = Function::new(f(2), "borrowed_readback", borrower, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0)).with_param(v(0), Ty::Ptr);
    block.body = vec![
        node(
            Inst::Load {
                ty: Ty::Closure(nominal),
                ptr: v(0),
                volatile: false,
                align: Some(align),
            },
            Some(1),
        ),
        node(Inst::Return { values: vec![v(1)] }, None),
    ];
    readback.blocks.push(block);
    module.functions = vec![entry, code, readback];
    for function in &mut module.functions {
        function.linkage = crate::Linkage::Internal;
    }
    module
}
fn run(module: &Module, captured: Option<i128>) -> i128 {
    let args = captured
        .into_iter()
        .map(|value| InterpretValue::int(Ty::U64, value).unwrap());
    let outcome = Interpreter::with_module(module)
        .execute_func(f(0), args)
        .unwrap();
    assert_eq!(outcome.host_calls, 0);
    outcome.returns[0].as_int().unwrap().as_signed()
}

#[test]
fn original_borrowed_closure_query_retains_actual_store_and_full_nominal_value_path() {
    for captured in [false, true] {
        for value in [37, 42] {
            let source = fixture(captured, value);
            let readback = source.borrowed_closure_readback(f(0), v(3)).unwrap();
            assert!(std::ptr::eq(readback.module(), &source));
            assert_eq!(readback.nominal(), ClosureTyId::new(0));
            assert_eq!(readback.binding().target, f(1));
            let captured_values = [v(0)];
            assert_eq!(
                readback.capture_values(),
                if captured { &captured_values[..] } else { &[] }
            );
            assert_eq!(readback.slot(), v(2));
            assert_eq!(readback.stored_value(), v(1));
            assert_eq!(readback.constructor().instruction(), 0);
            assert_eq!(readback.store().instruction(), 2);
            assert_eq!(readback.call().instruction(), 3);
            assert_eq!(readback.load().function(), f(2));
            assert_eq!(readback.returned().instruction(), 1);
            assert_eq!(run(&source, captured.then_some(value)), value);
        }
    }
}

#[test]
fn original_borrowed_closure_query_keeps_real_pointer_capture_allocation_and_readback() {
    let mut source = fixture(true, 0);
    source.closure_types[0].captures[0] = Ty::Ptr;
    let signature = source
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    for index in [0, 1] {
        source.functions[index].ty = signature;
        source.functions[index].blocks[0].params[0].1 = Ty::Ptr;
    }
    source.functions[1].blocks[0].body = vec![
        node(
            Inst::Load {
                ty: Ty::U64,
                ptr: v(0),
                volatile: false,
                align: Some(8),
            },
            Some(1),
        ),
        node(Inst::Return { values: vec![v(1)] }, None),
    ];
    // The pointer argument comes from real canonical Alloca/Store actions,
    // never an invented allocation id or a host pointer cast into an integer.
    let signature = source
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut wrapper = Function::new(f(3), "allocated_pointer_entry", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0)).with_param(v(0), Ty::U64);
    block.body = vec![
        node(
            Inst::Alloca {
                ty: Ty::U64,
                count: None,
                align: Some(8),
            },
            Some(1),
        ),
        node(
            Inst::Store {
                ty: Ty::U64,
                ptr: v(1),
                value: v(0),
                volatile: false,
                align: Some(8),
            },
            None,
        ),
        node(
            Inst::Call {
                callee: f(0),
                args: vec![v(1)],
            },
            Some(2),
        ),
        node(Inst::Return { values: vec![v(2)] }, None),
    ];
    wrapper.blocks.push(block);
    source.functions.push(wrapper);
    let path = source.borrowed_closure_readback(f(0), v(3)).unwrap();
    assert_eq!(path.binding().captures, &[Ty::Ptr]);
    assert_eq!(path.capture_values(), &[v(0)]);
    for value in [37, 42] {
        let outcome = Interpreter::with_module(&source)
            .execute_func(f(3), [InterpretValue::int(Ty::U64, value).unwrap()])
            .unwrap();
        assert_eq!(outcome.host_calls, 0);
        assert_eq!(outcome.returns[0].as_int().unwrap().as_signed(), value);
    }
}

#[test]
fn original_borrowed_closure_query_keeps_uninitialized_empty_cell_and_other_origin_refusals() {
    let mut source = fixture(false, 37);
    source.functions[0].blocks[0].body.remove(2);
    assert!(
        source.borrowed_closure_readback(f(0), v(3)).is_err(),
        "zero bytes cannot replace a Store"
    );
    let mut source = fixture(true, 37);
    source.functions[0].blocks[0].body.insert(
        2,
        node(
            Inst::Alloca {
                ty: Ty::Closure(ClosureTyId::new(0)),
                count: None,
                align: Some(8),
            },
            Some(9),
        ),
    );
    if let Inst::Call { args, .. } = &mut source.functions[0].blocks[0].body[4].inst {
        args[0] = v(9);
    }
    assert!(
        source.borrowed_closure_readback(f(0), v(3)).is_err(),
        "another same-shaped allocation was not stored"
    );
}

#[test]
fn original_borrowed_closure_query_does_not_promote_incoming_same_shape_targets() {
    for imported in [f(1), f(3)] {
        let mut source = fixture(false, 37);
        let mut impostor = source.functions[1].clone();
        impostor.id = f(3);
        impostor.name = "same_shape_other_code".into();
        source.functions.push(impostor);
        let signature = source
            .add_func_type(FuncTy {
                params: vec![Ty::Closure(ClosureTyId::new(0))],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            })
            .unwrap();
        source.functions[0].ty = signature;
        source.functions[0].blocks[0]
            .params
            .push((v(8), Ty::Closure(ClosureTyId::new(0))));
        if let Inst::Store { value, .. } = &mut source.functions[0].blocks[0].body[2].inst {
            *value = v(8);
        }
        assert!(
            source.borrowed_closure_readback(f(0), v(3)).is_err(),
            "unused constructor census cannot authorize the imported value"
        );
        let actual = Interpreter::with_module(&source).execute_func(
            f(0),
            [InterpretValue {
                ty: Ty::Closure(ClosureTyId::new(0)),
                kind: InterpretValueKind::Closure {
                    func: imported,
                    captures: vec![],
                },
            }],
        );
        if imported == f(1) {
            assert!(actual.is_ok());
        } else {
            assert!(
                actual.is_err(),
                "canonical Store still refuses the other target"
            );
        }
    }
}

#[test]
fn original_borrowed_closure_query_refuses_a_writing_callee_even_with_same_return() {
    let mut source = fixture(true, 0);
    source.functions[2].blocks[0].body.insert(
        1,
        node(
            Inst::Store {
                ty: Ty::Closure(ClosureTyId::new(0)),
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: Some(8),
            },
            None,
        ),
    );
    assert_eq!(run(&source, Some(42)), 42);
    assert!(
        source.borrowed_closure_readback(f(0), v(3)).is_err(),
        "value equality cannot replace a memory relation"
    );
}

#[test]
fn original_borrowed_closure_query_preserves_count_alignment_layout_and_unreachable_use_guards() {
    for mutant in 0..7 {
        let mut source = fixture(true, 0);
        match mutant {
            0 => {
                if let Inst::Alloca { count, .. } = &mut source.functions[0].blocks[0].body[1].inst
                {
                    *count = Some(v(0));
                }
            }
            1 => {
                if let Inst::Load { align, .. } = &mut source.functions[2].blocks[0].body[0].inst {
                    *align = Some(1);
                }
            }
            2 => source.closure_layouts[0].capture_offsets[0] = 1,
            3 => {
                let mut block = Block::new(BlockId::new(99));
                block.body.push(node(
                    Inst::Copy {
                        ty: Ty::Ptr,
                        operand: v(2),
                    },
                    Some(98),
                ));
                source.functions[0].blocks.push(block);
            }
            4 => {
                let mut block = Block::new(BlockId::new(99));
                block.body.push(node(
                    Inst::Const {
                        ty: Ty::U64,
                        value: Constant::Int(0),
                    },
                    Some(2),
                ));
                source.functions[0].blocks.push(block);
            }
            5 => source.functions[0].blocks[0].params[0].1 = Ty::Bool,
            6 => source.functions.push(source.functions[2].clone()),
            _ => unreachable!(),
        }
        assert!(
            source.borrowed_closure_readback(f(0), v(3)).is_err(),
            "mutant {mutant}"
        );
    }
}
