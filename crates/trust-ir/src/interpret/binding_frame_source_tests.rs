// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::inst::{BindingFrameDef, BindingSlot};
use crate::value::BindingFrameId;

fn source() -> (Module, Arc<InterpretBindingFrameOrigin>) {
    let mut module = Module::new("frame-source-declarations");
    let item_signature = module
        .add_func_type(crate::FuncTy::unrecorded(vec![], vec![], false))
        .unwrap();
    let item = Function::new(FuncId::new(7), "item", item_signature, BlockId::new(0));
    module.functions.push(item);
    let declaration = BindingFrameDef::new(
        BindingFrameId::new(3),
        "source",
        vec![BindingSlot::new("item", Ty::FnItem(FuncId::new(7)))],
    );
    let mut function = Function::new(FuncId::new(53), "origin", item_signature, BlockId::new(0));
    let mut block = crate::Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::OpenFrame {
            def: declaration.clone(),
        })
        .with_result(ValueId::new(0)),
    );
    function.blocks.push(block);
    module.functions.push(function);
    (
        module,
        Arc::new(InterpretBindingFrameOrigin {
            function: FuncId::new(53),
            declaration,
        }),
    )
}

fn item() -> InterpretValue {
    InterpretValue {
        ty: Ty::FnItem(FuncId::new(7)),
        kind: InterpretValueKind::FnItem(FuncId::new(7)),
    }
}

#[test]
fn source_bound_frame_checks_declared_slots_and_preserves_unwritten_transport() {
    let (module, origin) = source();
    let interpreter = Interpreter::with_module(&module);
    for slot in [
        None,
        Some(item()),
        Some(InterpretValue {
            ty: Ty::Unit,
            kind: InterpretValueKind::Uninit,
        }),
    ] {
        let value = frame_handle(0, origin.clone(), Arc::from(vec![slot]));
        interpreter
            .validate_function_items(&value, BlockId::new(0))
            .unwrap();
    }
    // Self-reported child.ty is insufficient: declared slot 0 requires item7.
    let hidden = frame_handle(
        0,
        origin.clone(),
        Arc::from(vec![Some(InterpretValue {
            ty: Ty::Unit,
            kind: InterpretValueKind::Unit,
        })]),
    );
    assert_eq!(
        interpreter
            .validate_function_items(&hidden, BlockId::new(0))
            .unwrap_err()
            .code,
        InterpretErrorCode::TypeError
    );
    let short = frame_handle(0, origin.clone(), Arc::from(vec![]));
    assert_eq!(
        interpreter
            .validate_function_items(&short, BlockId::new(0))
            .unwrap_err()
            .code,
        InterpretErrorCode::TypeError
    );
    let mut wrong_kind = frame_handle(0, origin, Arc::from(vec![Some(item())]));
    wrong_kind.ty = Ty::Unit;
    assert_eq!(
        interpreter
            .validate_function_items(&wrong_kind, BlockId::new(0))
            .unwrap_err()
            .code,
        InterpretErrorCode::TypeError
    );
}

#[test]
fn source_bound_frame_rejects_missing_changed_and_ambiguous_origins() {
    let (source_module, origin) = source();
    let value = frame_handle(0, origin.clone(), Arc::from(vec![Some(item())]));
    let mut missing = source_module.clone();
    missing
        .functions
        .retain(|function| function.id != origin.function);
    let mut changed = source_module.clone();
    if let Inst::OpenFrame { def } = &mut changed.functions[1].blocks[0].body[0].inst {
        def.slots[0].ty = Ty::Unit;
    }
    let mut duplicate_function = source_module.clone();
    duplicate_function
        .functions
        .push(source_module.functions[1].clone());
    let mut duplicate_frame = source_module.clone();
    let duplicate = duplicate_frame.functions[1].blocks[0].body[0].clone();
    duplicate_frame.functions[1].blocks[0].body.push(duplicate);
    for module in [&missing, &changed, &duplicate_function, &duplicate_frame] {
        assert_eq!(
            Interpreter::with_module(module)
                .validate_function_items(&value, BlockId::new(0))
                .unwrap_err()
                .code,
            InterpretErrorCode::TypeError
        );
    }
    let absent = InterpretValue {
        ty: Ty::Ptr,
        kind: InterpretValueKind::Frame {
            lineage: 0,
            origin: None,
            slots: Arc::from(vec![Some(item())]),
        },
    };
    assert_eq!(
        Interpreter::with_module(&source_module)
            .validate_function_items(&absent, BlockId::new(0))
            .unwrap_err()
            .code,
        InterpretErrorCode::TypeError
    );
}
