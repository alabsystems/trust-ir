// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public module validation must agree with shared edge-defined SSA semantics.

use trust_ir::{BlockId, Constant, Inst, InstrNode, Module, Ty, ValueId};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

fn fixture() -> Module {
    let mut module = ModuleBuilder::new("invoke_edge_ssa");
    let signature = module.add_func_type(vec![], vec![Ty::I32]);
    let callee = {
        let mut function = module.function("callee", signature);
        let entry = function.create_block();
        function.switch_to_block(entry);
        let zero = function.iconst(Ty::I32, 0);
        function.ret(vec![zero]);
        function.build()
    };
    let mut function = module.function("caller", signature);
    let entry = function.create_block();
    let normal = function.create_block();
    let unwind = function.create_block();
    function.switch_to_block(entry);
    let result = function.invoke(callee, vec![], normal, vec![], unwind);
    function.switch_to_block(normal);
    function.ret(vec![result]);
    function.switch_to_block(unwind);
    let (exception, _) = function.landingpad(true, vec![]);
    function.resume(exception);
    function.build();
    module.build().expect("ModuleBuilder::build: test fixture")
}

fn result(module: &Module) -> ValueId {
    module.functions[1].blocks[0].body[0].results[0]
}

#[test]
fn module_accepts_invoke_result_only_on_normal_edge_and_normal_dominated_uses() {
    let mut module = fixture();
    assert_eq!(validate_module(&module), []);
    let value = result(&module);
    let function = &mut module.functions[1];
    let phi = ValueId::new(100);
    function.blocks[1].params.push((phi, Ty::I32));
    function.blocks[1].body[0] = InstrNode::new(Inst::Return { values: vec![phi] });
    let Inst::Invoke { normal_args, .. } = &mut function.blocks[0].body[0].inst else {
        unreachable!()
    };
    normal_args.push(value);
    assert_eq!(validate_module(&module), []);
    // Reordering physical storage does not change the actual CFG edge.
    module.functions[1].blocks.reverse();
    assert_eq!(validate_module(&module), []);
}

#[test]
fn module_rejects_unwind_and_preinvoke_uses_without_confusing_normal_arguments() {
    let mut module = fixture();
    let value = result(&module);
    module.functions[1].blocks[2].body.insert(
        1,
        InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand: value,
        })
        .with_result(ValueId::new(100)),
    );
    assert!(
        validate_module(&module).contains(&ValidationError::UseBeforeDefInBlock {
            value: value.index(),
            block: 2,
        })
    );
    let mut module = fixture();
    let value = result(&module);
    // The exact same result occurring as a call argument is before the call,
    // even if it also occurs as a valid normal-edge argument.
    let function = &mut module.functions[1];
    function.blocks[1].params.push((ValueId::new(100), Ty::I32));
    let Inst::Invoke {
        args, normal_args, ..
    } = &mut function.blocks[0].body[0].inst
    else {
        unreachable!()
    };
    args.push(value);
    normal_args.push(value);
    let errors = validate_module(&module);
    assert_eq!(errors.iter().filter(|error| matches!(error,
        ValidationError::UseBeforeDefInBlock { value: used, block: 0 } if *used == value.index()
    )).count(), 1);
}

#[test]
fn module_accepts_normal_result_inside_loops_but_rejects_alternate_entry() {
    let mut module = fixture();
    let value = result(&module);
    let function = &mut module.functions[1];
    let normal = function.blocks[1].id;
    let mut loop_body = trust_ir::Block::new(BlockId::new(100));
    loop_body.body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand: value,
        })
        .with_result(ValueId::new(100)),
    );
    loop_body.body.push(InstrNode::new(Inst::Br {
        target: normal,
        args: vec![],
    }));
    function.blocks[1].body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(false),
        })
        .with_result(ValueId::new(101)),
        InstrNode::new(Inst::CondBr {
            cond: ValueId::new(101),
            then_target: BlockId::new(100),
            then_args: vec![],
            else_target: BlockId::new(101),
            else_args: vec![],
        }),
    ];
    let mut done = trust_ir::Block::new(BlockId::new(101));
    done.body.push(InstrNode::new(Inst::Return {
        values: vec![value],
    }));
    function.blocks.extend([loop_body, done]);
    assert_eq!(validate_module(&module), []);
    // A catch path can now reach the normal region without a normal return.
    module.functions[1].blocks[2].body[1] = InstrNode::new(Inst::Br {
        target: normal,
        args: vec![],
    });
    let errors = validate_module(&module);
    for block in [100, 101] {
        assert!(errors.contains(&ValidationError::UseBeforeDefInBlock {
            value: value.index(),
            block
        }));
    }
}

#[test]
fn module_checks_invoke_normal_edge_arity_and_types_like_a_branch() {
    // `validate_block_param_arity` handled Br / CondBr / Switch and dropped
    // Invoke into `_ => {}`, so the normal edge was the one CFG edge whose
    // arguments were never counted or typed against the target's parameters.
    let mut module = fixture();
    let value = result(&module);
    let function = &mut module.functions[1];
    let phi = ValueId::new(100);
    function.blocks[1].params.push((phi, Ty::I64));
    // Arity: the continuation now takes one parameter and receives none.
    assert!(
        validate_module(&module).contains(&ValidationError::BranchArgCountMismatch {
            block: 0,
            target: 1,
            expected: 1,
            actual: 0,
        }),
        "{:?}",
        validate_module(&module)
    );
    // Type: the I32 result does not fit the I64 parameter.
    let Inst::Invoke { normal_args, .. } = &mut module.functions[1].blocks[0].body[0].inst else {
        unreachable!()
    };
    normal_args.push(value);
    assert!(
        validate_module(&module).contains(&ValidationError::BranchArgTypeMismatch {
            block: 0,
            target: 1,
            arg_index: 0,
            expected: "i64".into(),
            actual: "i32".into(),
        }),
        "{:?}",
        validate_module(&module)
    );
    // And the well-typed edge is clean.
    module.functions[1].blocks[1].params[0].1 = Ty::I32;
    assert_eq!(validate_module(&module), []);
}
