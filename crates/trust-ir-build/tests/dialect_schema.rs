// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::dialect::{
    DialectInst,
    schema::{DialectSchema, DialectSchemaRegistry, OperandType, OperationSchema},
};
use trust_ir::{
    Block, BlockId, DialectTy, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};
use trust_ir_build::{ValidationError, validate_module, validate_module_with_dialect_schemas};

#[test]
fn function_operand_pattern_checks_the_actual_module_signature_and_function_identity() {
    let mut builder = trust_ir_build::ModuleBuilder::new("typed_callback");
    let signature = builder.add_func_type(vec![value_ty()], vec![value_ty()]);
    let mut helper = builder.function("helper", signature);
    let entry = helper.create_block();
    let parameter = helper.add_block_param(entry, value_ty());
    helper.switch_to_block(entry);
    helper.ret(vec![parameter]);
    let target = helper.build();
    let main_signature = builder.add_func_type(vec![], vec![]);
    let mut main = builder.function("main", main_signature);
    let entry = main.create_block();
    main.switch_to_block(entry);
    let function = main.fn_addr(signature, target);
    main.dialect_results::<0>(DialectInst::new("example", "capture").with_operand(function))
        .unwrap();
    main.ret(vec![]);
    main.build();
    let registry = DialectSchemaRegistry::new([DialectSchema {
        namespace: "example".into(),
        version: 1,
        operations: vec![OperationSchema {
            name: "capture".into(),
            operands: vec![OperandType::Function {
                params: vec![value_ty()],
                returns: vec![value_ty()],
            }],
            results: vec![],
            attributes: vec![],
        }],
    }])
    .unwrap();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(
        validate_module_with_dialect_schemas(&module, &registry),
        vec![]
    );
    let mut bad = module.clone();
    let Inst::Const { value, .. } = &mut bad.functions[1].blocks[0].body[0].inst else {
        unreachable!()
    };
    *value = trust_ir::Constant::FnDef(FuncId::new(999));
    assert!(
        validate_module_with_dialect_schemas(&bad, &registry)
            .iter()
            .any(|error| matches!(error, ValidationError::ConstTypeMismatch { .. }))
    );
    let mut bad = module.clone();
    let wrong_signature = bad
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let Inst::Const { ty, .. } = &mut bad.functions[1].blocks[0].body[0].inst else {
        unreachable!()
    };
    *ty = Ty::Func(wrong_signature);
    let errors = validate_module_with_dialect_schemas(&bad, &registry);
    assert!(
        errors
            .iter()
            .any(|error| matches!(error, ValidationError::ConstTypeMismatch { .. }))
    );
    assert!(
        errors
            .iter()
            .any(|error| matches!(error, ValidationError::InvalidDialectSchema { .. }))
    );
}

fn value_ty() -> Ty {
    Ty::Dialect(Box::new(DialectTy {
        namespace: "example".into(),
        name: "value".into(),
        version: 1,
    }))
}

fn schemas() -> DialectSchemaRegistry {
    DialectSchemaRegistry::new([DialectSchema {
        namespace: "example".into(),
        version: 1,
        operations: vec![OperationSchema {
            name: "identity".into(),
            operands: vec![value_ty().into()],
            results: vec![value_ty()],
            attributes: vec![],
        }],
    }])
    .unwrap()
}

fn module() -> Module {
    let mut module = Module::new("semantic_calls");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![value_ty()],
            returns: vec![value_ty()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut helper = Function::new(FuncId::new(0), "helper", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), value_ty());
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    helper.blocks.push(entry);
    module
        .try_add_function(helper)
        .expect("Module::try_add_function: test fixture");
    let mut caller = Function::new(FuncId::new(1), "caller", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), value_ty());
    entry.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(1)],
    }));
    let mut join = Block::new(BlockId::new(1)).with_param(ValueId::new(2), value_ty());
    join.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(
            DialectInst::new("example", "identity")
                .with_operand(ValueId::new(2))
                .with_result_ty(value_ty()),
        )))
        .with_result(ValueId::new(3)),
    );
    join.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(3)],
    }));
    // Non-topological storage ensures checking uses the complete SSA map.
    caller.blocks = vec![join, entry];
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn schema_checks_actual_call_and_block_parameter_types_without_an_extra_type_map() {
    let module = module();
    assert_eq!(
        validate_module_with_dialect_schemas(&module, &schemas()),
        vec![]
    );
    assert!(module.proof_obligations.is_empty());
    assert!(module.proof_certificates.is_empty());
}

#[test]
fn opaque_roundtrip_does_not_admit_unknown_operations_into_closed_schema() {
    let mut module = module();
    let Inst::DialectOp(op) = &mut module.functions[1].blocks[0].body[0].inst else {
        unreachable!()
    };
    op.op = "unknown".into();
    assert!(validate_module(&module).is_empty());
    assert!(
        validate_module_with_dialect_schemas(&module, &schemas())
            .iter()
            .any(|error| matches!(error, ValidationError::InvalidDialectSchema { .. }))
    );
}

#[test]
fn schema_reads_the_actual_call_result_type_not_the_operations_claim() {
    let mut module = module();
    let scalar_sig = module
        .add_func_type(FuncTy {
            params: vec![value_ty()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.functions[0].ty = scalar_sig;
    // Route the operation directly from the call result, with the declaration
    // deliberately lying that its operand still has the nominal value type.
    let caller = &mut module.functions[1];
    let mut op_node = caller.blocks[0].body.remove(0);
    let Inst::DialectOp(op) = &mut op_node.inst else {
        unreachable!()
    };
    op.operands[0] = ValueId::new(1);
    caller.blocks[1].body.insert(1, op_node);
    let errors = validate_module_with_dialect_schemas(&module, &schemas());
    assert!(errors.iter().any(|error| matches!(error,
        ValidationError::InvalidDialectSchema { reason, .. } if reason.contains("OperandType"))));
}

fn variadic_schema() -> DialectSchemaRegistry {
    DialectSchemaRegistry::new([DialectSchema {
        namespace: "example".into(),
        version: 1,
        operations: vec![OperationSchema {
            name: "collect".into(),
            operands: vec![value_ty().into(), OperandType::VariadicExact(value_ty())],
            results: vec![value_ty()],
            attributes: vec![],
        }],
    }])
    .unwrap()
}

fn variadic_module(tail_count: usize) -> Module {
    let mut builder = trust_ir_build::ModuleBuilder::new("variadic_operands");
    let signature = builder.add_func_type(vec![value_ty(), Ty::U64], vec![value_ty()]);
    let mut function = builder.function("collect", signature);
    let entry = function.create_block();
    let value = function.add_block_param(entry, value_ty());
    function.add_block_param(entry, Ty::U64);
    function.switch_to_block(entry);
    let [result] = function
        .dialect_results::<1>(
            DialectInst::new("example", "collect")
                .with_operands(std::iter::repeat_n(value, tail_count + 1))
                .with_result_ty(value_ty()),
        )
        .unwrap();
    function.ret(vec![result]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn variadic_schema_checks_actual_ssa_for_empty_and_wide_tails_without_evidence() {
    let schemas = variadic_schema();
    for count in [0, 1, 1024] {
        let module = variadic_module(count);
        assert_eq!(
            validate_module_with_dialect_schemas(&module, &schemas),
            vec![]
        );
        assert!(module.proof_obligations.is_empty());
        assert!(module.proof_certificates.is_empty());
        assert!(module.functions[0].proofs.is_empty());
        assert!(module.functions[0].blocks[0].body[0].proofs.is_empty());
    }
}

#[test]
fn variadic_schema_rejects_wrong_late_type_undefined_tail_and_missing_prefix() {
    let schemas = variadic_schema();
    for (mutation, reason) in [
        (0, "OperandType { index: 2"),
        (1, "UndefinedOperand(ValueId(999))"),
        (2, "OperandCountAtLeast { minimum: 1, actual: 0 }"),
    ] {
        let mut module = variadic_module(2);
        let Inst::DialectOp(op) = &mut module.functions[0].blocks[0].body[0].inst else {
            unreachable!()
        };
        match mutation {
            0 => op.operands[2] = ValueId::new(1),
            1 => op.operands[2] = ValueId::new(999),
            _ => op.operands.clear(),
        }
        assert!(
            validate_module_with_dialect_schemas(&module, &schemas)
                .iter()
                .any(|error| matches!(error,
                ValidationError::InvalidDialectSchema { reason: actual, .. }
                if actual.contains(reason)))
        );
    }
}
