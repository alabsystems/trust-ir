// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::{
    Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, SpecAnchor, SpecModule,
    SpecProjectionTarget, Ty,
};
use trust_ir_build::{ValidationError, validate_module, validate_spec_anchor_functions};

fn module_with_action_function() -> Module {
    let mut module = Module::new("typed_anchor");
    let ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "crate::Machine::step", ty, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(entry);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");

    let mut spec = SpecModule::new("crate::Machine");
    spec.actions.push("Step".to_string());
    spec.anchors.push(SpecAnchor {
        machine: "crate::Machine".to_string(),
        action: "Step".to_string(),
        rust_symbol: "crate::Machine::step".to_string(),
        span: "fixture.rs:1:1".to_string(),
        project: Some("fixture::project".to_string()),
        function: Some(FuncId::new(0)),
        projection_target: None,
    });
    module.spec_modules.push(spec);
    module
}

fn module_with_projection_function(signature: FuncTy) -> Module {
    let mut module = module_with_action_function();
    let ty = module
        .add_func_type(signature)
        .expect("Module::add_func_type: test fixture");
    let mut projection = Function::new(
        FuncId::new(1),
        "crate::Machine::project",
        ty,
        BlockId::new(0),
    );
    let mut entry = Block::new(BlockId::new(0));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    projection.blocks.push(entry);
    module
        .try_add_function(projection)
        .expect("Module::try_add_function: test fixture");
    module.spec_modules[0].anchors[0].project = Some("crate::Machine::project".to_string());
    module.spec_modules[0].anchors[0].projection_target =
        Some(SpecProjectionTarget::Function(FuncId::new(1)));
    module
}

fn valid_projection_signature() -> FuncTy {
    FuncTy {
        params: vec![Ty::Ref(Box::new(Ty::I32))],
        returns: vec![Ty::I32],
        abi: None,
        is_vararg: false,
    }
}

#[test]
fn typed_spec_anchor_accepts_exact_body_function() {
    let errors = validate_module(&module_with_action_function());
    assert!(
        !errors
            .iter()
            .any(|error| matches!(error, ValidationError::InvalidSpecAnchorFunction { .. })),
        "exact typed anchor should validate: {errors:?}"
    );
}

#[test]
fn typed_spec_anchor_rejects_out_of_range_function() {
    let mut module = module_with_action_function();
    module.spec_modules[0].anchors[0].function = Some(FuncId::new(9));
    assert!(validate_module(&module).iter().any(|error| matches!(
        error,
        ValidationError::InvalidSpecAnchorFunction { function: 9, .. }
    )));
}

#[test]
fn typed_spec_anchor_rejects_bodyless_declaration() {
    let mut module = module_with_action_function();
    module.functions[0].blocks.clear();
    assert!(validate_module(&module).iter().any(|error| matches!(
        error,
        ValidationError::InvalidSpecAnchorFunction { function: 0, detail, .. }
            if detail.contains("bodyless declaration")
    )));
}

#[test]
fn typed_spec_anchor_rejects_mismatched_source_identity() {
    let mut module = module_with_action_function();
    module.spec_modules[0].anchors[0].rust_symbol = "crate::Other::step".to_string();
    assert!(validate_module(&module).iter().any(|error| matches!(
        error,
        ValidationError::InvalidSpecAnchorFunction { function: 0, detail, .. }
            if detail.contains("does not match")
    )));
}

#[test]
fn typed_spec_projection_accepts_exact_body_name_and_signature() {
    let module = module_with_projection_function(valid_projection_signature());
    assert!(
        validate_spec_anchor_functions(&module).is_empty(),
        "exact typed action and projection should validate"
    );
    assert!(
        !validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::InvalidSpecProjectionFunction { .. }))
    );
}

#[test]
fn typed_spec_projection_rejects_missing_body_and_stale_identity() {
    let mut missing = module_with_projection_function(valid_projection_signature());
    missing.functions[1].blocks.clear();
    assert!(
        validate_spec_anchor_functions(&missing)
            .iter()
            .any(|error| matches!(
                error,
                ValidationError::InvalidSpecProjectionFunction { function: 1, detail, .. }
                    if detail.contains("bodyless declaration")
            ))
    );

    let mut stale = module_with_projection_function(valid_projection_signature());
    stale.spec_modules[0].anchors[0].project = Some("crate::Other::project".to_string());
    assert!(
        validate_spec_anchor_functions(&stale)
            .iter()
            .any(|error| matches!(
                error,
                ValidationError::InvalidSpecProjectionFunction { function: 1, detail, .. }
                    if detail.contains("does not match")
            ))
    );
}

#[test]
fn typed_spec_projection_rejects_missing_target_and_every_bad_signature_shape() {
    let mut missing = module_with_projection_function(valid_projection_signature());
    missing.spec_modules[0].anchors[0].projection_target =
        Some(SpecProjectionTarget::Function(FuncId::new(99)));
    assert!(validate_module(&missing).iter().any(|error| matches!(
        error,
        ValidationError::InvalidSpecProjectionFunction { function: 99, .. }
    )));

    let bad_signatures = [
        FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        },
        FuncTy {
            params: vec![Ty::RefMut(Box::new(Ty::I32))],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        },
        FuncTy {
            params: vec![Ty::Ref(Box::new(Ty::I32)), Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        },
        FuncTy {
            params: vec![Ty::Ref(Box::new(Ty::I32))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        },
        FuncTy {
            params: vec![Ty::Ref(Box::new(Ty::I32))],
            returns: vec![Ty::I32, Ty::I32],
            abi: None,
            is_vararg: false,
        },
        FuncTy {
            params: vec![Ty::Ref(Box::new(Ty::I32))],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: true,
        },
    ];
    for signature in bad_signatures {
        let errors = validate_spec_anchor_functions(&module_with_projection_function(signature));
        assert!(
            errors.iter().any(|error| matches!(
                error,
                ValidationError::InvalidSpecProjectionFunction { detail, .. }
                    if detail.contains("(&T) -> R")
            )),
            "bad projection signature must fail: {errors:?}"
        );
    }
}
