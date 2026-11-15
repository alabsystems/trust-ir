// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::dialect::{
    DialectInst,
    schema::{DialectSchema, DialectSchemaRegistry, OperationSchema},
};
use trust_ir::{DialectTy, Module, SourceSpan, Ty, ValueId};
use trust_ir_build::{
    DialectResultArityError, ModuleBuilder, validate_module_with_dialect_schemas,
};

fn nominal(name: &str) -> Ty {
    Ty::Dialect(Box::new(DialectTy::new("example", name, 1)))
}

fn operation(name: &str, results: Vec<Ty>) -> DialectInst {
    let mut operation = DialectInst::new("example", name);
    operation.result_tys = results;
    operation
}

fn build(fixed: bool) -> Module {
    let mut module = ModuleBuilder::new("dialect_results");
    let state = nominal("state");
    let outcome = nominal("outcome");
    let signature = module.add_func_type(vec![], vec![state.clone(), outcome.clone()]);
    let span = SourceSpan {
        file: module.intern_file("example.source"),
        line: 3,
        col: 1,
    };
    let mut function = module.function("entry", signature);
    let entry = function.create_block();
    let join = function.create_block();
    let joined_state = function.add_block_param(join, state.clone());
    let joined_outcome = function.add_block_param(join, outcome.clone());
    function.switch_to_block(entry);
    function.set_span(span);
    let empty = operation("zero", vec![]);
    let one = operation("one", vec![Ty::Bool]);
    let pair = operation("pair", vec![state, outcome]);
    let results = if fixed {
        assert_eq!(function.dialect_results::<0>(empty).unwrap(), []);
        assert_eq!(
            function.dialect_results::<1>(one).unwrap(),
            [ValueId::new(2)]
        );
        function.dialect_results::<2>(pair).unwrap()
    } else {
        assert_eq!(function.dialect_op(empty), vec![]);
        assert_eq!(function.dialect_op(one), vec![ValueId::new(2)]);
        function.dialect_op(pair).try_into().unwrap()
    };
    assert_eq!(results, [ValueId::new(3), ValueId::new(4)]);
    function.br(join, results.to_vec());
    function.switch_to_block(join);
    function.ret(vec![joined_state, joined_outcome]);
    function.build();
    module.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn fixed_dialect_results_preserve_zero_single_pair_ssa_metadata_and_legacy_identity() {
    let module = build(true);
    assert_eq!(module, build(false));
    assert_eq!(module.stable_digest(), build(false).stable_digest());
    let registry = DialectSchemaRegistry::new([DialectSchema {
        namespace: "example".into(),
        version: 1,
        operations: [
            operation("zero", vec![]),
            operation("one", vec![Ty::Bool]),
            operation("pair", vec![nominal("state"), nominal("outcome")]),
        ]
        .into_iter()
        .map(|op| OperationSchema {
            name: op.op,
            operands: vec![],
            results: op.result_tys,
            attributes: vec![],
        })
        .collect(),
    }])
    .unwrap();
    assert_eq!(
        validate_module_with_dialect_schemas(&module, &registry),
        vec![]
    );
    for node in &module.functions[0].blocks[0].body[..3] {
        assert!(node.span.is_some());
        assert!(node.proofs.is_empty());
    }
}

#[test]
fn arity_failure_does_not_consume_ssa_ids_or_emit_partial_operations() {
    let mut module = ModuleBuilder::new("arity_failure");
    let signature = module.add_func_type(vec![], vec![Ty::Bool]);
    let mut function = module.function("entry", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    assert_eq!(
        function.dialect_results::<2>(operation("one", vec![Ty::Bool])),
        Err(DialectResultArityError {
            expected: 2,
            actual: 1
        })
    );
    assert_eq!(
        function.dialect_results::<0>(operation("one", vec![Ty::Bool])),
        Err(DialectResultArityError {
            expected: 0,
            actual: 1
        })
    );
    assert!(function.last_emitted_position().is_none());
    let [value] = function
        .dialect_results::<1>(operation("one", vec![Ty::Bool]))
        .unwrap();
    assert_eq!(value, ValueId::new(0));
    function.ret(vec![value]);
    function.build();
    assert_eq!(
        module
            .build()
            .expect("ModuleBuilder::build: test fixture")
            .functions[0]
            .blocks[0]
            .body
            .len(),
        2
    );
}
