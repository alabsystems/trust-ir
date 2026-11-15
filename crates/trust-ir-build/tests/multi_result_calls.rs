// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::{CallingConv, DialectTy, FuncId, Inst, Module, ScopeData, SourceSpan, Ty, ValueId};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

fn nominal(name: &str) -> Ty {
    Ty::Dialect(Box::new(DialectTy::new("example", name, 1)))
}

#[test]
fn direct_results_support_nominal_forward_and_self_calls_and_cfg_joins() {
    let mut module = ModuleBuilder::new("nominal_forward_calls");
    let state = nominal("evaluation_state");
    let outcome = nominal("outcome");
    let signature = module.add_func_type(
        vec![state.clone(), outcome.clone()],
        vec![state.clone(), outcome.clone()],
    );
    let span = SourceSpan {
        file: module.intern_file("example.source"),
        line: 12,
        col: 3,
    };
    let caller_id = module
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let forward_id = FuncId::new(caller_id.index() + 1);
    let mut caller = module.function("caller", signature);
    let entry = caller.create_block();
    let join = caller.create_block();
    let input_state = caller.add_block_param(entry, state.clone());
    let input_outcome = caller.add_block_param(entry, outcome.clone());
    let joined_state = caller.add_block_param(join, state.clone());
    let joined_outcome = caller.add_block_param(join, outcome.clone());
    caller.set_scopes(vec![ScopeData {
        parent: None,
        span: Some(span),
        inlined_at: None,
    }]);
    caller.set_scope(0);
    caller.set_span(span);
    caller.switch_to_block(entry);
    let forward = caller.call_results::<2>(forward_id, vec![input_state, input_outcome]);
    assert_eq!(forward, [ValueId::new(4), ValueId::new(5)]);
    let recursive = caller.call_results::<2>(caller_id, forward.to_vec());
    assert_eq!(recursive, [ValueId::new(6), ValueId::new(7)]);
    caller.br(join, recursive.to_vec());
    caller.switch_to_block(join);
    let copied = caller.copy(outcome.clone(), joined_outcome);
    assert_eq!(copied, ValueId::new(8));
    caller.ret(vec![joined_state, copied]);
    assert_eq!(caller.build(), caller_id);

    let mut helper = module.function("forward", signature);
    let entry = helper.create_block();
    let state = helper.add_block_param(entry, state);
    let outcome = helper.add_block_param(entry, outcome);
    helper.switch_to_block(entry);
    helper.ret(vec![state, outcome]);
    assert_eq!(helper.build(), forward_id);

    let module = module.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), vec![]);
    let calls = &module.functions[0].blocks[0].body[..2];
    assert_eq!(calls[0].results, forward);
    assert_eq!(calls[1].results, recursive);
    for call in calls {
        assert_eq!(call.span, Some(span));
        assert_eq!(call.scope, Some(0));
        assert!(call.proofs.is_empty());
        assert!(call.proof_context.is_none());
    }
}

#[test]
fn indirect_results_preserve_nominal_types_and_explicit_calling_conventions() {
    for convention in [CallingConv::C, CallingConv::Fast] {
        let mut module = ModuleBuilder::new("nominal_indirect_calls");
        let state = nominal("evaluation_state");
        let outcome = nominal("outcome");
        let signature = module.add_func_type(
            vec![state.clone(), outcome.clone()],
            vec![state.clone(), outcome.clone()],
        );
        let mut callee = module.function("callee", signature);
        callee.set_calling_conv(convention);
        let entry = callee.create_block();
        let s = callee.add_block_param(entry, state.clone());
        let o = callee.add_block_param(entry, outcome.clone());
        callee.switch_to_block(entry);
        callee.ret(vec![s, o]);
        let callee = callee.build();

        let mut caller = module.function("caller", signature);
        caller.set_calling_conv(convention);
        let entry = caller.create_block();
        let s = caller.add_block_param(entry, state);
        let o = caller.add_block_param(entry, outcome);
        caller.switch_to_block(entry);
        let address = caller.fn_addr(signature, callee);
        assert_eq!(address, ValueId::new(2));
        let results = if convention == CallingConv::C {
            caller.call_indirect_results::<2>(address, signature, vec![s, o])
        } else {
            caller.call_indirect_results_cc::<2>(address, signature, vec![s, o], convention)
        };
        assert_eq!(results, [ValueId::new(3), ValueId::new(4)]);
        caller.ret(results.to_vec());
        caller.build();

        let module = module.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(validate_module(&module), vec![]);
        let call = &module.functions[1].blocks[0].body[1];
        assert_eq!(call.results, results);
        assert!(
            matches!(call.inst, Inst::CallIndirect { calling_conv, .. } if calling_conv == convention)
        );
    }
}

fn zero_and_one_result_module(array_api: bool) -> Module {
    let mut module = ModuleBuilder::new("compatible_calls");
    let void_sig = module.add_func_type(vec![Ty::I32], vec![]);
    let value_sig = module.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let caller_sig = module.add_func_type(vec![], vec![Ty::I32]);
    let mut void = module.function("void", void_sig);
    let entry = void.create_block();
    void.add_block_param(entry, Ty::I32);
    void.switch_to_block(entry);
    void.ret(vec![]);
    let void = void.build();
    let mut identity = module.function("identity", value_sig);
    let entry = identity.create_block();
    let input = identity.add_block_param(entry, Ty::I32);
    identity.switch_to_block(entry);
    identity.ret(vec![input]);
    let identity = identity.build();

    let mut caller = module.function("caller", caller_sig);
    let entry = caller.create_block();
    caller.switch_to_block(entry);
    let input = caller.iconst(Ty::I32, 7);
    if array_api {
        let [] = caller.call_results::<0>(void, vec![input]);
    } else {
        caller.call_void(void, vec![input]);
    }
    let direct = if array_api {
        caller.call_results::<1>(identity, vec![input])[0]
    } else {
        caller.call(identity, vec![input])
    };
    assert_eq!(direct, ValueId::new(1));
    let void_address = caller.fn_addr(void_sig, void);
    let value_address = caller.fn_addr(value_sig, identity);
    if array_api {
        let [] = caller.call_indirect_results::<0>(void_address, void_sig, vec![direct]);
    } else {
        caller.call_indirect_void(void_address, void_sig, vec![direct]);
    }
    let indirect = if array_api {
        caller.call_indirect_results::<1>(value_address, value_sig, vec![direct])[0]
    } else {
        caller.call_indirect(value_address, value_sig, vec![direct])
    };
    assert_eq!(indirect, ValueId::new(4));
    let explicit_cc = if array_api {
        caller.call_indirect_results_cc::<1>(
            value_address,
            value_sig,
            vec![indirect],
            CallingConv::C,
        )[0]
    } else {
        caller.call_indirect_cc(value_address, value_sig, vec![indirect], CallingConv::C)
    };
    assert_eq!(explicit_cc, ValueId::new(5));
    caller.ret(vec![explicit_cc]);
    caller.build();
    module.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn zero_and_one_result_calls_match_existing_api_exactly() {
    let legacy = zero_and_one_result_module(false);
    let arrays = zero_and_one_result_module(true);
    assert_eq!(validate_module(&legacy), vec![]);
    assert_eq!(validate_module(&arrays), vec![]);
    assert_eq!(arrays, legacy);
}

fn calls_with_wrong_result_arity<const N: usize>() -> Module {
    let mut module = ModuleBuilder::new("unchecked_call_arities");
    let pair_sig = module.add_func_type(vec![], vec![Ty::I32, Ty::Bool]);
    let void_sig = module.add_func_type(vec![], vec![]);
    let mut callee = module.function("pair", pair_sig);
    let entry = callee.create_block();
    callee.switch_to_block(entry);
    let integer = callee.iconst(Ty::I32, 3);
    let boolean = callee.const_value(Ty::Bool, trust_ir::Constant::Bool(true));
    callee.ret(vec![integer, boolean]);
    let callee = callee.build();
    let mut caller = module.function("caller", void_sig);
    let entry = caller.create_block();
    caller.switch_to_block(entry);
    caller.call_results::<N>(callee, vec![]);
    let address = caller.fn_addr(pair_sig, callee);
    caller.call_indirect_results::<N>(address, pair_sig, vec![]);
    caller.call_indirect_results_cc::<N>(address, pair_sig, vec![], CallingConv::C);
    caller.ret(vec![]);
    caller.build();
    module.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn unchecked_result_arities_are_rejected_by_module_validation() {
    for (actual, module) in [
        (0, calls_with_wrong_result_arity::<0>()),
        (1, calls_with_wrong_result_arity::<1>()),
        (3, calls_with_wrong_result_arity::<3>()),
    ] {
        let errors = validate_module(&module);
        assert_eq!(errors.len(), 3, "{errors:?}");
        for (error, op) in errors
            .iter()
            .zip(["call", "call_indirect", "call_indirect"])
        {
            assert_eq!(
                error,
                &ValidationError::InstrResultArityMismatch {
                    block: 0,
                    op: op.into(),
                    expected: 2,
                    actual,
                },
            );
        }
    }
}

#[test]
fn call_targets_arguments_and_indirect_signatures_remain_checked() {
    let mut module = calls_with_wrong_result_arity::<2>();
    assert_eq!(validate_module(&module), vec![]);
    let Inst::Call { callee, .. } = &mut module.functions[1].blocks[0].body[0].inst else {
        panic!("direct call");
    };
    *callee = FuncId::new(99);
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::CalleeNotFound { callee_id: 99, .. }))
    );

    let mut module = calls_with_wrong_result_arity::<2>();
    let wrong_sig = module
        .add_func_type(trust_ir::FuncTy {
            params: vec![],
            returns: vec![Ty::Bool, Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let Inst::CallIndirect { sig, .. } = &mut module.functions[1].blocks[0].body[2].inst else {
        panic!("indirect call");
    };
    *sig = wrong_sig;
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::CallEdgeSignatureMismatch { .. }))
    );

    let mut module = calls_with_wrong_result_arity::<2>();
    let Inst::CallIndirect { calling_conv, .. } = &mut module.functions[1].blocks[0].body[3].inst
    else {
        panic!("explicit-CC indirect call");
    };
    *calling_conv = CallingConv::Fast;
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::CallEdgeConvMismatch { .. }))
    );

    let mut module = zero_and_one_result_module(true);
    let Inst::Call { args, .. } = &mut module.functions[2].blocks[0].body[1].inst else {
        panic!("void call");
    };
    args.clear();
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::CallArgCountMismatch { .. }))
    );
}
