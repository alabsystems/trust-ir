// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::{CallingConv, Constant, DialectTy, FuncId, Inst, Module, ProofAnnotation, Ty};
use trust_ir_build::{FunctionDefinitionError, ModuleBuilder, validate_module};

fn nominal(name: &str) -> Ty {
    Ty::Dialect(Box::new(DialectTy::new("example", name, 1)))
}

fn pinned_target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("sysv64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

#[test]
fn reserved_functions_support_reverse_definitions_sparse_ids_and_mutual_callbacks() {
    let mut module = ModuleBuilder::new("reserved_recursive_functions");
    let state = nominal("state");
    let outcome = nominal("outcome");
    let signature = module.add_func_type(
        vec![state.clone(), outcome.clone()],
        vec![state.clone(), outcome.clone()],
    );
    // A real public-API source of sparse function identities: legacy drafts
    // reserve IDs even when abandoned, but append no table slot.
    drop(module.function("abandoned", signature));
    let first = module.declare_function("first", signature);
    drop(module.function("another_abandoned", signature));
    let second = module.declare_function("second", signature);
    assert_eq!((first, second), (FuncId::new(1), FuncId::new(3)));
    let next = module
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");

    for (function, callee) in [(second, first), (first, second)] {
        let mut body = module.define_function(function).unwrap();
        let entry = body.create_block();
        let s = body.add_block_param(entry, state.clone());
        let o = body.add_block_param(entry, outcome.clone());
        body.switch_to_block(entry);
        let results = body.call_results::<2>(callee, vec![s, o]);
        let callback = body.fn_addr(signature, callee);
        let results = body.call_indirect_results::<2>(callback, signature, results.to_vec());
        body.ret(results.to_vec());
        assert_eq!(body.build(), function);
        assert_eq!(
            module
                .peek_next_func_id()
                .expect("peek_next_func_id: test fixture"),
            next
        );
    }
    let module = module.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(
        module.functions.iter().map(|f| f.id).collect::<Vec<_>>(),
        [first, second]
    );
    assert_eq!(validate_module(&module), []);
    for (function, callee) in module.functions.iter().zip([second, first]) {
        assert!(
            matches!(function.blocks[0].body[0].inst, Inst::Call { callee: target, .. } if target == callee)
        );
        assert!(
            matches!(function.blocks[0].body[1].inst, Inst::Const { ty: Ty::Func(sig), value: Constant::FnDef(target) } if sig == signature && target == callee)
        );
    }
}

#[test]
fn abandoned_definition_is_retryable_and_does_not_publish_draft_claims() {
    let mut module = ModuleBuilder::new("abandoned_definition");
    let signature = module.add_func_type(vec![], vec![]);
    let function = module.declare_function("reserved", signature);
    let next = module
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    {
        let mut body = module.define_function(function).unwrap();
        body.set_calling_conv(CallingConv::Fast);
        body.set_attrs(trust_ir::FuncAttrs {
            readnone: true,
            ..Default::default()
        });
        body.add_function_proof(ProofAnnotation::Pure);
        let entry = body.create_block();
        body.switch_to_block(entry);
        body.ret(vec![]);
        // Deliberately no build().
    }
    assert_eq!(
        module
            .peek_next_func_id()
            .expect("peek_next_func_id: test fixture"),
        next
    );
    let mut body = module.define_function(function).unwrap();
    let entry = body.create_block();
    body.switch_to_block(entry);
    body.ret(vec![]);
    assert_eq!(body.build(), function);
    assert!(
        matches!(module.define_function(function), Err(FunctionDefinitionError::AlreadyDefined(id)) if id == function)
    );
    let module = module.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(module.functions.len(), 1);
    assert_eq!(module.functions[0].calling_conv, CallingConv::C);
    assert!(module.functions[0].attrs.is_empty());
    assert!(module.functions[0].proofs.is_empty());
    assert!(module.proof_obligations.is_empty());
    assert!(module.proof_certificates.is_empty());
    assert_eq!(validate_module(&module), []);
}

#[test]
fn unknown_legacy_and_completed_declarations_cannot_be_redefined() {
    let mut module = ModuleBuilder::new_with_target_info("definition_rejections", pinned_target());
    let signature = module.add_func_type(vec![], vec![]);
    let legacy = module.function("external_legacy", signature).build();
    let reserved = module.declare_function("external_reserved", signature);
    let next = module
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    for unknown in [legacy, FuncId::new(u32::MAX)] {
        assert!(
            matches!(module.define_function(unknown), Err(FunctionDefinitionError::NotDeclared(id)) if id == unknown)
        );
        assert_eq!(
            module
                .peek_next_func_id()
                .expect("peek_next_func_id: test fixture"),
            next
        );
    }
    // A committed empty draft is still consumed, unlike an abandoned draft.
    assert_eq!(module.define_function(reserved).unwrap().build(), reserved);
    assert!(
        matches!(module.define_function(reserved), Err(FunctionDefinitionError::AlreadyDefined(id)) if id == reserved)
    );
    let module = module.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(module.functions.len(), 2);
    assert!(module.functions.iter().all(|f| f.blocks.is_empty()));
    assert_eq!(validate_module(&module), []);
}

fn compatible_module(two_phase: bool) -> Module {
    let mut module = ModuleBuilder::new("compatible_definitions");
    module.set_default_producer(trust_ir::Producer::Clean);
    let signature = module.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let first = if two_phase {
        Some(module.declare_function("identity", signature))
    } else {
        None
    };
    let second = if two_phase {
        Some(module.declare_function("caller", signature))
    } else {
        None
    };
    let mut identity = match first {
        Some(id) => module.define_function(id).unwrap(),
        None => module.function("identity", signature),
    };
    let entry = identity.create_block();
    let value = identity.add_block_param(entry, Ty::I64);
    identity.switch_to_block(entry);
    identity.ret(vec![value]);
    identity.add_function_proof(ProofAnnotation::NoPanic);
    let identity = identity.build();

    let mut caller = match second {
        Some(id) => module.define_function(id).unwrap(),
        None => module.function("caller", signature),
    };
    let entry = caller.create_block();
    let value = caller.add_block_param(entry, Ty::I64);
    caller.switch_to_block(entry);
    let value = caller.call(identity, vec![value]);
    caller.ret(vec![value]);
    caller.build();
    module.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn ordinary_function_bytes_and_pending_obligation_synthesis_are_unchanged() {
    let legacy = compatible_module(false);
    let reserved = compatible_module(true);
    assert_eq!(reserved, legacy);
    assert_eq!(reserved.stable_digest(), legacy.stable_digest());
    #[cfg(feature = "binary")]
    assert_eq!(
        trust_ir::binary::serialize_module(&reserved).expect("serialize_module: test fixture"),
        trust_ir::binary::serialize_module(&legacy).expect("serialize_module: test fixture")
    );
    assert_eq!(reserved.proof_obligations.len(), 1);
    assert_eq!(
        reserved.proof_obligations[0].status,
        trust_ir::ProofStatus::Pending
    );
    assert!(reserved.proof_certificates.is_empty());
    assert_eq!(validate_module(&reserved), validate_module(&legacy));
}

#[test]
fn abandoned_draft_leaves_the_original_bodyless_declaration_byte_identical() {
    fn build(abandon: bool) -> Module {
        let mut module =
            ModuleBuilder::new_with_target_info("unchanged_declaration", pinned_target());
        let signature = module.add_func_type(vec![], vec![]);
        let function = module.declare_function("external", signature);
        if abandon {
            let mut body = module.define_function(function).unwrap();
            body.add_function_proof(ProofAnnotation::NoPanic);
            let entry = body.create_block();
            body.switch_to_block(entry);
            body.unreachable();
        }
        module.build().expect("ModuleBuilder::build: test fixture")
    }
    let original = build(false);
    let abandoned = build(true);
    assert_eq!(original, abandoned);
    assert_eq!(original.stable_digest(), abandoned.stable_digest());
    assert_eq!(validate_module(&abandoned), []);
}
