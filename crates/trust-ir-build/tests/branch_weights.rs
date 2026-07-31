// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ProofAnnotation::BranchWeights is a codegen hint; the validator checks it
// sits on a CondBr/Switch node with the right out-edge arity. (Round-trip is
// covered by the trust-ir-conformance proof_annotations corpus.)

use trust_ir::inst::{Inst, SwitchCase};
use trust_ir::{Constant, Module, ProofAnnotation, Ty};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

/// Build `fn f(bool) { entry: condbr %0 -> a / b; a: ret; b: ret }` and return
/// the module plus the entry block's terminator node index for annotation.
fn module_with_condbr() -> Module {
    let mut mb = ModuleBuilder::new("bw");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    {
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let a = fb.create_block();
        let b = fb.create_block();
        let c = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        fb.condbr(c, a, vec![], b, vec![]);
        fb.switch_to_block(a);
        fb.ret(vec![]);
        fb.switch_to_block(b);
        fb.ret(vec![]);
        fb.build();
    }
    mb.build()
}

/// Attach a proof annotation to the entry block's terminator (the CondBr).
fn annotate_terminator(m: &mut Module, p: ProofAnnotation) {
    let body = &mut m.functions[0].blocks[0].body;
    let last = body.len() - 1;
    body[last].proofs.push(p);
}

fn has_mismatch(m: &Module) -> bool {
    validate_module(m)
        .iter()
        .any(|e| matches!(e, ValidationError::BranchWeightsMismatch { .. }))
}

#[test]
fn condbr_with_two_weights_ok() {
    let mut m = module_with_condbr();
    annotate_terminator(&mut m, ProofAnnotation::BranchWeights(vec![7, 1]));
    assert!(!has_mismatch(&m), "errors: {:?}", validate_module(&m));
}

#[test]
fn condbr_with_wrong_arity_rejected() {
    let mut m = module_with_condbr();
    annotate_terminator(&mut m, ProofAnnotation::BranchWeights(vec![1, 2, 3]));
    assert!(has_mismatch(&m));
}

#[test]
fn branch_weights_on_non_terminator_rejected() {
    // Attach to a non-CondBr/Switch node: build a function whose entry has a
    // const then ret, and annotate the const.
    let mut mb = ModuleBuilder::new("bw2");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    {
        let mut fb = mb.function("g", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let _v = fb.iconst(Ty::I32, 0);
        let r = fb.iconst(Ty::I32, 1);
        fb.ret(vec![r]);
        fb.build();
    }
    let mut m = mb.build();
    // annotate the first const node (not a terminator)
    m.functions[0].blocks[0].body[0]
        .proofs
        .push(ProofAnnotation::BranchWeights(vec![1, 1]));
    assert!(has_mismatch(&m));
    // sanity: the node really isn't a terminator
    assert!(!matches!(
        m.functions[0].blocks[0].body[0].inst,
        Inst::CondBr { .. } | Inst::Switch { .. }
    ));
}

/// Build `fn f(i32) { entry: switch %0 [0 -> a] default b; a: ret; b: ret }`
/// (1 case → 2 out-edges) and annotate the Switch terminator with `weights`.
fn module_with_switch(weights: Vec<u32>) -> Module {
    let mut mb = ModuleBuilder::new("sw");
    let ft = mb.add_func_type(vec![Ty::I32], vec![]);
    {
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let a = fb.create_block();
        let b = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.switch(
            x,
            vec![SwitchCase {
                value: Constant::Int(0),
                target: a,
                args: vec![],
            }],
            b,
            vec![],
        );
        fb.switch_to_block(a);
        fb.ret(vec![]);
        fb.switch_to_block(b);
        fb.ret(vec![]);
        fb.build();
    }
    let mut m = mb.build();
    annotate_terminator(&mut m, ProofAnnotation::BranchWeights(weights));
    m
}

#[test]
fn switch_with_cases_plus_one_weights_ok() {
    // 1 case + default ⇒ exactly 2 weights are correct.
    let m = module_with_switch(vec![3, 5]);
    assert!(!has_mismatch(&m), "errors: {:?}", validate_module(&m));
}

#[test]
fn switch_with_wrong_arity_rejected() {
    // 1 case + default needs 2 weights; 3 is an off-by-one and must be rejected.
    let m = module_with_switch(vec![1, 1, 1]);
    assert!(has_mismatch(&m));
}

#[test]
fn branch_weights_at_function_scope_rejected() {
    // BranchWeights belongs on a CondBr/Switch terminator node, never on
    // Function.proofs. A function-scope placement must be rejected.
    let mut m = module_with_condbr();
    m.functions[0]
        .proofs
        .push(ProofAnnotation::BranchWeights(vec![7, 1]));
    assert!(has_mismatch(&m));
}
