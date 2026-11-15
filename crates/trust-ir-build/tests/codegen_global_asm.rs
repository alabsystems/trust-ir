// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `Module::global_asm`'s normative rule, as enforcement rather than prose.
//
// The v41 field carries module-level `global_asm!` blocks as OPAQUE TEXT, and
// the rule stated when it landed is that a consumer must REFUSE such a module
// rather than silently DROP the block. Before this test there was no
// enforcement point anywhere in `trust-ir-build`: the field round-tripped, was
// identity-bearing, and was otherwise unexamined, while downstream
// `trust-cg`'s `module_merge` COUNTS the blocks and refuses nothing.
//
// Both halves are pinned here, because the rule is a composition and not a
// widening: `validate_module` (structural) must keep ACCEPTING a module that
// carries assembly — such a module is well-formed, and that is what an
// artifact under inspection looks like — while
// `validate_module_for_codegen` (codegen intent) must refuse it. Exactly the
// `body_gate` split.

use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId};
use trust_ir::{Block, BodyGate, Function, Module};
use trust_ir_build::validate::{
    ValidationError, codegen_global_asm_errors, validate_module_for_codegen,
};
use trust_ir_build::validate_module;

/// One licensed, well-formed nullary function, so nothing but the assembly
/// rule can speak in `validate_module_for_codegen`.
fn licensed_module() -> Module {
    let mut module = Module::new("asm");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(block);
    // An authority OUTSIDE `EVIDENCE_BOUND_GATE_AUTHORITIES`: since WS1.5 a
    // `clean-kernel-tv` license must be backed by a kernel-rechecked TV
    // certificate, which this assembly-only fixture has no reason to carry.
    func.body_gate = Some(BodyGate::Gated {
        authority: "trust-direct-lane-structural".to_string(),
        evidence: None,
    });
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn a_module_carrying_global_asm_is_structurally_well_formed() {
    // The composition boundary. If this ever starts failing, the refusal has
    // leaked into the structural pass and every round-trip fixture, diff and
    // inspector that reads a module with assembly in it breaks.
    let mut module = licensed_module();
    module
        .global_asm
        .push(".globl trust_probe\ntrust_probe:\n  ret\n".to_string());
    assert_eq!(validate_module(&module), Vec::new());
}

#[test]
fn codegen_refuses_global_asm_and_names_the_block_count() {
    let mut module = licensed_module();
    module.global_asm.push(".byte 0x90".to_string());
    module.global_asm.push(".byte 0xcc".to_string());
    let errors = validate_module_for_codegen(&module);
    assert_eq!(
        errors,
        vec![ValidationError::GlobalAsmNotConsumable { blocks: 2 }],
        "codegen intent must refuse module-level assembly, naming how many blocks"
    );
    // The rendered diagnostic has to say WHY dropping is the hazard, since
    // that is the whole content of the normative rule.
    let rendered = errors[0].to_string();
    assert!(rendered.contains('2'), "{rendered}");
    assert!(rendered.contains("global_asm!"), "{rendered}");
    assert!(rendered.contains("drop"), "{rendered}");
}

#[test]
fn one_block_renders_in_the_singular() {
    let mut module = licensed_module();
    module.global_asm.push(".byte 0x90".to_string());
    let errors = codegen_global_asm_errors(&module);
    assert_eq!(
        errors,
        vec![ValidationError::GlobalAsmNotConsumable { blocks: 1 }]
    );
    assert!(
        errors[0]
            .to_string()
            .contains("1 module-level global_asm! block:")
    );
}

#[test]
fn no_global_asm_is_no_error() {
    let module = licensed_module();
    assert_eq!(codegen_global_asm_errors(&module), Vec::new());
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
}

#[test]
fn the_layer_is_separately_matchable_from_the_license_refusals() {
    // A consumer that has decided to accept assembly out-of-band (it links the
    // text itself) must be able to drop exactly this variant without losing
    // the license refusals, and vice versa. Both are in one vector, so the
    // only thing that makes that expressible is that they never share a
    // variant.
    let mut module = licensed_module();
    module.functions[0].body_gate = Some(BodyGate::Ungated);
    module.global_asm.push(".byte 0x90".to_string());
    let errors = validate_module_for_codegen(&module);
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::UngatedBodyForCodegen { .. }))
    );
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::GlobalAsmNotConsumable { blocks: 1 }))
    );
}
