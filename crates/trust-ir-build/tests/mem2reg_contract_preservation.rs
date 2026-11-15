// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::mem2reg::{promote_allocas_function, promote_allocas_module};
use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort, ProofFormula};
use trust_ir::{BodyGate, CastOp, FunctionSummary, Inst, Module, Ty, ValueId};
use trust_ir_build::{ModuleBuilder, validate_module};

fn fixture() -> (Module, ValueId, ValueId) {
    let mut builder = ModuleBuilder::new("summary-memory-authority");
    let signature = builder.add_func_type(vec![], vec![Ty::I64]);
    let mut function = builder.function("snapshot", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let slot = function.alloca(Ty::I64);
    let value = function.iconst(Ty::I64, 7);
    function.store(Ty::I64, slot, value);
    let loaded = function.load(Ty::I64, slot);
    // This address has no instruction users, but the summary below can own it.
    let address = function.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, slot);
    function.ret(vec![loaded]);
    function.build();
    (
        builder.build().expect("ModuleBuilder::build: test fixture"),
        loaded,
        address,
    )
}

fn binding(value: ValueId) -> ProofFormula {
    let mut clause = ProofFormula::smtlib2("(= named named)", "Bool");
    clause.bindings.push((
        "named".into(),
        ClauseBinding {
            sort: ClauseSort::BitVec(64),
            place: ClausePlace::Value(value),
        },
    ));
    clause
}

fn assert_preserved(mut module: Module) {
    assert!(validate_module(&module).is_empty());
    assert!(module.proof_obligations.is_empty());
    assert!(module.functions[0].proofs.is_empty());
    assert!(module.functions[0].blocks.iter().all(|block| {
        block
            .body
            .iter()
            .all(|node| node.proofs.is_empty() && node.proof_context.is_none())
    }));
    let before = module.clone();
    let digest = module.stable_digest();
    assert_eq!(promote_allocas_function(&mut module.functions[0]), 0);
    assert_eq!(module, before);
    promote_allocas_module(&mut module);
    assert_eq!(module, before);
    assert_eq!(module.stable_digest(), digest);
    assert!(validate_module(&module).is_empty());

    // Contract resolution really depends on the retained definition: removing
    // it independently must fail, rather than a vacuous metadata-only positive.
    let summary = module.functions[0].summary.as_ref().unwrap();
    let clause = summary
        .requires
        .iter()
        .chain(&summary.ensures)
        .chain(&summary.decreases)
        .next()
        .unwrap();
    let ClausePlace::Value(bound) = clause.bindings[0].1.place else {
        panic!("fixture must bind an actual SSA value")
    };
    module.functions[0].blocks[0]
        .body
        .retain(|node| !node.results.contains(&bound));
    assert!(validate_module(&module).iter().any(|error| matches!(
        error,
        trust_ir_build::validate::ValidationError::InvalidFunctionSummary { detail, .. }
            if detail.contains("names SSA value") && detail.contains("never defines")
    )));
}

#[test]
fn scalar_load_bound_only_by_each_summary_role_is_preserved() {
    for role in 0..3 {
        let (mut module, loaded, address) = fixture();
        // Remove the unrelated address-taking instruction so the old scalar
        // pass would otherwise promote this alloca and delete `loaded`.
        module.functions[0].blocks[0]
            .body
            .retain(|node| !node.results.contains(&address));
        let mut summary = FunctionSummary::new();
        match role {
            0 => summary.requires.push(binding(loaded)),
            1 => summary.ensures.push(binding(loaded)),
            _ => summary.decreases.push(binding(loaded)),
        }
        module.functions[0].summary = Some(summary);
        assert_preserved(module);
    }
}

#[test]
fn zero_instruction_use_address_bound_by_summary_is_preserved() {
    let (mut module, _, address) = fixture();
    let mut summary = FunctionSummary::new();
    summary.ensures.push(binding(address));
    module.functions[0].summary = Some(summary);
    assert_preserved(module);
}

#[test]
fn empty_summary_and_codegen_license_are_not_cleared_by_promotion() {
    let (mut module, _, address) = fixture();
    module.functions[0].blocks[0]
        .body
        .retain(|node| !node.results.contains(&address));
    module.functions[0].summary = Some(FunctionSummary::new());
    module.functions[0].body_gate = Some(BodyGate::Ungated);
    let before = module.clone();
    assert_eq!(promote_allocas_function(&mut module.functions[0]), 0);
    promote_allocas_module(&mut module);
    assert_eq!(module, before);

    // A genuinely contract-free function retains the existing scalar path;
    // the codegen license is still preserved and cannot be laundered to None.
    module.functions[0].summary = None;
    assert_eq!(promote_allocas_function(&mut module.functions[0]), 1);
    assert_eq!(module.functions[0].body_gate, Some(BodyGate::Ungated));
    assert!(
        module.functions[0].blocks[0]
            .body
            .iter()
            .all(|node| !matches!(
                node.inst,
                Inst::Alloca { .. } | Inst::Load { .. } | Inst::Store { .. }
            ))
    );
}
