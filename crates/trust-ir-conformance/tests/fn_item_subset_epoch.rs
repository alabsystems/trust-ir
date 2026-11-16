// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A historical receipt never acquires the new nominal constructor merely
//! because the implementation can now execute it. Full module typing remains
//! separate from this structural conformance contract.
use trust_ir::bridge::{ConformanceSubset, SubsetSite};
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Pred, Ty, ValueId,
};
use trust_ir_conformance::subset::{SUBSET_VERSION, module_subset_violations_at_version};

fn module() -> Module {
    let mut module = Module::new("subset-epoch");
    let signature = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![], false))
        .unwrap();
    let mut target = Function::new(FuncId::new(7), "item", signature, BlockId::new(0));
    let mut block = Block::new(target.entry);
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    target.blocks.push(block);
    module.functions.push(target);
    module
}

fn verdict(module: &Module, version: u32) -> (bool, Vec<String>) {
    let core = ConformanceSubset { version }.check(module);
    let mirrored = module_subset_violations_at_version(module, version);
    assert_eq!(
        core.is_ok(),
        mirrored.is_empty(),
        "core/mirror differ at v{version}: {core:?}/{mirrored:?}"
    );
    (core.is_ok(), mirrored)
}

#[test]
fn fn_item_subset_epoch_keeps_old_receipts_and_future_versions_separate() {
    assert_eq!(SUBSET_VERSION, 6);
    let old = module();
    for version in 1..=6 {
        assert!(verdict(&old, version).0);
    }
    let mut item = old.clone();
    item.types.push(Ty::FnItem(FuncId::new(7)));
    item.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Const {
            ty: Ty::FnItem(FuncId::new(7)),
            value: Constant::FnItem(FuncId::new(7)),
        })
        .with_result(ValueId::new(0)),
    );
    assert!(trust_ir_build::validate_module(&item).is_empty());
    for version in 1..=5 {
        let (accepted, errors) = verdict(&item, version);
        assert!(!accepted);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("requires lowering-target subset v6"))
        );
    }
    assert!(verdict(&item, 6).0);
    for version in [7, u32::MAX] {
        for module in [&old, &item] {
            assert!(!verdict(module, version).0);
            assert!(
                ConformanceSubset { version }
                    .check(module)
                    .unwrap_err()
                    .iter()
                    .any(|error| error.site == SubsetSite::ModuleEpoch)
            );
        }
    }
}

#[test]
fn fn_item_subset_epoch_checks_unused_headers_and_constant_only_occurrences() {
    let mut source = module();
    // This deliberately invalid predicate is not a value/admission fixture.
    // It isolates discovery of a new constant without a new type spelling.
    source
        .predicates
        .push(Pred::FiniteSet(vec![Constant::Aggregate(vec![
            Constant::FnItem(FuncId::new(7)),
        ])]));
    assert!(
        verdict(&source, 5)
            .1
            .iter()
            .any(|error| error.contains("requires lowering-target subset v6"))
    );
    source.predicates.clear();
    source.types.push(Ty::FnItem(FuncId::new(7)));
    assert!(verdict(&source, 6).0);
    source.functions.push(source.functions[0].clone());
    assert!(
        !verdict(&source, 6).0,
        "duplicate actual header cannot authenticate an unused item type"
    );
    source.functions.pop();
    source.functions[0].ty = trust_ir::FuncTyId::new(99);
    assert!(
        !verdict(&source, 6).0,
        "a declaration without its actual signature is not an item context"
    );
    source.functions.clear();
    assert!(!verdict(&source, 6).0);
}
