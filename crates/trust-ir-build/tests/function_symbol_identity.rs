// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// The def identity a module-level uniqueness rule may key on
// (docs/SPEC_RATIFICATIONS.md section 1.1).
//
// This file exists because the enforcement-link gate found the section had
// none: its Enforcement entry said the treatment was "pinned", and no `#[test]`
// in any workspace crate named `DuplicateFunctionSymbol` or
// `InvalidDisplayPath`. The rule was code that nothing executed. These tests
// are EVIDENCE that it fires as ratified, not a proof of it.
//
// What section 1.1 ratifies, clause by clause:
//   * the link-time symbol `Function.name` is the ONLY def identity, so two
//     rows sharing one are refused, definitions and declarations alike;
//   * a duplicate `display_path` is EXPLICITLY DECLINED as a rule: two
//     monomorphic instances legitimately share a def-path;
//   * `display_path` is validated for usability only (blank, or a newline).

use trust_ir::Module;
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

/// A body-less external declaration is an ABI boundary, so the validator
/// demands a target before it will call the module clean.
fn pinned_target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("sysv64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

/// One definition (`defined`) and two body-less declarations (`first`,
/// `second`), all of one nullary signature, in that table order.
fn three_rows() -> Module {
    let mut module =
        ModuleBuilder::new_with_target_info("function_symbol_identity", pinned_target());
    let signature = module.add_func_type(vec![], vec![]);
    let defined = module.declare_function("defined", signature);
    module.declare_function("first", signature);
    module.declare_function("second", signature);
    let mut body = module.define_function(defined).unwrap();
    let entry = body.create_block();
    body.switch_to_block(entry);
    body.ret(vec![]);
    body.build();
    module.build().expect("ModuleBuilder::build: test fixture")
}

fn duplicate_symbols(module: &Module) -> Vec<ValidationError> {
    validate_module(module)
        .into_iter()
        .filter(|error| matches!(error, ValidationError::DuplicateFunctionSymbol { .. }))
        .collect()
}

fn display_path_errors(module: &Module) -> Vec<ValidationError> {
    validate_module(module)
        .into_iter()
        .filter(|error| matches!(error, ValidationError::InvalidDisplayPath { .. }))
        .collect()
}

#[test]
fn distinct_symbols_validate_clean() {
    // The baseline every refusal below is attributed against.
    assert_eq!(validate_module(&three_rows()), []);
}

#[test]
fn two_declarations_sharing_a_link_symbol_are_refused_once_in_id_order() {
    let mut module = three_rows();
    module.functions[2].name = "first".into();
    let (first, second) = (
        module.functions[1].id.index(),
        module.functions[2].id.index(),
    );
    assert_eq!(
        duplicate_symbols(&module),
        [ValidationError::DuplicateFunctionSymbol {
            name: "first".into(),
            first,
            second,
            first_producer: None,
            second_producer: None,
            first_display_path: None,
            second_display_path: None,
        }]
    );
}

#[test]
fn the_rule_fires_on_a_definition_and_a_declaration_alike() {
    // A declaration that takes a DEFINITION's symbol: the three consumers that
    // key on the name would conflate them at link time.
    let mut module = three_rows();
    module.functions[1].name = "defined".into();
    let (first, second) = (
        module.functions[0].id.index(),
        module.functions[1].id.index(),
    );
    assert_eq!(
        duplicate_symbols(&module),
        [ValidationError::DuplicateFunctionSymbol {
            name: "defined".into(),
            first,
            second,
            first_producer: None,
            second_producer: None,
            first_display_path: None,
            second_display_path: None,
        }]
    );
}

#[test]
fn a_symbol_held_three_times_is_reported_against_its_first_holder_each_time() {
    let mut module = three_rows();
    module.functions[1].name = "defined".into();
    module.functions[2].name = "defined".into();
    let ids: Vec<u32> = module.functions.iter().map(|f| f.id.index()).collect();
    assert_eq!(
        duplicate_symbols(&module),
        [
            ValidationError::DuplicateFunctionSymbol {
                name: "defined".into(),
                first: ids[0],
                second: ids[1],
                first_producer: None,
                second_producer: None,
                first_display_path: None,
                second_display_path: None,
            },
            ValidationError::DuplicateFunctionSymbol {
                name: "defined".into(),
                first: ids[0],
                second: ids[2],
                first_producer: None,
                second_producer: None,
                first_display_path: None,
                second_display_path: None,
            },
        ]
    );
}

#[test]
fn two_rows_may_share_a_display_path() {
    // The DECLINED rule. `Vec<i32>::push` and `Vec<u8>::push` share a def-path
    // and are two rows with two symbols; refusing that would refuse correct
    // output, so a shared `display_path` must validate clean.
    let mut module = three_rows();
    for function in &mut module.functions {
        function.display_path = Some("alloc::vec::Vec::push".into());
    }
    assert_eq!(validate_module(&module), []);
}

#[test]
fn a_blank_display_path_is_refused_for_usability() {
    let mut module = three_rows();
    module.functions[1].display_path = Some("   ".into());
    let function = module.functions[1].id.index();
    let errors = display_path_errors(&module);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        matches!(&errors[0], ValidationError::InvalidDisplayPath { function: f, detail }
            if *f == function && detail.contains("blank")),
        "{errors:?}"
    );
}

#[test]
fn a_display_path_carrying_a_newline_is_refused_for_usability() {
    let mut module = three_rows();
    module.functions[2].display_path = Some("core::ops\nAdd::add".into());
    let function = module.functions[2].id.index();
    let errors = display_path_errors(&module);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        matches!(&errors[0], ValidationError::InvalidDisplayPath { function: f, detail }
            if *f == function && detail.contains("newline")),
        "{errors:?}"
    );
}

#[test]
fn an_unrecorded_display_path_is_not_an_error() {
    let module = three_rows();
    assert!(module.functions.iter().all(|f| f.display_path.is_none()));
    assert_eq!(display_path_errors(&module), []);
}
