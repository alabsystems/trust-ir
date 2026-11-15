// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Public, narrow Switch source checking shares the validator's literal rules.

use trust_ir::inst::{Inst, SwitchCase};
use trust_ir::{Constant, FuncId, Global, Linkage, Module, Pred, Ty};
use trust_ir_build::{
    ModuleBuilder, ValidationError, codegen_switch_case_literal_errors, validate_module,
};

fn add_switch(mb: &mut ModuleBuilder, name: &str, ty: Ty, values: Vec<Constant>) {
    let signature = mb.add_func_type(vec![ty.clone()], vec![]);
    let mut fb = mb.function(name, signature);
    let entry = fb.create_block();
    let selector = fb.add_block_param(entry, ty);
    let hit = fb.create_block();
    let miss = fb.create_block();
    fb.switch_to_block(entry);
    fb.switch(
        selector,
        values
            .into_iter()
            .map(|value| SwitchCase {
                value,
                target: hit,
                args: vec![],
            })
            .collect(),
        miss,
        vec![],
    );
    for block in [hit, miss] {
        fb.switch_to_block(block);
        fb.ret(vec![]);
    }
    fb.build();
}

fn switches(cells: &[(Ty, Constant)]) -> Module {
    let mut mb = ModuleBuilder::new("codegen_switch_literal_contract");
    for (index, (ty, value)) in cells.iter().enumerate() {
        add_switch(
            &mut mb,
            &format!("f{index}"),
            ty.clone(),
            vec![value.clone()],
        );
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn assert_exact_parity(module: &Module) -> Vec<ValidationError> {
    let bulk = codegen_switch_case_literal_errors(module);
    let full = validate_module(module);
    assert_eq!(bulk, full, "only actual switch literals are malformed");
    assert!(
        bulk.iter()
            .all(|error| matches!(error, ValidationError::ConstTypeMismatch { .. }))
    );
    bulk
}

#[test]
fn bulk_switch_source_contract_preserves_signed_unsigned_boundary_refusals() {
    let cells = [
        (Ty::U8, Constant::Int(-1)),
        (Ty::I8, Constant::Int(255)),
        (Ty::I8, Constant::Int(-129)),
        (Ty::U8, Constant::Int(256)),
        (Ty::I16, Constant::Int(1 << 15)),
        (Ty::I16, Constant::Int(-(1 << 15) - 1)),
        (Ty::U16, Constant::Int(-1)),
        (Ty::U16, Constant::Int(1 << 16)),
        (Ty::I32, Constant::Int(1 << 31)),
        (Ty::I32, Constant::Int(-(1 << 31) - 1)),
        (Ty::U32, Constant::Int(-1)),
        (Ty::U32, Constant::Int(1 << 32)),
        (Ty::I64, Constant::Int(1 << 63)),
        (Ty::I64, Constant::Int(-(1 << 63) - 1)),
        (Ty::U64, Constant::Int(-1)),
        (Ty::U64, Constant::Int(1 << 64)),
        (Ty::Isize, Constant::Int(1 << 63)),
        (Ty::Usize, Constant::Int(-1)),
        (Ty::I128, Constant::u128((i128::MAX as u128) + 1)),
        (Ty::U128, Constant::Int(-1)),
    ];
    let errors = assert_exact_parity(&switches(&cells));
    assert_eq!(errors.len(), cells.len());
    for (index, error) in errors.iter().enumerate() {
        let ValidationError::ConstTypeMismatch { location, .. } = error else {
            unreachable!()
        };
        assert_eq!(location, &format!("function 'f{index}' bb0 switch case 0"));
    }
}

#[test]
fn bulk_switch_source_contract_keeps_full_width_and_char_positive_boundaries() {
    let cells = [
        (Ty::I8, Constant::Int(i8::MIN.into())),
        (Ty::I8, Constant::Int(i8::MAX.into())),
        (Ty::U8, Constant::Int(0)),
        (Ty::U8, Constant::Int(u8::MAX.into())),
        (Ty::I16, Constant::Int(i16::MIN.into())),
        (Ty::I16, Constant::Int(i16::MAX.into())),
        (Ty::U16, Constant::Int(u16::MAX.into())),
        (Ty::I32, Constant::Int(i32::MIN.into())),
        (Ty::I32, Constant::Int(i32::MAX.into())),
        (Ty::U32, Constant::Int(u32::MAX.into())),
        (Ty::I64, Constant::Int(i64::MIN.into())),
        (Ty::I64, Constant::Int(i64::MAX.into())),
        (Ty::U64, Constant::Int(u64::MAX.into())),
        (Ty::I128, Constant::Int(i128::MIN)),
        (Ty::I128, Constant::Int(i128::MAX)),
        (Ty::U128, Constant::Int(i128::MAX)),
        (Ty::U128, Constant::u128(u128::MAX)),
        (Ty::Isize, Constant::Int(i64::MIN.into())),
        (Ty::Usize, Constant::Int(u64::MAX.into())),
        (Ty::Char, Constant::Int(0)),
        (Ty::Char, Constant::Int(0xD7FF)),
        (Ty::Char, Constant::Int(0xE000)),
        (Ty::Char, Constant::Int(0x10FFFF)),
    ];
    assert!(assert_exact_parity(&switches(&cells)).is_empty());
}

#[test]
fn bulk_switch_source_contract_preserves_canonical_u128_and_unicode_diagnostics() {
    let cells = [
        (Ty::U128, Constant::U128(5)),
        (Ty::U8, Constant::U128(5)),
        (Ty::Char, Constant::Int(-1)),
        (Ty::Char, Constant::Int(0xD800)),
        (Ty::Char, Constant::Int(0xDFFF)),
        (Ty::Char, Constant::Int(0x110000)),
        (Ty::I32, Constant::Bool(true)),
    ];
    let errors = assert_exact_parity(&switches(&cells));
    assert!(errors.iter().any(|error| matches!(error,
        ValidationError::ConstTypeMismatch { expected, .. }
            if expected.contains("canonical integer spelling"))));
    assert!(errors.iter().any(|error| matches!(error,
        ValidationError::ConstTypeMismatch { expected, actual, .. }
            if expected.contains("Unicode scalar value") && actual == "char constant 55296")));
}

#[test]
fn bulk_switch_source_contract_reads_refinement_representations_not_predicate_bounds() {
    let mut mb = ModuleBuilder::new("refined_switch_source");
    let pred = mb
        .intern_pred(Pred::Interval { lo: 3, hi: 7 })
        .expect("valid predicate");
    let unsigned = mb.refine_ty(Ty::U8, pred);
    let signed = mb.refine_ty(Ty::I8, pred);
    add_switch(
        &mut mb,
        "unsigned",
        unsigned,
        vec![
            Constant::Int(-1),
            Constant::Int(256),
            Constant::Int(0),
            Constant::Int(255),
        ],
    );
    add_switch(
        &mut mb,
        "signed",
        signed,
        vec![
            Constant::Int(-129),
            Constant::Int(128),
            Constant::Int(-128),
            Constant::Int(127),
        ],
    );
    let errors = assert_exact_parity(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert_eq!(errors.len(), 4);
    let locations: Vec<_> = errors
        .iter()
        .map(|error| match error {
            ValidationError::ConstTypeMismatch { location, .. } => location.as_str(),
            _ => unreachable!(),
        })
        .collect();
    assert_eq!(
        locations,
        [
            "function 'unsigned' bb0 switch case 0",
            "function 'unsigned' bb0 switch case 1",
            "function 'signed' bb0 switch case 0",
            "function 'signed' bb0 switch case 1",
        ]
    );
}

#[test]
fn bulk_switch_source_contract_resolves_sparse_call_result_and_repeated_switches() {
    let mut mb = ModuleBuilder::new("sparse_call_switch_source");
    let identity_ty = mb.add_func_type(vec![Ty::U8], vec![Ty::U8]);
    let mut fb = mb.function("identity", identity_ty);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U8);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    let identity = fb.build();
    let caller_ty = mb.add_func_type(vec![Ty::U8], vec![]);
    let mut fb = mb.function("caller", caller_ty);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U8);
    let next = fb.create_block();
    let finish = fb.create_block();
    fb.switch_to_block(entry);
    let result = fb.call(identity, vec![x]);
    fb.switch(
        result,
        vec![SwitchCase {
            value: Constant::Int(-1),
            target: next,
            args: vec![],
        }],
        next,
        vec![],
    );
    fb.switch_to_block(next);
    fb.switch(
        result,
        vec![SwitchCase {
            value: Constant::Int(256),
            target: finish,
            args: vec![],
        }],
        finish,
        vec![],
    );
    fb.switch_to_block(finish);
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    // This is an ordinary hand-authored sparse-ID module, not a changed
    // emitted/proved endpoint or supplied selector type.
    module.functions[0].id = FuncId::new(41);
    module.functions[1].id = FuncId::new(93);
    for node in &mut module.functions[1].blocks[0].body {
        if let Inst::Call { callee, .. } = &mut node.inst {
            *callee = FuncId::new(41);
        }
    }
    let errors = assert_exact_parity(&module);
    assert_eq!(errors.len(), 2);
    assert!(
        matches!(&errors[0], ValidationError::ConstTypeMismatch { location, .. }
        if location == "function 'caller' bb0 switch case 0")
    );
    assert!(
        matches!(&errors[1], ValidationError::ConstTypeMismatch { location, .. }
        if location == "function 'caller' bb1 switch case 0")
    );
}

#[test]
fn bulk_switch_source_contract_excludes_globals_and_const_but_preserves_full_order() {
    let mut mb = ModuleBuilder::new("switch_only_scope");
    mb.add_global(Global {
        name: "bad_global".into(),
        ty: Ty::U8,
        mutable: false,
        initializer: Some(Constant::Int(-1)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let signature = mb.add_func_type(vec![Ty::U8], vec![]);
    let mut fb = mb.function("f", signature);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U8);
    let finish = fb.create_block();
    fb.switch_to_block(entry);
    fb.const_value(Ty::I8, Constant::Int(255));
    fb.switch(
        x,
        vec![SwitchCase {
            value: Constant::Int(-1),
            target: finish,
            args: vec![],
        }],
        finish,
        vec![],
    );
    fb.switch_to_block(finish);
    fb.const_value(Ty::I8, Constant::Int(255));
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let bulk = codegen_switch_case_literal_errors(&module);
    let full = validate_module(&module);
    assert_eq!(bulk.len(), 1);
    assert_eq!(full.len(), 4);
    assert_eq!(full[2], bulk[0]);
    let locations: Vec<_> = full
        .iter()
        .map(|error| match error {
            ValidationError::ConstTypeMismatch { location, .. } => location.as_str(),
            other => panic!("only known constant errors are expected: {other:?}"),
        })
        .collect();
    assert_eq!(
        locations,
        [
            "global 'bad_global'",
            "function 'f' bb0",
            "function 'f' bb0 switch case 0",
            "function 'f' bb1",
        ]
    );
    let bool_switch = switches(&[(Ty::Bool, Constant::Bool(true))]);
    assert!(
        assert_exact_parity(&bool_switch).is_empty(),
        "bool selectors remain outside the literal contract"
    );
    let mut unrelated = ModuleBuilder::new("unrelated_global_is_not_a_switch");
    unrelated.add_global(module.globals[0].clone());
    let unrelated = unrelated
        .build()
        .expect("ModuleBuilder::build: test fixture");
    assert!(codegen_switch_case_literal_errors(&unrelated).is_empty());
    assert!(
        !validate_module(&unrelated).is_empty(),
        "an empty narrow scan must not imply module validity"
    );
}

#[test]
fn bulk_switch_source_contract_never_selects_a_duplicate_callees_output_carrier() {
    let mut mb = ModuleBuilder::new("ambiguous_switch_call_result");
    let mut callees = Vec::new();
    for (name, ty) in [("unsigned", Ty::U8), ("signed", Ty::I8)] {
        let signature = mb.add_func_type(vec![], vec![ty.clone()]);
        let mut fb = mb.function(name, signature);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let zero = fb.iconst(ty, 0);
        fb.ret(vec![zero]);
        callees.push(fb.build());
    }
    let signature = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("caller", signature);
    let entry = fb.create_block();
    let hit = fb.create_block();
    let miss = fb.create_block();
    fb.switch_to_block(entry);
    let result = fb.call(callees[0], vec![]);
    fb.switch(
        result,
        vec![SwitchCase {
            value: Constant::Int(255),
            target: hit,
            args: vec![],
        }],
        miss,
        vec![],
    );
    for block in [hit, miss] {
        fb.switch_to_block(block);
        fb.ret(vec![]);
    }
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    for function in &mut module.functions[..2] {
        function.id = FuncId::new(41);
    }
    for node in &mut module.functions[2].blocks[0].body {
        if let Inst::Call { callee, .. } = &mut node.inst {
            *callee = FuncId::new(41);
        }
    }
    // The ordinary unique-callee twins prove the case genuinely distinguishes
    // the output carriers: 255 fits U8 but does not fit I8.
    let mut unsigned = module.clone();
    unsigned.functions.remove(1);
    assert!(assert_exact_parity(&unsigned).is_empty());
    let mut signed = module.clone();
    signed.functions.remove(0);
    assert_eq!(assert_exact_parity(&signed).len(), 1);

    for _ in 0..2 {
        assert!(
            codegen_switch_case_literal_errors(&module).is_empty(),
            "an ambiguous call supplies no authenticated selector carrier"
        );
        let full = validate_module(&module);
        assert!(full.contains(&ValidationError::DuplicateFuncId(41)));
        assert!(full.contains(&ValidationError::CalleeNotFound {
            block: 0,
            callee_id: 41
        }));
        assert!(
            !full
                .iter()
                .any(|error| matches!(error, ValidationError::ConstTypeMismatch { .. })),
            "no arbitrarily selected signed declaration may invent a literal refusal: {full:?}"
        );
        module.functions.swap(0, 1);
    }
}
