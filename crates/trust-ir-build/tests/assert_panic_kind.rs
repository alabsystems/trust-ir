// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Plan item P (faithful panics, wire v52): what the validator and the codegen
// admission do with `Inst::Assert`'s kind.
//
//   * a kind's operands are `usize` SSA operands: a wrong type is
//     `OperandTypeMismatch { op: "assert", role }`, an undefined one is the
//     ordinary undefined-operand refusal;
//   * an `Unspecified` kind (every pre-v52 assert) is well-formed, so the
//     structural tier and the default codegen gate accept it, and a consumer
//     that lowers failed checks faithfully refuses it by name under
//     `CodegenAdmission::with_require_assert_panic_kinds`
//     (`ValidationError::AssertPanicKindUnspecified`), while a kinded assert
//     passes the same admission.

use trust_ir::{AssertKind, AssertOverflowOp, Inst, Module, Ty, ValueId};
use trust_ir_build::validate::{CodegenAdmission, ValidationError, unspecified_assert_kind_errors};
use trust_ir_build::{ModuleBuilder, validate_module, validate_module_for_codegen_with};

/// `check(i: T, n: T) -> T`: `assert i < n` with the kind `make(i, n)`
/// returns, then `i`. Licensed for codegen (the structural license), so the
/// codegen gate's only possible complaint is the assert.
fn module(operand_ty: Ty, make: impl FnOnce(ValueId, ValueId) -> AssertKind) -> Module {
    let mut mb = ModuleBuilder::new("assert_panic_kind");
    let ft = mb.add_func_type(
        vec![operand_ty.clone(), operand_ty.clone()],
        vec![operand_ty.clone()],
    );
    let mut fb = mb.function("check", ft);
    let entry = fb.create_block();
    let i = fb.add_block_param(entry, operand_ty.clone());
    let n = fb.add_block_param(entry, operand_ty.clone());
    fb.switch_to_block(entry);
    let in_range = fb.icmp(trust_ir::ICmpOp::Ult, operand_ty, i, n);
    fb.assert_kind(in_range, make(i, n));
    fb.ret(vec![i]);
    // A structural (non-evidence-bound) license, as the must-refuse corpus's
    // rows wear, so the license layer admits the body and the assert is the
    // codegen gate's only possible subject.
    fb.set_body_gate(trust_ir::BodyGate::Gated {
        authority: "trust-direct-lane-structural".into(),
        evidence: None,
    });
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn bounds(i: ValueId, n: ValueId) -> AssertKind {
    AssertKind::BoundsCheck { index: i, len: n }
}

#[test]
fn usize_kind_operands_validate() {
    for make in [
        bounds as fn(ValueId, ValueId) -> AssertKind,
        |r, f| AssertKind::MisalignedPtr {
            required: r,
            found: f,
        },
        |_, _| AssertKind::Overflow(AssertOverflowOp::Shl),
        |_, _| AssertKind::NullPtr,
    ] {
        let errors = validate_module(&module(Ty::Usize, make));
        assert!(errors.is_empty(), "{errors:?}");
    }
}

/// The negative twin: the same check over `u32` operands. The CONDITION is
/// still well-typed (`u32 < u32`); only the kind's operands are refused, one
/// error per role, naming the role and `usize`.
#[test]
fn a_non_usize_kind_operand_is_refused_by_role() {
    let errors = validate_module(&module(Ty::U32, bounds));
    let roles: Vec<&str> = errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::OperandTypeMismatch {
                op,
                role,
                expected,
                actual,
                ..
            } if op == "assert" && expected == "usize" && actual == "u32" => Some(role.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(roles, vec!["index", "len"], "{errors:?}");
    // An operand-free kind over the same u32 values is fine: nothing to type.
    let errors = validate_module(&module(Ty::U32, |_, _| AssertKind::DivByZero));
    assert!(errors.is_empty(), "{errors:?}");
}

/// A kind operand is an SSA USE: one that no instruction or parameter
/// defines is refused like any other undefined operand.
#[test]
fn an_undefined_kind_operand_is_refused() {
    let mut m = module(Ty::Usize, bounds);
    let body = &mut m.functions[0].blocks[0].body;
    let assert = body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::Assert { .. }))
        .expect("the assert");
    assert.inst = Inst::Assert {
        cond: match assert.inst {
            Inst::Assert { cond, .. } => cond,
            _ => unreachable!(),
        },
        kind: AssertKind::BoundsCheck {
            index: ValueId::new(0),
            len: ValueId::new(999),
        },
        site: None,
    };
    let errors = validate_module(&m);
    assert!(
        errors
            .iter()
            .any(|e| format!("{e}").contains("999") || format!("{e:?}").contains("999")),
        "the undefined %999 must be named: {errors:?}"
    );
    // Control: the defined operand alone is clean.
    assert!(validate_module(&module(Ty::Usize, bounds)).is_empty());
}

#[test]
fn the_codegen_admission_refuses_an_unspecified_assert_only_when_asked() {
    let unspecified = module(Ty::Usize, |_, _| AssertKind::Unspecified);
    let kinded = module(Ty::Usize, bounds);
    let pinned = CodegenAdmission::pinned();
    let faithful = CodegenAdmission::pinned().with_require_assert_panic_kinds(true);
    assert!(!pinned.require_assert_panic_kinds());
    assert!(faithful.require_assert_panic_kinds());

    // The default gate accepts both: an Unspecified assert is well-formed.
    assert_eq!(
        validate_module_for_codegen_with(&unspecified, &pinned),
        vec![]
    );
    assert_eq!(validate_module_for_codegen_with(&kinded, &pinned), vec![]);

    // The faithful-panic gate refuses exactly the Unspecified one, by site.
    let errors = validate_module_for_codegen_with(&unspecified, &faithful);
    assert_eq!(
        errors,
        vec![ValidationError::AssertPanicKindUnspecified {
            function: "check".to_string(),
            block: 0,
            inst_index: 1,
        }]
    );
    assert!(format!("{}", errors[0]).contains("require_assert_panic_kinds"));
    assert_eq!(validate_module_for_codegen_with(&kinded, &faithful), vec![]);
    assert_eq!(unspecified_assert_kind_errors(&kinded), vec![]);
}
