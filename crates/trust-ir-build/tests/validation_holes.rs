// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Regression tests for the validator well-formedness holes closed during the
// 2026-06 audit. Each test constructs a deliberately ill-formed module/function
// and asserts the specific `ValidationError` is reported.
//
// Numbering matches the audit finding list:
//   #1  operand/result type-validation arms (atomics, overflow, GEP, memory,
//       borrow, ARC, copy, fields)
//   #2  branch argument type mismatch vs target block params
//   #3  intra-block use-before-def ordering + dominance
//   #4  mid-block terminator / missing terminator structure
//   #5  cast operand-vs-declared-src and width direction
//   #6  entry block params vs declared FuncTy params
//   #7  dangling type-table references
//   #8  multi-result val_ty population (overflow flag is type-checked)
//   #9  Discharged obligation requires ground certificate (formula-bearing)
//   #10 duplicate ProofObligation id
//   #11 dangling ProofCertificate
//   #12 non-vector dialect ops routed through validation
//   #16 `Module::imports` is content-interned (WS4.7, F-075)
//   #17 declared struct layouts: overlap / containment / shape agreement,
//       with or without a pinned target (WS2.3 / F-031)

// WS2.5 unwind structure (and the early WS1.8 B4 scope-resolution item):
// a module of this gate-9 test target so standing gate 9 runs it.
#[path = "validation_holes/unwind_structure.rs"]
mod unwind_structure;

// WS2.7 claim-style attributes (readnone/readonly) and borrow structure.
#[path = "validation_holes/claim_attrs_and_borrows.rs"]
mod claim_attrs_and_borrows;

// WS8.7: the 2026-09-17 proof program's claim repros (F-120), one module per
// claim, ported from `reports/2026-09-17-two-language-proof-program/verify/`.
// `gap_*` rows are ratchets on today's acceptance (the fixing increment flips
// them), `bydesign_*` rows are positive fixtures, `control_*` rows are the
// single mutations that are already refused.
// c01 (F-001) is CLOSED UPSTREAM by WS1.1 (`0aeae341`, `b961642d`), which
// landed its flipped twins (`verify_c01_l1`, `verify_c01_l2`: the i64 `-1`
// headline, i8 / f64 / unbound-symbol scope, `(>= -5 0)`, the DivNonZero
// amplification), the u64 positive fixture and the binding-skipping mutation
// control in `tests/contract_clause_binding.rs` (gate 9).
// c04 (F-005) is CLOSED UPSTREAM by WS1.4 (`795f57f8`, `a78918c9`), which
// landed its flipped twins, positive fixture and producer row in
// `tests/tv_callee_binding.rs` (`verify_c04_*`, `a2_*`, `b0_*`, `b3_*`).
#[path = "validation_holes/c15_validator_leniency_eh_switch_borrow.rs"]
mod c15_validator_leniency_eh_switch_borrow;

// WS4.18 (F-081): fail-closed refusals enumerate repair options, advice
// text that no code path may read (row
// `spec-surface-0709/23-refusals-carry-repair-options`).
#[path = "validation_holes/repair_options.rs"]
mod repair_options;

// WS4.4 (NEW-1, both halves): `format::canonicalize` carries `ClausePlace::
// Value` bindings with the SSA renumbering, and every module obligation
// binding is resolved against its owning function (`InvalidObligationBinding`).
#[path = "validation_holes/ws4_4_obligation_bindings.rs"]
mod ws4_4_obligation_bindings;

// WS2.26 (F-044, DG-08): the ratified SC / single-threaded projection is
// enforced — no `DataRaceFree` / `AtomicOrdering` annotation counts toward a
// `Discharged` obligation (TRUST.md item 8).
// The paired positive fixture mints a Clean replay certificate.
#[cfg(feature = "clean-tv-anchor")]
#[path = "validation_holes/ws2_26_concurrency_claims_discharge_nothing.rs"]
mod ws2_26_concurrency_claims_discharge_nothing;

// WS4.17 (F-079 cheap half, DG-54): `DuplicateFunctionSymbol` names both
// holders' producers and display paths, and `SyntheticSymbolName` refuses the
// `<shadowed-by-` retired-row spelling (rows
// `design-0827/no-def-owns-two-rows`,
// `spec-surface-0709/03-shared-namespace-duplicates`).
#[path = "validation_holes/item_identity_diagnostics.rs"]
mod item_identity_diagnostics;

use trust_ir::inst::{AtomicRMWOp, CastOp, Inst, Ordering, OverflowOp};
use trust_ir::node::InstrNode;
use trust_ir::proof::{
    ObligationDiagnostic, ObligationKind, ProofCertificate, ProofEvidence, ProofFormula,
    ProofObligation, ProofStatus, clean_cic_lineage_digest,
};
use trust_ir::ty::{FieldDef, FuncTy, StructDef, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ProofId, SourceSpan, StructId, TyId, ValueId};
use trust_ir::{Block, Constant, Function, Module};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{validate_function, validate_module};

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn b(i: u32) -> BlockId {
    BlockId::new(i)
}
fn v(i: u32) -> ValueId {
    ValueId::new(i)
}

/// A module with a single function whose entry block is `block`, signature
/// `params -> returns`.
fn single_fn_module(name: &str, params: Vec<Ty>, returns: Vec<Ty>, block: Block) -> Module {
    let mut module = Module::new(name);
    let ft = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn ret_node() -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![] })
}

// ---------------------------------------------------------------------------
// #1 — operand/result type-validation arms
// ---------------------------------------------------------------------------

#[test]
fn load_from_non_pointer_operand_is_rejected() {
    // %0: i32 (param), load i32 from %0 — %0 is not pointer-like.
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32));
    block.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_result(v(1)),
    );
    block.body.push(ret_node());

    let module = single_fn_module("load_bad", vec![Ty::I32], vec![], block);
    let errs = validate_module(&module);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::OperandNotPointer { op, .. } if op == "load"
        )),
        "load from non-pointer must be rejected: {errs:?}"
    );
}

#[test]
fn dealloc_of_non_pointer_is_rejected() {
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I64));
    block.body.push(InstrNode::new(Inst::Dealloc { ptr: v(0) }));
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::I64], vec![], block));
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::OperandNotPointer { op, .. } if op == "dealloc")),
        "dealloc of non-pointer must be rejected: {errs:?}"
    );
}

#[test]
fn gep_index_must_be_integer() {
    // base: ptr, index: f32 -> GEP index not integer.
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::Ptr));
    block.params.push((v(1), Ty::F32));
    block.body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I32,
            base: v(0),
            indices: vec![v(1)],
            inbounds: false,
        })
        .with_result(v(2)),
    );
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::Ptr, Ty::F32], vec![], block));
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::GepIndexNotInteger { .. })),
        "gep with non-integer index must be rejected: {errs:?}"
    );
}

#[test]
fn gep_base_must_be_pointer() {
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32));
    block.params.push((v(1), Ty::I64));
    block.body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I32,
            base: v(0),
            indices: vec![v(1)],
            inbounds: false,
        })
        .with_result(v(2)),
    );
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::I32, Ty::I64], vec![], block));
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::OperandNotPointer { op, .. } if op == "gep")),
        "gep with non-pointer base must be rejected: {errs:?}"
    );
}

#[test]
fn atomic_store_value_type_must_match_declared() {
    // ptr: ptr, val: i64; atomic_store i32 *ptr = val -> value type mismatch.
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::Ptr));
    block.params.push((v(1), Ty::I64));
    block.body.push(InstrNode::new(Inst::AtomicStore {
        ty: Ty::I32,
        ptr: v(0),
        value: v(1),
        ordering: Ordering::SeqCst,
    }));
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::Ptr, Ty::I64], vec![], block));
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::OperandTypeMismatch { op, role, .. }
                if op == "atomic_store" && role == "value"
        )),
        "atomic_store value type mismatch must be rejected: {errs:?}"
    );
}

#[test]
fn atomic_load_from_non_pointer_is_rejected() {
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32));
    block.body.push(
        InstrNode::new(Inst::AtomicLoad {
            ty: Ty::I32,
            ptr: v(0),
            ordering: Ordering::Acquire,
        })
        .with_result(v(1)),
    );
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::I32], vec![], block));
    assert!(
        errs.iter().any(
            |e| matches!(e, ValidationError::OperandNotPointer { op, .. } if op == "atomic_load")
        ),
        "atomic_load from non-pointer must be rejected: {errs:?}"
    );
}

#[test]
fn atomic_rmw_value_type_must_match_declared() {
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::Ptr));
    block.params.push((v(1), Ty::I32));
    block.body.push(
        InstrNode::new(Inst::AtomicRMW {
            op: AtomicRMWOp::Add,
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::SeqCst,
        })
        .with_result(v(2)),
    );
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::Ptr, Ty::I32], vec![], block));
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::OperandTypeMismatch { op, role, .. }
                if op == "atomic_rmw" && role == "value"
        )),
        "atomic_rmw value type mismatch must be rejected: {errs:?}"
    );
}

#[test]
fn cmpxchg_pointer_and_value_types_checked() {
    // ptr is an integer (not pointer), expected has wrong type.
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32)); // bad ptr
    block.params.push((v(1), Ty::I64)); // bad expected (declared i32)
    block.params.push((v(2), Ty::I32)); // ok desired
    block.body.push(
        InstrNode::new(Inst::CmpXchg {
            ty: Ty::I32,
            ptr: v(0),
            expected: v(1),
            desired: v(2),
            success: Ordering::SeqCst,
            failure: Ordering::SeqCst,
            weak: false,
        })
        .with_results([v(3), v(4)]),
    );
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(
        vec![Ty::I32, Ty::I64, Ty::I32],
        vec![],
        block,
    ));
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::OperandNotPointer { op, .. } if op == "cmpxchg")),
        "cmpxchg with non-pointer ptr must be rejected: {errs:?}"
    );
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::OperandTypeMismatch { op, role, .. }
                if op == "cmpxchg" && role == "expected"
        )),
        "cmpxchg expected type mismatch must be rejected: {errs:?}"
    );
}

#[test]
fn overflow_operands_must_be_integer_and_agree() {
    // overflow on f32 (not integer) with mismatched operands.
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::F32));
    block.params.push((v(1), Ty::F32));
    block.body.push(
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::F32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_results([v(2), v(3)]),
    );
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::F32, Ty::F32], vec![], block));
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::OperandNotInteger { op, .. } if op.contains("overflow"))),
        "overflow on non-integer type must be rejected: {errs:?}"
    );
}

#[test]
fn copy_result_type_must_match_operand() {
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32));
    // copy i64 of an i32 operand -> operand type mismatch.
    block.body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::I64,
            operand: v(0),
        })
        .with_result(v(1)),
    );
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::I32], vec![], block));
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::OperandTypeMismatch { op, role, .. }
                if op == "copy" && role == "operand"
        )),
        "copy with mismatched operand type must be rejected: {errs:?}"
    );
}

#[test]
fn borrow_and_retain_require_pointer_operand() {
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32));
    block
        .body
        .push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
    block.body.push(InstrNode::new(Inst::Retain { ptr: v(0) }));
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::I32], vec![], block));
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::OperandNotPointer { op, .. } if op == "borrow")),
        "borrow of non-pointer must be rejected: {errs:?}"
    );
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::OperandNotPointer { op, .. } if op == "retain")),
        "retain of non-pointer must be rejected: {errs:?}"
    );
}

#[test]
fn is_unique_requires_pointer_operand() {
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32));
    block
        .body
        .push(InstrNode::new(Inst::IsUnique { ptr: v(0) }).with_result(v(1)));
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::I32], vec![], block));
    assert!(
        errs.iter().any(
            |e| matches!(e, ValidationError::OperandNotPointer { op, .. } if op == "is_unique")
        ),
        "is_unique of non-pointer must be rejected: {errs:?}"
    );
}

#[test]
fn extract_field_index_out_of_range_is_rejected() {
    // struct Pair { a: i32, b: i64 }; extract field 5.
    let mut module = Module::new("field_oob");
    let sid = StructId::new(0);
    module.add_struct(StructDef {
        id: sid,
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: Some(0),
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::I64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),

        repr: Default::default(),
        origin: None,
    });
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Struct(sid)],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::Struct(sid)));
    block.body.push(
        InstrNode::new(Inst::ExtractField {
            ty: Ty::I32,
            aggregate: v(0),
            field: 5,
        })
        .with_result(v(1)),
    );
    block.body.push(ret_node());
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let errs = validate_module(&module);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::FieldAccessInvalid { op, reason, .. }
                if op == "extract_field" && reason.contains("out of range")
        )),
        "extract_field with out-of-range index must be rejected: {errs:?}"
    );
}

#[test]
fn extract_field_wrong_field_type_is_rejected() {
    // Pair { a: i32, b: i64 }; extract field 1 declared as i32 (should be i64).
    let mut module = Module::new("field_ty");
    let sid = StructId::new(0);
    module.add_struct(StructDef {
        id: sid,
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: Some(0),
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::I64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),

        repr: Default::default(),
        origin: None,
    });
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Struct(sid)],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::Struct(sid)));
    block.body.push(
        InstrNode::new(Inst::ExtractField {
            ty: Ty::I32, // wrong: field 1 is i64
            aggregate: v(0),
            field: 1,
        })
        .with_result(v(1)),
    );
    block.body.push(ret_node());
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let errs = validate_module(&module);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::OperandTypeMismatch { op, role, .. }
                if op == "extract_field" && role == "field"
        )),
        "extract_field with wrong declared field type must be rejected: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #2 — branch argument type mismatch
// ---------------------------------------------------------------------------

#[test]
fn branch_arg_type_mismatch_is_rejected() {
    // bb0(%0: i32): br bb1(%0)   bb1(%1: i64): ret   -> i32 arg to i64 param.
    let mut module = Module::new("branch_ty");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));

    let mut bb0 = Block::new(b(0));
    bb0.params.push((v(0), Ty::I32));
    bb0.body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![v(0)],
    }));

    let mut bb1 = Block::new(b(1));
    bb1.params.push((v(1), Ty::I64));
    bb1.body.push(ret_node());

    func.blocks.push(bb0);
    func.blocks.push(bb1);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let errs = validate_module(&module);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::BranchArgTypeMismatch {
                target: 1,
                arg_index: 0,
                ..
            }
        )),
        "branch arg type mismatch must be rejected: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #3 — intra-block use-before-def
// ---------------------------------------------------------------------------

#[test]
fn forward_reference_within_block_is_rejected() {
    // %1 = copy %2 ; %2 = const 0  -> %2 used before defined in the same block.
    let mut block = Block::new(b(0));
    block.body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand: v(2),
        })
        .with_result(v(1)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        })
        .with_result(v(2)),
    );
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![], vec![], block));
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::UseBeforeDefInBlock { value: 2, block: 0 }
        )),
        "forward reference within a block must be rejected: {errs:?}"
    );
}

#[test]
fn use_of_value_from_non_dominating_block_is_rejected() {
    // bb0 -> condbr bb1/bb2 ; bb1 defines %5 ; bb2 uses %5 (bb1 does not
    // dominate bb2) -> non-dominated use.
    let mut module = Module::new("dom");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));

    let mut bb0 = Block::new(b(0));
    bb0.params.push((v(0), Ty::Bool));
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: v(0),
        then_target: b(1),
        then_args: vec![],
        else_target: b(2),
        else_args: vec![],
    }));

    let mut bb1 = Block::new(b(1));
    bb1.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(v(5)),
    );
    bb1.body.push(InstrNode::new(Inst::Br {
        target: b(3),
        args: vec![],
    }));

    let mut bb2 = Block::new(b(2));
    // Uses %5 defined in bb1, which does NOT dominate bb2.
    bb2.body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand: v(5),
        })
        .with_result(v(6)),
    );
    bb2.body.push(InstrNode::new(Inst::Br {
        target: b(3),
        args: vec![],
    }));

    let mut bb3 = Block::new(b(3));
    bb3.body.push(ret_node());

    func.blocks.extend([bb0, bb1, bb2, bb3]);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let errs = validate_function(&func_only(&module));
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::UseBeforeDefInBlock { value: 5, block: 2 }
        )),
        "use of value from a non-dominating block must be rejected: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #4 — mid-block / missing terminator
// ---------------------------------------------------------------------------

#[test]
fn mid_block_terminator_is_rejected() {
    // bb0: br bb1 (mid) ; const ; ret
    let mut module = Module::new("midterm");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
    let mut bb0 = Block::new(b(0));
    bb0.body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![],
    }));
    bb0.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        })
        .with_result(v(0)),
    );
    bb0.body.push(ret_node());
    let mut bb1 = Block::new(b(1));
    bb1.body.push(ret_node());
    func.blocks.push(bb0);
    func.blocks.push(bb1);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let errs = validate_function(&func_only(&module));
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::MidBlockTerminator { block: 0, .. })),
        "mid-block terminator must be rejected: {errs:?}"
    );
}

#[test]
fn block_without_trailing_terminator_is_rejected() {
    // bb0: const (no terminator).
    let mut block = Block::new(b(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        })
        .with_result(v(0)),
    );
    let errs = validate_function(&single_fn_function(vec![], vec![], block));
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::MissingTerminator { block: 0 })),
        "block whose last node is not a terminator must be rejected: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #5 — cast operand-vs-src and width direction
// ---------------------------------------------------------------------------

#[test]
fn cast_operand_type_must_match_declared_src() {
    // %0: i64; trunc i32 -> i16 of %0  (operand is i64, declared src i32).
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I64));
    block.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::I32,
            dst_ty: Ty::I16,
            operand: v(0),
        })
        .with_result(v(1)),
    );
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::I64], vec![], block));
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::CastOperandTypeMismatch { .. })),
        "cast operand type not matching declared src must be rejected: {errs:?}"
    );
}

#[test]
fn trunc_to_wider_type_is_rejected() {
    // trunc i16 -> i32: src width 16 <= dst width 32 -> wrong direction.
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I16));
    block.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::I16,
            dst_ty: Ty::I32,
            operand: v(0),
        })
        .with_result(v(1)),
    );
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::I16], vec![], block));
    assert!(
        errs.iter().any(
            |e| matches!(e, ValidationError::CastWidthDirectionInvalid { op, .. } if op == "trunc")
        ),
        "trunc to a wider type must be rejected: {errs:?}"
    );
}

#[test]
fn zext_to_narrower_type_is_rejected() {
    // zext i32 -> i16: src >= dst -> wrong direction.
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32));
    block.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::I32,
            dst_ty: Ty::I16,
            operand: v(0),
        })
        .with_result(v(1)),
    );
    block.body.push(ret_node());

    let errs = validate_function(&single_fn_function(vec![Ty::I32], vec![], block));
    assert!(
        errs.iter().any(
            |e| matches!(e, ValidationError::CastWidthDirectionInvalid { op, .. } if op == "zext")
        ),
        "zext to a narrower type must be rejected: {errs:?}"
    );
}

#[test]
fn bool_resize_casts_reject_wrong_width_directions() {
    let cases = [
        (CastOp::ZExt, Ty::I8, Ty::Bool),
        (CastOp::SExt, Ty::I8, Ty::Bool),
        (CastOp::Trunc, Ty::Bool, Ty::I8),
    ];
    for (op, src_ty, dst_ty) in cases {
        let mut block = Block::new(b(0));
        block.params.push((v(0), src_ty.clone()));
        block.body.push(
            InstrNode::new(Inst::Cast {
                op,
                src_ty: src_ty.clone(),
                dst_ty: dst_ty.clone(),
                operand: v(0),
            })
            .with_result(v(1)),
        );
        block.body.push(ret_node());

        let errs = validate_function(&single_fn_function(vec![src_ty], vec![], block));
        assert!(
            errs.iter()
                .any(|error| matches!(error, ValidationError::CastWidthDirectionInvalid { .. })),
            "{op} with wrong Bool width direction must be rejected: {errs:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// #6 — entry params vs signature
// ---------------------------------------------------------------------------

#[test]
fn entry_params_count_mismatch_is_rejected() {
    // signature () but entry block has a param.
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32));
    block.body.push(ret_node());
    let module = single_fn_module("entry_count", vec![], vec![], block);
    let errs = validate_module(&module);
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::EntryParamsMismatch { .. })),
        "entry param count mismatch must be rejected: {errs:?}"
    );
}

#[test]
fn entry_params_type_mismatch_is_rejected() {
    // signature (i64) but entry block param is i32.
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32));
    block.body.push(ret_node());
    let module = single_fn_module("entry_type", vec![Ty::I64], vec![], block);
    let errs = validate_module(&module);
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::EntryParamsMismatch { .. })),
        "entry param type mismatch must be rejected: {errs:?}"
    );
}

#[test]
fn matching_entry_params_validate() {
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I64));
    block.body.push(ret_node());
    let module = single_fn_module("entry_ok", vec![Ty::I64], vec![], block);
    let errs = validate_module(&module);
    assert!(
        !errs
            .iter()
            .any(|e| matches!(e, ValidationError::EntryParamsMismatch { .. })),
        "matching entry params must NOT trip the check: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #7 — dangling type-table references
// ---------------------------------------------------------------------------

#[test]
fn dangling_struct_reference_in_signature_is_rejected() {
    // No structs defined, but a func type references struct.7.
    let mut module = Module::new("dangling_struct");
    module
        .add_func_type(FuncTy {
            params: vec![Ty::Struct(StructId::new(7))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let errs = validate_module(&module);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::DanglingTypeReference {
                kind: "struct",
                id: 7,
                ..
            }
        )),
        "dangling struct reference must be rejected: {errs:?}"
    );
}

#[test]
fn dangling_tyid_in_array_is_rejected() {
    // Array(ty.9, 4) with no type-table entry at 9.
    let mut module = Module::new("dangling_ty");
    module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Array(TyId::new(9), 4)],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let errs = validate_module(&module);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::DanglingTypeReference {
                kind: "ty",
                id: 9,
                ..
            }
        )),
        "dangling TyId in array element must be rejected: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #8 — multi-result val_ty population (overflow bool flag is typed)
// ---------------------------------------------------------------------------

#[test]
fn overflow_bool_flag_is_typed_and_checked() {
    // %0,%1: i32; (%2: i32, %3: bool) = add_overflow %0, %1
    // condbr on %2 (the value, an i32) instead of %3 (the bool flag) ->
    // CondBrRequiresBool, proving %2 got a real type from the multi-result map.
    let mut module = Module::new("overflow_flag");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
    let mut bb0 = Block::new(b(0));
    bb0.params.push((v(0), Ty::I32));
    bb0.params.push((v(1), Ty::I32));
    bb0.body.push(
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_results([v(2), v(3)]),
    );
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: v(2), // the i32 value, NOT the bool flag %3
        then_target: b(1),
        then_args: vec![],
        else_target: b(1),
        else_args: vec![],
    }));
    let mut bb1 = Block::new(b(1));
    bb1.body.push(ret_node());
    func.blocks.push(bb0);
    func.blocks.push(bb1);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let errs = validate_module(&module);
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::CondBrRequiresBool { .. })),
        "overflow value result must be typed i32 (not bool): {errs:?}"
    );
    // And the bool flag %3 IS bool: using it in condbr must NOT trip the check.
    // (Covered implicitly: only one CondBrRequiresBool is expected.)
}

// ---------------------------------------------------------------------------
// #9 / #10 / #11 — proof obligation integrity
// ---------------------------------------------------------------------------

fn trivial_module(name: &str) -> Module {
    let mut block = Block::new(b(0));
    block.body.push(ret_node());
    single_fn_module(name, vec![], vec![], block)
}

#[test]
fn discharged_obligation_with_formula_requires_certificate() {
    let mut m = trivial_module("discharged");
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "claims a real proof",
        )
        .with_formula(ProofFormula::new("trust-types.Formula@1", "x > 0")),
    );
    // No certificate at all.
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::DischargedWithoutCertificate { obligation: 0 }
        )),
        "formula-bearing Discharged obligation without evidence must be rejected: {errs:?}"
    );
}

#[test]
fn discharged_obligation_with_formula_and_opaque_smt_bytes_is_rejected() {
    let mut m = trivial_module("discharged_ok");
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "claims a real proof",
        )
        .with_formula(ProofFormula::new("trust-types.Formula@1", "x > 0")),
    );
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "ay".into(),
        evidence: ProofEvidence::SmtProof(vec![1, 2, 3]),
        assurance: None,
    });
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::DischargedWithoutCertificate { obligation: 0 }
        )),
        "producer-provided SMT bytes must not authorize a Discharged label: {errs:?}"
    );
}

#[test]
fn duplicate_proof_obligation_id_is_rejected() {
    let mut m = trivial_module("dup_oblig");
    for _ in 0..2 {
        m.proof_obligations.push(ProofObligation::new(
            ProofId::new(3),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "o",
        ));
    }
    let errs = validate_module(&m);
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::DuplicateProofObligationId(3))),
        "duplicate proof obligation id must be rejected: {errs:?}"
    );
}

#[test]
fn dangling_proof_certificate_is_rejected() {
    let mut m = trivial_module("dangling_cert");
    // Certificate for obligation #42 which does not exist.
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(42),
        prover: "ay".into(),
        evidence: ProofEvidence::SmtProof(vec![0]),
        assurance: None,
    });
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::DanglingProofCertificate { obligation: 42 }
        )),
        "certificate for a non-existent obligation must be rejected: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #12 — non-vector dialects routed through validation
// ---------------------------------------------------------------------------

#[test]
fn unknown_gpu_dialect_op_is_rejected() {
    use trust_ir::dialect::DialectInst;
    // gpu.not_a_real_op is not a registered gpu op.
    let op = DialectInst::new("gpu", "not_a_real_op").with_result_ty(Ty::U32);
    let mut block = Block::new(b(0));
    block
        .body
        .push(InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(v(0)));
    block.body.push(ret_node());
    let module = single_fn_module("gpu_dialect", vec![], vec![], block);
    let errs = validate_module(&module);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::InvalidVectorDialectOp { op, .. } if op.starts_with("gpu.")
        )),
        "unknown gpu dialect op must be rejected (not just vector): {errs:?}"
    );
}

#[test]
fn well_formed_gpu_dialect_op_validates() {
    let op = trust_ir::dialect::gpu::thread_id_x();
    let mut block = Block::new(b(0));
    block
        .body
        .push(InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(v(0)));
    block.body.push(ret_node());
    let module = single_fn_module("gpu_ok", vec![], vec![], block);
    let errs = validate_module(&module);
    assert!(
        !errs
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidVectorDialectOp { .. })),
        "well-formed gpu.thread_id_x must validate: {errs:?}"
    );
}

#[test]
fn exact_trust_rust_tls_address_validates_and_near_miss_is_rejected() {
    use trust_ir::dialect::trust_rust;

    let exact = trust_rust::thread_local_addr("crate::TLS");
    let mut block = Block::new(b(0));
    block
        .body
        .push(InstrNode::new(Inst::DialectOp(Box::new(exact))).with_result(v(0)));
    block.body.push(ret_node());
    let module = single_fn_module("trust_rust_tls_ok", vec![], vec![], block);
    let errs = validate_module(&module);
    assert!(
        !errs
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidVectorDialectOp { .. })),
        "canonical trust_rust.thread_local_addr must validate: {errs:?}"
    );

    let mut near_miss = trust_rust::thread_local_addr("crate::TLS");
    near_miss.version = 2;
    let mut block = Block::new(b(0));
    block
        .body
        .push(InstrNode::new(Inst::DialectOp(Box::new(near_miss))).with_result(v(0)));
    block.body.push(ret_node());
    let module = single_fn_module("trust_rust_tls_bad", vec![], vec![], block);
    let errs = validate_module(&module);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::InvalidVectorDialectOp { op, .. }
                if op == "trust_rust.thread_local_addr"
        )),
        "a trust_rust schema near miss must fail validation: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #13 — Certified gate requires a NON-EMPTY CleanCic term (forgery floor)
// ---------------------------------------------------------------------------

#[test]
fn certified_with_empty_term_clean_cic_is_rejected() {
    // The cheapest forgery: stamp Certified, attach a CleanCic whose `term` is
    // empty but whose `lineage` is the (publicly recomputable) digest of the
    // obligation. The lineage matches, but there is NO kernel-checkable content,
    // so the Certified tier (strictly stronger than Trusted) must NOT be granted.
    let mut m = trivial_module("empty_term_cleancic");
    let oblig = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "claims a kernel-checked proof",
    )
    .with_formula(ProofFormula::new("trust-types.Formula@1", "x > 0"));
    let lineage = clean_cic_lineage_digest(&oblig);
    m.proof_obligations.push(oblig);
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "forger".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![], // empty — no checkable content
            context: vec![],
            lineage, // correct digest, recomputable from the public obligation
            kernel_recheck: None,
        },
        assurance: None,
    });
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedWithoutCleanCic { obligation: 0 }
        )),
        "empty-term CleanCic must NOT satisfy the Certified gate: {errs:?}"
    );
}

#[test]
fn certified_with_nonempty_term_clean_cic_validates() {
    // Positive control: the same obligation with a NON-empty term + correct
    // lineage is admitted as Certified.
    let mut m = trivial_module("nonempty_term_cleancic");
    let oblig = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "claims a kernel-checked proof",
    )
    .with_formula(ProofFormula::new("trust-types.Formula@1", "x > 0"));
    let lineage = clean_cic_lineage_digest(&oblig);
    m.proof_obligations.push(oblig);
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "clean".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![1, 2, 3],
            context: vec![],
            lineage,
            kernel_recheck: None,
        },
        assurance: None,
    });
    let errs = validate_module(&m);
    assert!(
        !errs.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedWithoutCleanCic { .. }
                | ValidationError::CertifiedCleanCicLineageMismatch { .. }
        )),
        "non-empty CleanCic bound to the obligation must validate: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #14 — memory-access alignment must be a positive power of two
// ---------------------------------------------------------------------------

fn block_with_aligned_load(align: Option<u64>) -> Block {
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::Ptr));
    block.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align,
        })
        .with_result(v(1)),
    );
    block.body.push(ret_node());
    block
}

#[test]
fn load_with_non_power_of_two_align_is_rejected() {
    let module = single_fn_module(
        "bad_align",
        vec![Ty::Ptr],
        vec![],
        block_with_aligned_load(Some(3)),
    );
    let errs = validate_module(&module);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::AccessAlignInvalid {
                inst: "load",
                align: 3
            }
        )),
        "align=3 (not a power of two) must be rejected: {errs:?}"
    );
}

#[test]
fn alloca_with_zero_align_is_rejected() {
    let mut block = Block::new(b(0));
    block.body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::I32,
            count: None,
            align: Some(0),
        })
        .with_result(v(0)),
    );
    block.body.push(ret_node());
    let errs = validate_function(&single_fn_function(vec![], vec![], block));
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::AccessAlignInvalid {
                inst: "alloca",
                align: 0
            }
        )),
        "align=0 must be rejected: {errs:?}"
    );
}

#[test]
fn load_with_power_of_two_align_validates() {
    let module = single_fn_module(
        "ok_align",
        vec![Ty::Ptr],
        vec![],
        block_with_aligned_load(Some(8)),
    );
    let errs = validate_module(&module);
    assert!(
        !errs
            .iter()
            .any(|e| matches!(e, ValidationError::AccessAlignInvalid { .. })),
        "align=8 (a power of two) must validate: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #14b — Wrapping conflicts with NoOverflow/NoWrap (contradictory claims)
// ---------------------------------------------------------------------------

#[test]
fn wrapping_with_no_overflow_is_rejected() {
    use trust_ir::ProofAnnotation;
    use trust_ir::inst::BinOp as BinOpKind;
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I32));
    block.params.push((v(1), Ty::I32));
    let mut node = InstrNode::new(Inst::BinOp {
        op: BinOpKind::Add,
        ty: Ty::I32,
        lhs: v(0),
        rhs: v(1),
    })
    .with_result(v(2));
    node.proofs.push(ProofAnnotation::Wrapping);
    node.proofs.push(ProofAnnotation::NoOverflow);
    block.body.push(node);
    block.body.push(ret_node());
    let errs = validate_function(&single_fn_function(vec![Ty::I32, Ty::I32], vec![], block));
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::WrappingConflictsWithNoOverflow { block: 0 }
        )),
        "Wrapping + NoOverflow on one node must be rejected: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #15 — obligation-diagnostic source location indexes Module.files
// ---------------------------------------------------------------------------

#[test]
fn diagnostic_location_with_dangling_file_index_is_rejected() {
    let mut m = trivial_module("diag_loc");
    m.proof_obligations.push(ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Precondition,
        ProofStatus::Failed,
        "o",
    ));
    let _f0 = m
        .intern_file("src/lib.rs")
        .expect("Module::intern_file: test fixture"); // files.len() == 1, valid index is 0
    m.obligation_diagnostics.push(
        ObligationDiagnostic::error(ProofId::new(0), "boom").with_location(SourceSpan {
            file: 999, // out of range
            line: 1,
            col: 1,
        }),
    );
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::SpanFileIndexOutOfRange { file: 999, .. }
        )),
        "diagnostic location with a dangling file index must be rejected: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// #16 — `Module::imports` is content-interned (WS4.7, F-075)
// ---------------------------------------------------------------------------

/// A module carrying one interned import row per producer of a MIXED
/// dependency: the same name and digest, `TRust` and `Clean`. Nothing cites
/// the rows, so every tier's verdict on the table is the interning rule alone.
fn two_producer_importer() -> Module {
    use trust_ir::{Endianness, ModuleImport, Producer, TargetInfo};
    let mut m = trivial_module("importer");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let digest = Module::new("mixed_dep").stable_digest();
    let rust = m
        .intern_import(ModuleImport::new("mixed_dep", digest).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    let clean = m
        .intern_import(ModuleImport::new("mixed_dep", digest).with_producer(Producer::Clean))
        .expect("Module::intern_import: test fixture");
    assert_ne!(rust, clean);
    m
}

fn import_not_interned(errs: &[ValidationError], first: u32, duplicate: u32) -> bool {
    errs.iter().any(|e| {
        matches!(
            e,
            ValidationError::ImportTableNotInterned { first: f, duplicate: d, name }
                if *f == first && *d == duplicate && name == "mixed_dep"
        )
    })
}

#[test]
fn import_table_with_one_row_per_producer_is_interned() {
    // Positive: rows sharing a digest but differing in producer are distinct
    // edges (ratified, SPEC_RATIFICATIONS §6), and re-interning either is a no-op.
    let mut m = two_producer_importer();
    let again = m
        .intern_import(m.imports[1].clone())
        .expect("Module::intern_import: test fixture");
    assert_eq!(again.index(), 1);
    assert_eq!(m.imports.len(), 2);
    let errs = validate_module(&m);
    assert!(
        !errs
            .iter()
            .any(|e| matches!(e, ValidationError::ImportTableNotInterned { .. })),
        "{errs:?}"
    );
}

#[test]
fn pushed_duplicate_import_row_is_refused_in_every_tier() {
    use trust_ir::proof::RejectingModuleProofAuthority;
    use trust_ir_build::{
        validate_module_for_codegen, validate_module_report, validate_module_report_with_authority,
        validate_module_with_authority,
    };

    // Negative twin: a pushed (not interned) clone of `imports[0]`.
    let mut m = two_producer_importer();
    m.imports.push(m.imports[0].clone());
    m.imports.push(m.imports[1].clone());
    for (tier, errs) in [
        ("validate_module", validate_module(&m)),
        (
            "validate_module_report",
            validate_module_report(&m).into_errors(),
        ),
        (
            "validate_module_with_authority",
            validate_module_with_authority(&m, &RejectingModuleProofAuthority),
        ),
        (
            "validate_module_report_with_authority",
            validate_module_report_with_authority(&m, &RejectingModuleProofAuthority).into_errors(),
        ),
        (
            "validate_module_for_codegen",
            validate_module_for_codegen(&m),
        ),
    ] {
        assert!(import_not_interned(&errs, 0, 2), "{tier}: {errs:?}");
        assert!(import_not_interned(&errs, 1, 3), "{tier}: {errs:?}");
        let reported = errs
            .iter()
            .filter(|e| matches!(e, ValidationError::ImportTableNotInterned { .. }))
            .count();
        assert_eq!(reported, 2, "{tier}: once per duplicate row: {errs:?}");
    }
    let rendered = validate_module(&m)
        .iter()
        .find(|e| matches!(e, ValidationError::ImportTableNotInterned { .. }))
        .map(ToString::to_string)
        .unwrap();
    assert!(rendered.contains("intern_import"), "{rendered}");

    // Mutation control: the key is the WHOLE row. Changing any one component
    // of the clone — name, digest or producer — makes it a distinct row.
    let base = two_producer_importer();
    let mut renamed = base.clone();
    let mut row = base.imports[0].clone();
    row.name = "other_dep".into();
    renamed.imports.push(row);
    let mut redigested = base.clone();
    let mut row = base.imports[0].clone();
    row.digest = Module::new("other_dep").stable_digest();
    redigested.imports.push(row);
    let mut unrecorded = base.clone();
    let mut row = base.imports[0].clone();
    row.producer = None;
    unrecorded.imports.push(row);
    for (what, module) in [
        ("name", renamed),
        ("digest", redigested),
        ("producer", unrecorded),
    ] {
        let errs = validate_module(&module);
        assert!(
            !errs
                .iter()
                .any(|e| matches!(e, ValidationError::ImportTableNotInterned { .. })),
            "a row differing in {what} is not a duplicate: {errs:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// #16b — one artifact, one name across the import table (WS1.16, F-077)
// ---------------------------------------------------------------------------

fn identity_conflict(errs: &[ValidationError], first: u32, conflicting: u32) -> bool {
    errs.iter().any(|e| {
        matches!(
            e,
            ValidationError::ImportIdentityConflict {
                first: f,
                conflicting: c,
                first_name,
                conflicting_name,
            } if *f == first && *c == conflicting && first_name == "mixed_dep"
                && conflicting_name == "renamed_dep"
        )
    })
}

fn any_identity_conflict(errs: &[ValidationError]) -> bool {
    errs.iter()
        .any(|e| matches!(e, ValidationError::ImportIdentityConflict { .. }))
}

#[test]
fn ws1_16_rows_sharing_a_digest_and_name_across_producers_are_valid() {
    // Positive: the ratified two-producer shape — same digest, same name,
    // different producers — is one artifact under one name.
    let m = two_producer_importer();
    assert_eq!(m.imports[0].digest, m.imports[1].digest);
    assert_eq!(m.imports[0].name, m.imports[1].name);
    assert_ne!(m.imports[0].producer, m.imports[1].producer);
    let errs = validate_module(&m);
    assert!(!any_identity_conflict(&errs), "{errs:?}");
    assert!(errs.is_empty(), "the ratified shape validates: {errs:?}");
}

#[test]
fn ws1_16_rows_sharing_a_digest_under_two_names_are_import_identity_conflict() {
    use trust_ir::proof::RejectingModuleProofAuthority;
    use trust_ir_build::{
        validate_module_for_codegen, validate_module_report, validate_module_report_with_authority,
        validate_module_with_authority,
    };

    // Negative twin: the SAME two rows, the Clean row renamed. One digest is
    // one artifact, and an artifact has one `Module::name`.
    let mut m = two_producer_importer();
    m.imports[1].name = "renamed_dep".into();
    for (tier, errs) in [
        ("validate_module", validate_module(&m)),
        (
            "validate_module_report",
            validate_module_report(&m).into_errors(),
        ),
        (
            "validate_module_with_authority",
            validate_module_with_authority(&m, &RejectingModuleProofAuthority),
        ),
        (
            "validate_module_report_with_authority",
            validate_module_report_with_authority(&m, &RejectingModuleProofAuthority).into_errors(),
        ),
        (
            "validate_module_for_codegen",
            validate_module_for_codegen(&m),
        ),
    ] {
        assert!(identity_conflict(&errs, 0, 1), "{tier}: {errs:?}");
        assert_eq!(
            errs.iter()
                .filter(|e| matches!(e, ValidationError::ImportIdentityConflict { .. }))
                .count(),
            1,
            "{tier}: once per conflicting row: {errs:?}"
        );
        // The rows differ, so this is not (also) an interning violation.
        assert!(
            !errs
                .iter()
                .any(|e| matches!(e, ValidationError::ImportTableNotInterned { .. })),
            "{tier}: {errs:?}"
        );
    }
    let rendered = validate_module(&m)
        .iter()
        .find(|e| matches!(e, ValidationError::ImportIdentityConflict { .. }))
        .map(ToString::to_string)
        .unwrap();
    assert!(rendered.contains("same digest"), "{rendered}");

    // The scheme is not an escape: the renamed row recorded under V2 with the
    // same digest bytes is still one artifact under two names.
    let mut rescheme = m.clone();
    rescheme.imports[1].scheme = trust_ir::IdentityScheme::V2;
    assert!(identity_conflict(&validate_module(&rescheme), 0, 1));

    // Mutation control: give the renamed row ITS OWN digest (a different
    // artifact) and the conflict disappears — the key is the digest.
    let mut distinct = m.clone();
    distinct.imports[1].digest = Module::new("renamed_dep").stable_digest();
    let errs = validate_module(&distinct);
    assert!(!any_identity_conflict(&errs), "{errs:?}");
}

/// WS1.16 review, over-refusal control: the rule keys on the DIGEST, never on
/// the name. Two builds of one crate NAME are two artifacts with two
/// identities, and recording both stays legal — a module that legitimately
/// imports two versions of `mixed_dep` must not be refused by the new rule.
#[test]
fn ws1_16_one_name_under_two_digests_is_two_artifacts_and_validates() {
    let mut m = two_producer_importer();
    m.imports[1].digest = Module::new("mixed_dep_rebuilt").stable_digest();
    assert_eq!(m.imports[0].name, m.imports[1].name);
    assert_ne!(m.imports[0].digest, m.imports[1].digest);
    let errs = validate_module(&m);
    assert!(!any_identity_conflict(&errs), "{errs:?}");
    assert!(
        errs.is_empty(),
        "two versions of one name validate: {errs:?}"
    );
}

/// WS1.16 review, adversarial arity: with THREE or more rows under one digest,
/// every later disagreeing row is reported once and against the FIRST row —
/// not pairwise, and not once for the whole table. A later row that AGREES
/// with the first is no conflict, whatever the rows between it say; being
/// equal to the first is the interning rule's business, not this one.
#[test]
fn ws1_16_each_later_conflicting_row_is_reported_once_against_the_first() {
    use trust_ir::{ModuleImport, Producer};

    let conflicts = |m: &Module| -> Vec<(u32, u32, String)> {
        validate_module(m)
            .iter()
            .filter_map(|e| match e {
                ValidationError::ImportIdentityConflict {
                    first,
                    conflicting,
                    conflicting_name,
                    ..
                } => Some((*first, *conflicting, conflicting_name.clone())),
                _ => None,
            })
            .collect()
    };

    // Names a, b, c under one digest: two conflicts, both against row 0.
    let mut m = two_producer_importer();
    let digest = m.imports[0].digest;
    m.imports[1].name = "second".into();
    m.imports
        .push(ModuleImport::new("third", digest).with_producer(Producer::TrustIr));
    assert_eq!(
        conflicts(&m),
        vec![(0, 1, "second".to_string()), (0, 2, "third".to_string()),],
        "{:?}",
        validate_module(&m)
    );

    // Names a, b, a: only row 1 disagrees. Row 2 equals row 0, which the
    // interning rule — and only it — refuses.
    let mut repeat = two_producer_importer();
    repeat.imports[1].name = "second".into();
    let row0 = repeat.imports[0].clone();
    repeat.imports.push(row0);
    assert_eq!(
        conflicts(&repeat),
        vec![(0, 1, "second".to_string())],
        "{:?}",
        validate_module(&repeat)
    );
    assert!(
        import_not_interned(&validate_module(&repeat), 0, 2),
        "{:?}",
        validate_module(&repeat)
    );
}

// ---------------------------------------------------------------------------
// WS2.1 (F-028): `CoroSuspend` is a return-shaped terminator
// ---------------------------------------------------------------------------
//
// `Inst::CoroSuspend { frame, state_slot, next_state, value }` is DEFINED as
// `GEP(frame, state_slot)` + `Store(next_state)` + `Return(value)`. Only
// `Inst::Return` was compared with `FuncTy::returns`, and `frame` was never
// typed. The suspend now shares `check_return_values` with `Return` (as the
// one-operand `Return` of `value`) and `frame` is held to the GEP-base rule.
// Each twin below is ONE edit from `coro_suspend_module(Ptr, U64, [U64])`.

/// `fn f(%0: frame_ty, %1: value_ty) -> returns { coro_suspend %0, 0, 1, %1 }`.
fn coro_suspend_module(frame_ty: Ty, value_ty: Ty, returns: Vec<Ty>) -> Module {
    let mut block = Block::new(b(0))
        .with_param(v(0), frame_ty.clone())
        .with_param(v(1), value_ty.clone());
    block.body.push(InstrNode::new(Inst::CoroSuspend {
        frame: v(0),
        state_slot: 0,
        next_state: 1,
        value: v(1),
    }));
    single_fn_module("coro_suspend", vec![frame_ty, value_ty], returns, block)
}

/// As `coro_suspend_module`, with the yielded value (and optionally the
/// return slot) refined by the interval `lo..=hi` over `base`.
fn refined_coro_suspend_module(
    base: Ty,
    refine_value: bool,
    refine_return: bool,
    returns_base: Ty,
) -> Module {
    let mut module = Module::new("coro_suspend_refined");
    let base_id = module
        .add_type(base.clone())
        .expect("Module::add_type: test fixture");
    let pred = module
        .intern_pred(trust_ir::Pred::Interval { lo: 0, hi: 8 })
        .expect("Module::intern_pred: test fixture")
        .expect("canonical interval");
    let refined = Ty::Refine(base_id, pred);
    let value_ty = if refine_value { refined.clone() } else { base };
    let return_ty = if refine_return { refined } else { returns_base };
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, value_ty.clone()],
            returns: vec![return_ty],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
    let mut block = Block::new(b(0))
        .with_param(v(0), Ty::Ptr)
        .with_param(v(1), value_ty);
    block.body.push(InstrNode::new(Inst::CoroSuspend {
        frame: v(0),
        state_slot: 0,
        next_state: 1,
        value: v(1),
    }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn ws2_1_coro_suspend_positive_u64_yield_through_ptr_frame_validates() {
    let module = coro_suspend_module(Ty::Ptr, Ty::U64, vec![Ty::U64]);
    assert_eq!(validate_module(&module), Vec::new());
    assert_eq!(validate_function(&func_only(&module)), Vec::new());
}

/// Port of `b6.coro_suspend.yield_type_unchecked`.
#[test]
fn ws2_1_coro_suspend_yield_of_ptr_into_u64_is_return_type_mismatch() {
    let errs = validate_module(&coro_suspend_module(Ty::Ptr, Ty::Ptr, vec![Ty::U64]));
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        matches!(
            &errs[0],
            ValidationError::ReturnTypeMismatch { block: 0, expected, actual }
                if expected == "u64" && actual == "ptr"
        ),
        "{errs:?}"
    );
    assert!(
        errs[0].to_string().contains("return type mismatch"),
        "{}",
        errs[0]
    );
}

#[test]
fn ws2_1_coro_suspend_yield_into_unit_return_is_return_arity_mismatch() {
    let errs = validate_module(&coro_suspend_module(Ty::Ptr, Ty::U64, vec![]));
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        matches!(
            errs[0],
            ValidationError::ReturnArityMismatch {
                block: 0,
                expected: 0,
                actual: 1
            }
        ),
        "{errs:?}"
    );
}

/// The arity arm fires even though the single yielded `u64` MATCHES
/// `returns[0]` of the two-return signature — a zip-only implementation
/// (type check without the arity check) would pass this module clean.
#[test]
fn ws2_1_coro_suspend_one_yield_into_two_returns_is_return_arity_mismatch() {
    let errs = validate_module(&coro_suspend_module(
        Ty::Ptr,
        Ty::U64,
        vec![Ty::U64, Ty::U64],
    ));
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        matches!(
            errs[0],
            ValidationError::ReturnArityMismatch {
                block: 0,
                expected: 2,
                actual: 1
            }
        ),
        "{errs:?}"
    );
}

/// Port of `b6.coro_suspend.frame_operand_unchecked`. The frame rule is in the
/// per-function type pass, so standalone `validate_function` refuses it too.
#[test]
fn ws2_1_coro_suspend_u64_frame_is_operand_not_pointer() {
    let module = coro_suspend_module(Ty::U64, Ty::U64, vec![Ty::U64]);
    let not_pointer = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::OperandNotPointer { block: 0, op, ty }
                if op == "coro_suspend" && ty == "u64"
        )
    };
    let errs = validate_module(&module);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(not_pointer(&errs[0]), "{errs:?}");
    let standalone = validate_function(&func_only(&module));
    assert!(standalone.iter().any(not_pointer), "{standalone:?}");
}

/// Mutation control: the refine exemption `Return` has is kept. A
/// `Refine(u64, 0..=8)` yield into `-> u64` is the sound direction (the
/// resumer is promised a `u64` and gets one) and must still validate; an
/// implementation that dropped the exemption refuses it as
/// `ReturnTypeMismatch`.
#[test]
fn ws2_1_coro_suspend_refined_yield_into_plain_return_validates() {
    let module = refined_coro_suspend_module(Ty::U64, true, false, Ty::U64);
    assert_eq!(validate_module(&module), Vec::new());
}

/// Mutation controls for the refinement half. The exemption skips only RAW
/// equality; the pair is still decided at the `ReturnValues` consumption site
/// the suspend now shares with `Return`: an unrefined yield out of a refined
/// signature is `RefinementNotImplied`, and a refined yield whose BASE is not
/// the return type is a representation mismatch — so the exemption opens no
/// hole in either direction.
#[test]
fn ws2_1_coro_suspend_refinement_exemption_is_decided_by_the_refinement_layer() {
    let unrefined_out_of_refined = refined_coro_suspend_module(Ty::U64, false, true, Ty::U64);
    let errs = validate_module(&unrefined_out_of_refined);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        matches!(
            &errs[0],
            ValidationError::RefinementNotImplied { location, .. }
                if location.contains("coro_suspend yield 0")
        ),
        "{errs:?}"
    );

    let wrong_base = refined_coro_suspend_module(Ty::U32, true, false, Ty::U64);
    let errs = validate_module(&wrong_base);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            ValidationError::RefinementTypeInvalid { location, detail }
                if location.contains("coro_suspend yield 0") && detail.contains("representation")
        )),
        "{errs:?}"
    );
}

// ---------------------------------------------------------------------------
// shared single-function helpers used above
// ---------------------------------------------------------------------------

/// Build a single function (no surrounding module) with `params -> returns`.
fn single_fn_function(params: Vec<Ty>, returns: Vec<Ty>, block: Block) -> Function {
    let mut func = Function::new(FuncId::new(0), "f", FuncTyId::new(0), b(0));
    let _ = (params, returns); // signature unused for standalone validate_function
    func.blocks.push(block);
    func
}

/// Extract the (single) function from a module by clone for `validate_function`.
fn func_only(module: &Module) -> Function {
    module.functions[0].clone()
}

// ---------------------------------------------------------------------------
// #17 declared struct layouts: one coherence rule shared with the layout
//     authority (`Module::ty_layout_shape`), run with or without a pinned
//     target (roadmap WS2.3 / F-031; proof-program rows
//     `b6.union.overlapping_struct_fields_rejected` /
//     `b6.union.overlap_is_not_a_validation_error`, claim c07 t2/t4).
// ---------------------------------------------------------------------------

mod declared_struct_layouts {
    use trust_ir::ty::{FieldDef, StructDef, StructRepr};
    use trust_ir::value::StructId;
    use trust_ir::{Endianness, LayoutError, Module, TargetInfo, Ty};
    use trust_ir_build::validate::{STRUCT_LAYOUT_INCOHERENT_REASON, ValidationError};
    use trust_ir_build::{ModuleBuilder, validate_module};

    const FIELDS_OVERLAP: &str = "fields overlap";
    const OFFSET_OUTSIDE: &str = "field offset is outside the declared struct size";

    fn x86_64() -> TargetInfo {
        TargetInfo {
            triple: "x86_64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        }
    }

    fn at(name: &str, ty: Ty, offset: u64) -> FieldDef {
        FieldDef {
            name: name.into(),
            ty,
            offset: Some(offset),
        }
    }

    /// One `StructDef` #0 with a declared layout; `pin` adds an x86_64 target.
    fn layout(fields: Vec<FieldDef>, size: u64, align: u64, repr: StructRepr, pin: bool) -> Module {
        let mut m = Module::new("ws2_3");
        m.add_struct(StructDef {
            id: StructId::new(0),
            name: "S".into(),
            fields,
            size: Some(size),
            align: Some(align),
            repr,
            origin: None,
        });
        if pin {
            m.target_info = Some(x86_64());
        }
        m
    }

    /// `u8`, registered as type-table entry 0 (for `[u8; N]` fields).
    fn with_u8_table(mut m: Module) -> Module {
        m.types.push(Ty::U8);
        m
    }

    fn bytes(n: u64) -> Ty {
        Ty::Array(trust_ir::TyId::new(0), n)
    }

    fn inconsistent(reason: &'static str) -> ValidationError {
        ValidationError::StructLayoutInconsistent {
            struct_id: 0,
            reason,
        }
    }

    fn shape0(m: &Module) -> Result<trust_ir::TyLayoutShape, LayoutError> {
        m.ty_layout_shape(&Ty::Struct(StructId::new(0)))
    }

    /// Positive: `Pair { a: u32 @ 0, b: f32 @ 4 } size 8 align 4`, pinned AND
    /// target-free, validates with no error at all, and the layout authority
    /// agrees.
    #[test]
    fn coherent_pair_validates_pinned_and_target_free() {
        for pin in [true, false] {
            let m = layout(
                vec![at("a", Ty::U32, 0), at("b", Ty::F32, 4)],
                8,
                4,
                StructRepr::C,
                pin,
            );
            assert_eq!(validate_module(&m), vec![], "pin={pin}");
            assert!(shape0(&m).is_ok(), "pin={pin}");
        }
    }

    /// Negative twin (one mutation, `b.offset 4 -> 0`): `StructLayoutInconsistent
    /// { reason: "fields overlap" }` in BOTH the target-free and the pinned
    /// module — before WS2.3 both returned `[]` (c07 t2) while `shape` and the
    /// interpreter refused the same descriptor.
    #[test]
    fn overlapping_pair_is_refused_pinned_and_target_free() {
        for pin in [true, false] {
            let m = layout(
                vec![at("a", Ty::U32, 0), at("b", Ty::F32, 0)],
                8,
                4,
                StructRepr::C,
                pin,
            );
            let errors = validate_module(&m);
            assert_eq!(errors, vec![inconsistent(FIELDS_OVERLAP)], "pin={pin}");
            assert!(
                errors[0].to_string().contains(FIELDS_OVERLAP),
                "pin={pin}: the named reason reaches the message: {}",
                errors[0]
            );
            assert!(
                matches!(shape0(&m), Err(LayoutError::StructLayoutIncoherent(id)) if id == StructId::new(0)),
                "pin={pin}: the validator and the layout authority agree"
            );
        }
    }

    /// Target-free `offset 12 > size 8` is now caught; before WS2.3 only the
    /// pinned variant was (c07 t4).
    #[test]
    fn target_free_offset_past_size_is_refused() {
        for pin in [true, false] {
            let m = layout(
                vec![at("a", Ty::U32, 0), at("b", Ty::F32, 12)],
                8,
                4,
                StructRepr::C,
                pin,
            );
            assert_eq!(
                validate_module(&m),
                vec![inconsistent(OFFSET_OUTSIDE)],
                "pin={pin}"
            );
        }
    }

    /// The shared-authority half: a defect only `ty_layout_shape` names (a
    /// field whose EXTENT runs past `size` from an in-range offset; a
    /// `repr(transparent)` wrapper larger than its carrier) is refused with
    /// the generic incoherence reason, pinned and target-free. Each has a
    /// one-mutation control that validates.
    #[test]
    fn layout_authority_refusals_become_validation_errors() {
        for pin in [true, false] {
            // `[u8; 8] @ 4` in a size-8 struct ends at byte 12.
            let overrun = with_u8_table(layout(
                vec![at("a", Ty::U32, 0), at("tail", bytes(8), 4)],
                8,
                4,
                StructRepr::C,
                pin,
            ));
            let errors = validate_module(&overrun);
            assert_eq!(
                errors,
                vec![inconsistent(STRUCT_LAYOUT_INCOHERENT_REASON)],
                "pin={pin}"
            );
            assert!(
                errors[0]
                    .to_string()
                    .contains("declared layout is incoherent")
            );
            let fits = with_u8_table(layout(
                vec![at("a", Ty::U32, 0), at("tail", bytes(4), 4)],
                8,
                4,
                StructRepr::C,
                pin,
            ));
            assert_eq!(validate_module(&fits), vec![], "pin={pin}");

            // `repr(transparent)` must be exactly its carrier: size 8 over a u32.
            let transparent = layout(
                vec![at("inner", Ty::U32, 0)],
                8,
                4,
                StructRepr::Transparent,
                pin,
            );
            assert_eq!(
                validate_module(&transparent),
                vec![inconsistent(STRUCT_LAYOUT_INCOHERENT_REASON)],
                "pin={pin}"
            );
            let exact = layout(
                vec![at("inner", Ty::U32, 0)],
                4,
                4,
                StructRepr::Transparent,
                pin,
            );
            assert_eq!(validate_module(&exact), vec![], "pin={pin}");
        }
    }

    /// Mutation control: a trailing ZST at `offset == size` must validate — it
    /// catches a naive `offset + size > size` rule — and so must a ZST sharing
    /// an offset with a real field (zero-sized fields never overlap).
    #[test]
    fn zero_sized_fields_at_size_or_shared_offsets_validate() {
        for pin in [true, false] {
            let m = layout(
                vec![
                    at("marker", Ty::Unit, 0),
                    at("a", Ty::U32, 0),
                    at("tail", Ty::Unit, 4),
                ],
                4,
                4,
                StructRepr::C,
                pin,
            );
            assert_eq!(validate_module(&m), vec![], "pin={pin}");
            assert!(shape0(&m).is_ok(), "pin={pin}");
        }
    }

    /// Mutation control: the ratified G18-3 union model — a `repr(C)` struct
    /// holding an untyped `[u8; 8]` carrier at 8 in a size-16/align-8 struct —
    /// must validate, and a pun through the carrier must execute. This catches
    /// an over-eager rule that would refuse the model the overlap rule points
    /// producers to (`union_byte_overlap_model.rs` is the standing proof).
    #[test]
    fn ratified_union_byte_carrier_still_validates_and_runs() {
        use trust_ir::Constant;
        use trust_ir::interpret::{InterpretValueKind, Interpreter};
        for pin in [true, false] {
            let mut mb = if pin {
                ModuleBuilder::new_with_target_info("union_carrier", x86_64())
            } else {
                ModuleBuilder::new("union_carrier")
            };
            let u8_ty = mb.add_type(Ty::U8);
            let holder = Ty::Struct(StructId::new(0));
            mb.add_struct(StructDef {
                id: StructId::new(0),
                name: "Holder".into(),
                fields: vec![at("tag", Ty::U64, 0), at("u", Ty::Array(u8_ty, 8), 8)],
                size: Some(16),
                align: Some(8),
                repr: StructRepr::C,
                origin: None,
            });
            let sig = mb.add_func_type(vec![], vec![Ty::F64]);
            let mut fb = mb.function("pun", sig);
            fb.set_producer(trust_ir::Producer::TRust);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let p = fb.alloca_aligned(holder, 8);
            let slot = fb.gep_byte_offset(p, 8);
            let bits = fb.const_value(Ty::U64, Constant::Int(0x3FF0_0000_0000_0000));
            fb.store(Ty::U64, slot, bits);
            let as_f64 = fb.load(Ty::F64, slot);
            fb.ret(vec![as_f64]);
            fb.build();
            let m = mb.build().expect("ModuleBuilder::build: test fixture");
            assert_eq!(validate_module(&m), vec![], "pin={pin}");
            let func = m.function_by_name("pun").expect("pun");
            let out = Interpreter::with_module(&m)
                .execute_func(func.id, Vec::new())
                .expect("the byte-carrier pun executes");
            let InterpretValueKind::FloatBits(bits) = out.returns[0].kind else {
                panic!("pin={pin}: expected an f64, got {:?}", out.returns[0]);
            };
            assert_eq!(f64::from_bits(bits), 1.0, "pin={pin}");
        }
    }

    /// Boundary control on the predicate: `[0,4)` and `[4,8)` touch and
    /// validate; shifting the second back one byte to `[3,7)` shares byte 3.
    /// Declared ORDER is not a rule: a `repr(Rust)` reordering validates and a
    /// straddle between non-adjacent declarations is still found.
    #[test]
    fn overlap_predicate_boundaries_and_reordering() {
        for pin in [true, false] {
            let touching = with_u8_table(layout(
                vec![at("a", bytes(4), 0), at("b", bytes(4), 4)],
                8,
                1,
                StructRepr::C,
                pin,
            ));
            assert_eq!(validate_module(&touching), vec![], "pin={pin}");
            let shared = with_u8_table(layout(
                vec![at("a", bytes(4), 0), at("b", bytes(4), 3)],
                8,
                1,
                StructRepr::C,
                pin,
            ));
            assert_eq!(
                validate_module(&shared),
                vec![inconsistent(FIELDS_OVERLAP)],
                "pin={pin}"
            );

            let reordered = layout(
                vec![
                    at("a", Ty::U64, 8),
                    at("b", Ty::U32, 0),
                    at("c", Ty::U32, 4),
                ],
                16,
                8,
                StructRepr::Rust,
                pin,
            );
            assert_eq!(validate_module(&reordered), vec![], "pin={pin}");
            let straddle = with_u8_table(layout(
                vec![
                    at("a", Ty::U64, 8),
                    at("b", Ty::U32, 0),
                    at("c", bytes(4), 6),
                ],
                16,
                8,
                StructRepr::Rust,
                pin,
            ));
            assert_eq!(
                validate_module(&straddle),
                vec![inconsistent(FIELDS_OVERLAP)],
                "pin={pin}"
            );
        }
    }

    /// One struct gets one error: overlap AND containment is reported once,
    /// an earlier precise rule (align 3) suppresses both the overlap rule and
    /// the generic shape report, and an incoherent NESTED struct is reported
    /// on itself only — never again on the struct that contains it.
    #[test]
    fn one_struct_one_error() {
        for pin in [true, false] {
            let both = layout(
                vec![
                    at("a", Ty::U64, 0),
                    at("b", Ty::U64, 0),
                    at("c", Ty::U64, 0),
                ],
                8,
                8,
                StructRepr::C,
                pin,
            );
            assert_eq!(
                validate_module(&both),
                vec![inconsistent(FIELDS_OVERLAP)],
                "pin={pin}"
            );

            let bad_align = layout(
                vec![at("a", Ty::U8, 0), at("b", Ty::U8, 0)],
                3,
                3,
                StructRepr::C,
                pin,
            );
            assert_eq!(
                validate_module(&bad_align),
                vec![inconsistent("align must be a non-zero power of two")],
                "pin={pin}"
            );

            let mut nested = layout(
                vec![at("inner", Ty::Struct(StructId::new(1)), 0)],
                8,
                4,
                StructRepr::C,
                pin,
            );
            nested.add_struct(StructDef {
                id: StructId::new(1),
                name: "Inner".into(),
                fields: vec![at("lo", Ty::U32, 0), at("hi", Ty::U32, 0)],
                size: Some(8),
                align: Some(4),
                repr: StructRepr::C,
                origin: None,
            });
            assert_eq!(
                validate_module(&nested),
                vec![ValidationError::StructLayoutInconsistent {
                    struct_id: 1,
                    reason: FIELDS_OVERLAP,
                }],
                "pin={pin}"
            );
        }
    }

    /// Item-1 skip, as a control: a PARTIALLY-declared layout (one sized field
    /// without an offset) is refused by `shape` as `MissingFieldOffset` but
    /// is NOT a validation error in this increment — pinned or target-free.
    #[test]
    fn partial_offsets_are_not_refused_by_the_validator() {
        for pin in [true, false] {
            let mut m = layout(
                vec![at("a", Ty::U32, 0), at("b", Ty::U32, 4)],
                8,
                4,
                StructRepr::C,
                pin,
            );
            m.structs[0].fields[1].offset = None;
            assert!(
                matches!(shape0(&m), Err(LayoutError::MissingFieldOffset { .. })),
                "pin={pin}: {:?}",
                shape0(&m)
            );
            assert_eq!(validate_module(&m), vec![], "pin={pin}");
        }
    }

    /// The only target-dependent clause stays target-dependent and is
    /// reported once: under i686 (outside the canonical scalar table) the
    /// descriptor draws exactly one `TargetScalarLayoutUnavailable`; the SAME
    /// descriptor target-free is judged against the canonical reference layout
    /// — where `f64 @ 4` is misaligned — exactly as `shape` judges it.
    #[test]
    fn target_scalar_layout_unavailable_is_pinned_only_and_reported_once() {
        let mut m = layout(
            vec![at("tag", Ty::U8, 0), at("value", Ty::F64, 4)],
            12,
            4,
            StructRepr::C,
            false,
        );
        m.target_info = Some(TargetInfo {
            triple: "i686-unknown-linux-gnu".into(),
            pointer_size: 4,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        });
        assert_eq!(
            validate_module(&m),
            vec![ValidationError::TargetScalarLayoutUnavailable {
                struct_id: 0,
                triple: "i686-unknown-linux-gnu".into(),
            }]
        );
        m.target_info = None;
        assert_eq!(
            validate_module(&m),
            vec![inconsistent(
                "field offset is not a multiple of the field's effective alignment"
            )]
        );
        assert!(matches!(
            shape0(&m),
            Err(LayoutError::StructLayoutIncoherent(_))
        ));
    }

    /// Ported ratchet (`b6.union.overlap_is_not_a_validation_error`, GAP ->
    /// PASS): the proof program's target-pinned `Pair { a: u8, b: u64 }` size
    /// 16 align 8 with a `struct_image` body. Baseline `(a @ 8, b @ 0)` lays
    /// out, runs and validates; the struct-spelled union `(a @ 0, b @ 0)` is
    /// refused by the layout authority, the interpreter, AND now every
    /// validator entry point — `validate_module`, `validate_changed`,
    /// `validate_linked_module`, and `validate_module_for_codegen` with every
    /// body licensed.
    #[test]
    fn struct_spelled_union_is_refused_by_every_authority() {
        use trust_ir::interpret::Interpreter;
        use trust_ir::{BodyGate, Constant};

        fn pair_module(a_offset: u64, b_offset: u64) -> Module {
            let mut mb = ModuleBuilder::new_with_target_info("b6_layouts", x86_64());
            let pair = Ty::Struct(StructId::new(0));
            mb.add_struct(StructDef {
                id: StructId::new(0),
                name: "Pair".into(),
                fields: vec![at("a", Ty::U8, a_offset), at("b", Ty::U64, b_offset)],
                size: Some(16),
                align: Some(8),
                repr: StructRepr::default(),
                origin: None,
            });
            let n64 = mb.add_func_type(vec![], vec![Ty::U64]);
            let mut fb = mb.function("struct_image", n64);
            fb.set_producer(trust_ir::Producer::TRust);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let p = fb.alloca(pair.clone());
            let c = fb.const_value(
                pair.clone(),
                Constant::Aggregate(vec![
                    Constant::Int(17),
                    Constant::Int(0x1122_3344_5566_7788),
                ]),
            );
            fb.store(pair, p, c);
            let raw = fb.load(Ty::U64, p);
            fb.ret(vec![raw]);
            fb.build();
            mb.build().expect("ModuleBuilder::build: test fixture")
        }
        fn run(m: &Module) -> Result<u64, String> {
            let func = m.function_by_name("struct_image").expect("struct_image");
            Interpreter::with_module(m)
                .execute_func(func.id, Vec::new())
                .map(|outcome| outcome.returns[0].as_int().unwrap().as_unsigned() as u64)
                .map_err(|e| format!("{:?}: {e}", e.code))
        }
        fn licensed(m: &Module) -> Module {
            let mut m = m.clone();
            for f in &mut m.functions {
                f.body_gate = Some(BodyGate::Gated {
                    authority: "trust-verify".into(),
                    evidence: None,
                });
            }
            m
        }

        let base = pair_module(8, 0);
        assert!(shape0(&base).is_ok());
        assert_eq!(run(&base), Ok(0x1122_3344_5566_7788));
        assert_eq!(validate_module(&base), vec![]);
        assert_eq!(
            trust_ir_build::validate_module_for_codegen(&licensed(&base)),
            vec![]
        );

        let union_ = pair_module(0, 0);
        assert!(matches!(
            shape0(&union_),
            Err(LayoutError::StructLayoutIncoherent(id)) if id == StructId::new(0)
        ));
        let ran = run(&union_);
        assert!(
            matches!(&ran, Err(e) if e.starts_with("TypeError") && e.contains("overlapping fields 0 and 1")),
            "{ran:?}"
        );
        let overlap = inconsistent(FIELDS_OVERLAP);
        assert_eq!(validate_module(&union_), vec![overlap.clone()]);
        assert_eq!(
            trust_ir_build::validate_changed(&union_, &[]),
            vec![overlap.clone()],
            "an edit list naming no function still re-checks struct layouts"
        );
        let empty = trust_ir_build::ModuleSet::new([]);
        let linked = trust_ir_build::validate_linked_module(
            &union_,
            &empty,
            &trust_ir::proof::RejectingModuleProofAuthority,
        );
        assert!(linked.errors().contains(&overlap), "{:?}", linked.errors());
        let codegen = trust_ir_build::validate_module_for_codegen(&licensed(&union_));
        assert!(codegen.contains(&overlap), "{codegen:?}");
    }
}
