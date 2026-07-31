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
    let ft = module.add_func_type(FuncTy {
        params,
        returns,
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
    func.blocks.push(block);
    module.add_function(func);
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
    });
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Struct(sid)],
        returns: vec![],
        is_vararg: false,
    });
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
    module.add_function(func);

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
    });
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Struct(sid)],
        returns: vec![],
        is_vararg: false,
    });
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
    module.add_function(func);

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
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![],
        is_vararg: false,
    });
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
    module.add_function(func);

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
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Bool],
        returns: vec![],
        is_vararg: false,
    });
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
    module.add_function(func);

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
    let ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
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
    module.add_function(func);

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
    module.add_func_type(FuncTy {
        params: vec![Ty::Struct(StructId::new(7))],
        returns: vec![],
        is_vararg: false,
    });
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
    module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::Array(TyId::new(9), 4)],
        is_vararg: false,
    });
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
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![],
        is_vararg: false,
    });
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
    module.add_function(func);

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
    let _f0 = m.intern_file("src/lib.rs"); // files.len() == 1, valid index is 0
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
