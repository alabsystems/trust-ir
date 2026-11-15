// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact typed reflection of real producer casts; execution is a separate gate.

use super::*;
use crate::ModuleBuilder;
use trust_ir::{CastOp, Endianness, StructPassingPolicy, TargetInfo};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn cast_module(op: CastOp, src: Ty, dst: Ty) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info("typed_cast", target());
    let signature = builder.add_func_type(vec![src.clone(), src.clone()], vec![dst.clone()]);
    let function = builder.declare_function("convert", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let _unused = body.add_block_param(block, src.clone());
    let operand = body.add_block_param(block, src.clone());
    body.switch_to_block(block);
    body.uconst(Ty::U64, 93);
    let converted = body.cast(op, src, dst, operand);
    body.ret(vec![converted]);
    body.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

fn elements(term: &Expr) -> Vec<&Expr> {
    let mut cursor = term;
    let mut elements = Vec::new();
    while *cursor.get_app_fn() == c("IRList.cons") {
        let fields = cursor.get_app_args();
        assert_eq!(fields.len(), 3);
        elements.push(fields[1]);
        cursor = fields[2];
    }
    assert_eq!(*cursor.get_app_fn(), c("IRList.nil"));
    elements
}

fn check_cast(module: &Module, op: &str, src: Expr, dst: Expr) -> Expr {
    assert!(
        crate::validate_module(module).is_empty(),
        "valid producer cast"
    );
    let function = &module.functions[0];
    let block = &function.blocks[0];
    let Inst::Cast { operand, .. } = &block.body[1].inst else {
        panic!("actual cast at nonzero PC");
    };
    let result = &block.body[1].results[0];
    let reflected = reflect_core_module_v1(module, &[(function.id, 4096)]).unwrap();
    let context = reflected.context_term();
    let context_fields = context.get_app_args();
    let module_fields = context_fields[0].get_app_args();
    let functions = elements(module_fields[0]);
    let blocks = elements(functions[0].get_app_args()[3]);
    let nodes = elements(blocks[0].get_app_args()[2]);
    assert_eq!(
        *nodes[1],
        app(
            "IRNode.mk",
            [
                app(
                    "IRInst.cast",
                    [c(op), src, dst.clone(), nat(u64::from(operand.index()))],
                ),
                list("Nat", [nat(u64::from(result.index()))]),
            ],
        )
    );
    let sites = elements(context_fields[4]);
    let site = sites[1].get_app_args();
    assert_eq!(*site[0], nat(u64::from(function.id.index())));
    assert_eq!(*site[1], nat(u64::from(block.id.index())));
    assert_eq!(*site[2], nat(1));
    assert_eq!(*site[5], list("IRTy", [dst]));
    context.clone()
}

#[test]
fn actual_cast_module_retains_opcode_types_operand_result_and_nonzero_site() {
    for (op, src, dst, name, src_expr, dst_expr) in [
        (
            CastOp::Trunc,
            Ty::I64,
            Ty::U8,
            "trunc",
            app("IRTy.int_", [nat(64)]),
            app("IRTy.uint_", [nat(8)]),
        ),
        (
            CastOp::Trunc,
            Ty::U8,
            Ty::Bool,
            "trunc",
            app("IRTy.uint_", [nat(8)]),
            c("IRTy.bool_"),
        ),
        (
            CastOp::ZExt,
            Ty::Bool,
            Ty::U64,
            "zext",
            c("IRTy.bool_"),
            app("IRTy.uint_", [nat(64)]),
        ),
        (
            CastOp::SExt,
            Ty::I8,
            Ty::I64,
            "sext",
            app("IRTy.int_", [nat(8)]),
            app("IRTy.int_", [nat(64)]),
        ),
        (
            CastOp::Bitcast,
            Ty::I64,
            Ty::U64,
            "bitcast",
            app("IRTy.int_", [nat(64)]),
            app("IRTy.uint_", [nat(64)]),
        ),
        (
            CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            "inttoptr",
            app("IRTy.int_", [nat(64)]),
            c("IRTy.ptr_"),
        ),
        (
            CastOp::PtrToInt,
            Ty::Ptr,
            Ty::U64,
            "ptrtoint",
            c("IRTy.ptr_"),
            app("IRTy.uint_", [nat(64)]),
        ),
        (
            CastOp::PtrToPtr,
            Ty::Ptr,
            Ty::Ptr,
            "ptrtoptr",
            c("IRTy.ptr_"),
            c("IRTy.ptr_"),
        ),
    ] {
        let _ = check_cast(
            &cast_module(op, src, dst),
            &format!("IRCastOp.{name}"),
            src_expr,
            dst_expr,
        );
    }
}

#[test]
fn pointer_width_reflection_does_not_claim_the_byte_evaluator_supports_it() {
    // Static validity and exact reflection are not an execution witness. The
    // byte model deliberately refuses these non-64-bit pointer conversions.
    for (op, src, dst, name, src_expr, dst_expr) in [
        (
            CastOp::IntToPtr,
            Ty::U32,
            Ty::Ptr,
            "inttoptr",
            app("IRTy.uint_", [nat(32)]),
            c("IRTy.ptr_"),
        ),
        (
            CastOp::PtrToInt,
            Ty::Ptr,
            Ty::U128,
            "ptrtoint",
            c("IRTy.ptr_"),
            app("IRTy.uint_", [nat(128)]),
        ),
    ] {
        let _ = check_cast(
            &cast_module(op, src, dst),
            &format!("IRCastOp.{name}"),
            src_expr,
            dst_expr,
        );
    }
}

#[test]
fn actual_cast_operand_source_and_result_type_tampering_fails_validation() {
    let module = cast_module(CastOp::IntToPtr, Ty::I64, Ty::Ptr);
    for kind in 0..3 {
        let mut changed = module.clone();
        let node = &mut changed.functions[0].blocks[0].body[1];
        let Inst::Cast {
            src_ty,
            dst_ty,
            operand,
            ..
        } = &mut node.inst
        else {
            unreachable!();
        };
        match kind {
            0 => *src_ty = Ty::U32,
            1 => *dst_ty = Ty::U64,
            _ => *operand = trust_ir::ValueId::new(9876),
        }
        assert!(!crate::validate_module(&changed).is_empty());
        assert!(reflect_core_module_v1(&changed, &[(FuncId::new(0), 4096)]).is_err());
    }
}

#[test]
fn cast_reflection_retains_existing_float_refusals() {
    for module in [
        cast_module(CastOp::FPToUI, Ty::F64, Ty::U64),
        cast_module(CastOp::UIToFP, Ty::U64, Ty::F64),
    ] {
        assert!(crate::validate_module(&module).is_empty());
        let error = reflect_core_module_v1(&module, &[(FuncId::new(0), 4096)]).unwrap_err();
        assert!(
            error.to_string().contains("unsupported byte-profile type"),
            "{error}"
        );
    }
}
