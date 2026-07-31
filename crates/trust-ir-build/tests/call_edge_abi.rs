// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ABI pinning — call-edge cross-checks (abi-pinning.md enforcement layer).
//
// Where a `CallIndirect`'s function pointer has statically-visible provenance
// (a `Const FnDef` chased through `Copy`/`ReifyFnPointer`), the validator
// cross-checks the edge's DECLARED calling convention and signature against
// the callee-side DECLARATION. The signature check is the roadmap's golden
// rejection: a Rust caller and a C callee that disagree on how a struct is
// passed at the call edge (by value vs through a byval/sret pointer) are
// rejected. byval/sret placement coherence is covered at the bottom.

use trust_ir::inst::{CastOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FieldDef, FuncTy, StructDef, StructRepr, Ty};
use trust_ir::value::{BlockId, FuncId, StructId, ValueId};
use trust_ir::{
    Block, CallingConv, Constant, Endianness, Function, Module, ParamAttrs, StructPassingPolicy,
    TargetInfo,
};
use trust_ir_build::{ValidationError, validate_module};

fn pinned_target() -> TargetInfo {
    TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("sysv64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn has<F: Fn(&ValidationError) -> bool>(m: &Module, pred: F) -> bool {
    validate_module(m).iter().any(pred)
}

/// The roadmap's golden module, parameterized on the caller's view.
///
/// Callee `c_take_pair` (C side): a bodyless `external` ccc declaration whose
/// signature passes the repr(C) struct THROUGH MEMORY — `(Ptr) -> ()` with
/// `byval` on the pointer parameter (v20 ParamAttrs).
///
/// Caller `rust_caller` (Rust side): reifies a pointer to the callee and
/// calls it indirectly with `calling_conv: C`. When `caller_by_value` is
/// true, the caller's declared edge signature passes the struct BY VALUE
/// (`(BigPair) -> ()`) — the two sides disagree on how BigPair crosses the
/// edge. When false, the caller declares the callee's real memory-passing
/// signature and the edge agrees.
fn rust_to_c_module(caller_by_value: bool) -> Module {
    let mut m = Module::new("rust_to_c");
    m.target_info = Some(pinned_target());

    let s = StructId::new(0);
    m.add_struct(StructDef {
        id: s,
        name: "BigPair".into(),
        fields: vec![
            FieldDef {
                name: "lo".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "hi".into(),
                ty: Ty::U64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
    });

    // functy.0 — the callee's true signature: BigPair through memory.
    let callee_sig = m.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    });
    // functy.1 — the by-value view: BigPair in registers.
    let by_value_sig = m.add_func_type(FuncTy {
        params: vec![Ty::Struct(s)],
        returns: vec![],
        is_vararg: false,
    });
    // functy.2 — the caller's own signature.
    let caller_ty = m.add_func_type(FuncTy {
        params: vec![Ty::Struct(s), Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    });

    // C-side import declaration: bodyless external, ccc, byval memory copy.
    let mut callee = Function::new(FuncId::new(0), "c_take_pair", callee_sig, BlockId::new(0));
    callee.calling_conv = CallingConv::C;
    callee.attrs.params = vec![ParamAttrs {
        byval: true,
        dereferenceable: Some(16),
        align: Some(8),
        ..Default::default()
    }];
    m.add_function(callee);

    // Rust-side caller.
    let edge_sig = if caller_by_value {
        by_value_sig
    } else {
        callee_sig
    };
    let mut caller = Function::new(FuncId::new(1), "rust_caller", caller_ty, BlockId::new(0));
    caller.calling_conv = CallingConv::Rust;
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Struct(s))); // the pair, by value
    block.params.push((ValueId::new(1), Ty::Ptr)); // the pair, spilled
    // v2 = const FnDef(c_take_pair), then reify + copy so the provenance
    // check exercises the whole chase chain.
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Func(edge_sig),
            value: Constant::FnDef(FuncId::new(0)),
        })
        .with_result(ValueId::new(2)),
    );
    block.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ReifyFnPointer,
            src_ty: Ty::Func(edge_sig),
            dst_ty: Ty::Func(edge_sig),
            operand: ValueId::new(2),
        })
        .with_result(ValueId::new(3)),
    );
    block.body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::Func(edge_sig),
            operand: ValueId::new(3),
        })
        .with_result(ValueId::new(4)),
    );
    let arg = if caller_by_value {
        ValueId::new(0)
    } else {
        ValueId::new(1)
    };
    block.body.push(InstrNode::new(Inst::CallIndirect {
        callee: ValueId::new(4),
        sig: edge_sig,
        args: vec![arg],
        calling_conv: CallingConv::C,
    }));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    caller.blocks.push(block);
    m.add_function(caller);

    m
}

// --------------------------------------------------------------------------
// The golden rejection (abi-pinning.md acceptance criterion): caller and
// callee disagree on how BigPair is passed at the call edge.
// --------------------------------------------------------------------------

#[test]
fn golden_rust_to_c_struct_passing_disagreement_rejected() {
    let m = rust_to_c_module(true);
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::CallEdgeSignatureMismatch { callee, .. } if callee == "c_take_pair"
        )),
        "a by-value vs byval struct-passing disagreement at a Rust->C call edge \
         must be rejected: {errors:?}"
    );
}

#[test]
fn golden_rust_to_c_agreeing_struct_passing_accepted() {
    // Same module, but the caller declares the callee's true memory-passing
    // signature: the edge agrees and no CallEdge* error fires.
    let m = rust_to_c_module(false);
    let errors = validate_module(&m);
    assert!(
        !errors.iter().any(|e| matches!(
            e,
            ValidationError::CallEdgeSignatureMismatch { .. }
                | ValidationError::CallEdgeConvMismatch { .. }
        )),
        "an agreeing Rust->C call edge must validate: {errors:?}"
    );
}

// --------------------------------------------------------------------------
// Calling-convention cross-check.
// --------------------------------------------------------------------------

/// A caller that resolves `callee_conv`-declared `target_fn` via FnDef and
/// calls it indirectly declaring `edge_conv`.
fn conv_module(edge_conv: CallingConv, callee_conv: CallingConv) -> Module {
    let mut m = Module::new("conv_edge");
    m.target_info = Some(pinned_target());
    let sig = m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });

    let mut callee = Function::new(FuncId::new(0), "target_fn", sig, BlockId::new(0));
    callee.calling_conv = callee_conv;
    let mut cb = Block::new(BlockId::new(0));
    cb.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    callee.blocks.push(cb);
    m.add_function(callee);

    let mut caller = Function::new(FuncId::new(1), "caller", sig, BlockId::new(0));
    caller.calling_conv = edge_conv; // enclosing conv == edge conv: no FFI boundary from the edge itself
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Func(sig),
            value: Constant::FnDef(FuncId::new(0)),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::CallIndirect {
        callee: ValueId::new(0),
        sig,
        args: vec![],
        calling_conv: edge_conv,
    }));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    caller.blocks.push(block);
    m.add_function(caller);
    m
}

#[test]
fn call_edge_conv_mismatch_rejected() {
    let m = conv_module(CallingConv::Rust, CallingConv::C);
    assert!(
        has(&m, |e| matches!(
            e,
            ValidationError::CallEdgeConvMismatch { callee, .. } if callee == "target_fn"
        )),
        "an indirect call declaring rustcc resolved to a ccc callee must be rejected: {:?}",
        validate_module(&m)
    );
}

#[test]
fn call_edge_conv_agreement_accepted() {
    let m = conv_module(CallingConv::C, CallingConv::C);
    assert!(!has(&m, |e| matches!(
        e,
        ValidationError::CallEdgeConvMismatch { .. }
    )));
}

#[test]
fn call_edge_with_dynamic_provenance_is_not_checkable() {
    // The documented not-checkable subset: a function pointer arriving as a
    // block parameter has no static provenance, so the edge is trusted as
    // declared (no CallEdge* error even though no callee matches).
    let mut m = Module::new("dynamic_edge");
    m.target_info = Some(pinned_target());
    let sig = m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let caller_ty = m.add_func_type(FuncTy {
        params: vec![Ty::Func(sig)],
        returns: vec![],
        is_vararg: false,
    });
    let mut caller = Function::new(FuncId::new(0), "caller", caller_ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Func(sig)));
    block.body.push(InstrNode::new(Inst::CallIndirect {
        callee: ValueId::new(0),
        sig,
        args: vec![],
        calling_conv: CallingConv::C,
    }));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    caller.blocks.push(block);
    m.add_function(caller);

    assert!(!has(&m, |e| matches!(
        e,
        ValidationError::CallEdgeConvMismatch { .. }
            | ValidationError::CallEdgeSignatureMismatch { .. }
    )));
}

// --------------------------------------------------------------------------
// byval/sret placement coherence (validate_param_abi_attrs).
// --------------------------------------------------------------------------

/// One function with the given signature and param attrs, target pinned.
fn attr_module(params: Vec<Ty>, returns: Vec<Ty>, attrs: Vec<ParamAttrs>) -> Module {
    let mut m = Module::new("attr_abi");
    m.target_info = Some(pinned_target());
    let ft = m.add_func_type(FuncTy {
        params: params.clone(),
        returns,
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    func.attrs.params = attrs;
    let mut block = Block::new(BlockId::new(0));
    for (i, ty) in params.iter().enumerate() {
        block.params.push((ValueId::new(i as u32), ty.clone()));
    }
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(block);
    m.add_function(func);
    m
}

fn byval() -> ParamAttrs {
    ParamAttrs {
        byval: true,
        ..Default::default()
    }
}

fn sret() -> ParamAttrs {
    ParamAttrs {
        sret: true,
        ..Default::default()
    }
}

#[test]
fn byval_and_sret_on_pointer_params_accepted() {
    let m = attr_module(vec![Ty::Ptr, Ty::Ptr], vec![], vec![sret(), byval()]);
    assert!(
        !has(&m, |e| matches!(
            e,
            ValidationError::ParamAbiAttrInvalid { .. }
        )),
        "well-placed byval/sret must validate: {:?}",
        validate_module(&m)
    );
}

#[test]
fn byval_on_non_pointer_param_rejected() {
    let m = attr_module(vec![Ty::I32], vec![], vec![byval()]);
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::ParamAbiAttrInvalid {
            param_index: 0,
            reason: "byval/sret require a pointer-typed parameter",
            ..
        }
    )));
}

#[test]
fn byval_plus_sret_on_one_param_rejected() {
    let m = attr_module(
        vec![Ty::Ptr],
        vec![],
        vec![ParamAttrs {
            byval: true,
            sret: true,
            ..Default::default()
        }],
    );
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::ParamAbiAttrInvalid {
            reason: "byval and sret are mutually exclusive on one parameter",
            ..
        }
    )));
}

#[test]
fn two_sret_params_rejected() {
    let m = attr_module(vec![Ty::Ptr, Ty::Ptr], vec![], vec![sret(), sret()]);
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::ParamAbiAttrInvalid {
            param_index: 1,
            reason: "at most one parameter may be sret",
            ..
        }
    )));
}

#[test]
fn sret_with_nonempty_returns_rejected() {
    let m = attr_module(vec![Ty::Ptr], vec![Ty::I32], vec![sret()]);
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::ParamAbiAttrInvalid {
            reason: "sret marks the return slot, so the signature must return no values",
            ..
        }
    )));
}

#[test]
fn byval_past_signature_params_rejected() {
    let m = attr_module(vec![Ty::Ptr], vec![], vec![ParamAttrs::default(), byval()]);
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::ParamAbiAttrInvalid {
            param_index: 1,
            reason: "attribute is positioned past the signature's parameters",
            ..
        }
    )));
}
