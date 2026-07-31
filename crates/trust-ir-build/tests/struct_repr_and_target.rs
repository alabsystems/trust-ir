// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Validation coverage for StructDef.repr (ABI classification) and TargetInfo
// consistency — the ABI-pinning audit fitness gaps. (Binary/text/serde
// round-trips for repr live in the trust-ir crate's own tests.)

use trust_ir::ty::{FieldDef, FuncTy, StructDef, StructRepr};
use trust_ir::value::{BlockId, FuncId, FuncTyId, StructId};
use trust_ir::{Endianness, Function, Linkage, Module, TargetInfo, Ty};
use trust_ir_build::{ValidationError, validate_module};

fn field(name: &str, ty: Ty) -> FieldDef {
    FieldDef {
        name: name.into(),
        ty,
        offset: None,
    }
}

fn module_with_struct(fields: Vec<FieldDef>, repr: StructRepr) -> Module {
    let mut m = Module::new("repr");
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields,
        size: None,
        align: None,
        repr,
    });
    m
}

fn has<F: Fn(&ValidationError) -> bool>(m: &Module, pred: F) -> bool {
    validate_module(m).iter().any(pred)
}

#[test]
fn transparent_with_one_non_zst_field_ok() {
    let m = module_with_struct(vec![field("inner", Ty::I64)], StructRepr::Transparent);
    assert!(!has(&m, |e| matches!(
        e,
        ValidationError::TransparentReprFieldCount { .. }
    )));
}

#[test]
fn transparent_with_zst_companions_ok() {
    // One real field plus zero-size fields is still a valid transparent wrapper.
    let m = module_with_struct(
        vec![
            field("inner", Ty::I64),
            field("marker", Ty::Unit),
            field("u", Ty::Tuple(vec![])),
        ],
        StructRepr::Transparent,
    );
    assert!(!has(&m, |e| matches!(
        e,
        ValidationError::TransparentReprFieldCount { .. }
    )));
}

#[test]
fn transparent_with_two_non_zst_fields_rejected() {
    let m = module_with_struct(
        vec![field("a", Ty::I32), field("b", Ty::I32)],
        StructRepr::Transparent,
    );
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::TransparentReprFieldCount {
            actual_non_zst: 2,
            ..
        }
    )));
}

#[test]
fn transparent_with_zero_non_zst_fields_rejected() {
    let m = module_with_struct(vec![field("z", Ty::Unit)], StructRepr::Transparent);
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::TransparentReprFieldCount {
            actual_non_zst: 0,
            ..
        }
    )));
}

#[test]
fn packed_power_of_two_ok() {
    for align in [1u32, 2, 4, 8, 16] {
        let m = module_with_struct(vec![field("a", Ty::I32)], StructRepr::Packed(align));
        assert!(
            !has(&m, |e| matches!(
                e,
                ValidationError::PackedReprInvalidAlign { .. }
            )),
            "packed({align}) should be valid"
        );
    }
}

#[test]
fn packed_non_power_of_two_and_zero_rejected() {
    for align in [0u32, 3, 6, 12] {
        let m = module_with_struct(vec![field("a", Ty::I32)], StructRepr::Packed(align));
        assert!(
            has(&m, |e| matches!(
                e,
                ValidationError::PackedReprInvalidAlign { .. }
            )),
            "packed({align}) should be rejected"
        );
    }
}

#[test]
fn target_info_valid_ok() {
    let mut m = Module::new("t");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let errs = validate_module(&m);
    assert!(!errs.iter().any(|e| matches!(
        e,
        ValidationError::TargetPointerSizeInvalid { .. } | ValidationError::TargetTripleEmpty
    )));
}

#[test]
fn target_info_invalid_pointer_size_and_empty_triple_rejected() {
    let mut m = Module::new("t");
    m.target_info = Some(TargetInfo {
        triple: String::new(),
        pointer_size: 7,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let errs = validate_module(&m);
    assert!(errs.iter().any(|e| matches!(
        e,
        ValidationError::TargetPointerSizeInvalid { pointer_size: 7 }
    )));
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::TargetTripleEmpty))
    );
}

#[test]
fn absent_target_info_ok_without_ffi_boundary() {
    // A module with NO FFI boundary may stay target-independent: absent
    // target_info is neither sanity-checked nor required. (The historical
    // "never required" lock-in flipped with the ABI-pinning enforcement layer:
    // FFI-boundary modules now DO require it — see the tests further below.)
    let m = Module::new("t"); // target_info: None, no functions
    assert!(!m.requires_target_info());
    assert!(!validate_module(&m).iter().any(|e| matches!(
        e,
        ValidationError::TargetPointerSizeInvalid { .. }
            | ValidationError::TargetTripleEmpty
            | ValidationError::TargetInfoRequired { .. }
    )));
}

// --------------------------------------------------------------------------
// ABI pinning (finding #22): target-pinned struct-layout consistency.
// --------------------------------------------------------------------------

fn pinned_target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// Build a module with one struct whose layout fields are set, optionally
/// pinning a target.
fn module_with_layout(
    fields: Vec<FieldDef>,
    size: Option<u64>,
    align: Option<u64>,
    pin_target: bool,
) -> Module {
    let mut m = Module::new("layout");
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields,
        size,
        align,
        repr: StructRepr::C,
    });
    if pin_target {
        m.target_info = Some(pinned_target());
    }
    m
}

fn field_at(name: &str, ty: Ty, offset: u64) -> FieldDef {
    FieldDef {
        name: name.into(),
        ty,
        offset: Some(offset),
    }
}

#[test]
fn target_pinned_consistent_layout_ok() {
    // size 16, align 8, fields at 0 and 8 — a coherent C layout.
    let m = module_with_layout(
        vec![field_at("a", Ty::I32, 0), field_at("b", Ty::F64, 8)],
        Some(16),
        Some(8),
        true,
    );
    assert!(
        !has(&m, |e| matches!(
            e,
            ValidationError::StructLayoutInconsistent { .. }
        )),
        "coherent target-pinned layout must validate: {:?}",
        validate_module(&m)
    );
}

#[test]
fn target_pinned_non_power_of_two_align_rejected() {
    let m = module_with_layout(vec![field("a", Ty::I32)], Some(12), Some(3), true);
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::StructLayoutInconsistent {
            struct_id: 0,
            reason: "align must be a non-zero power of two"
        }
    )));
}

#[test]
fn target_pinned_size_not_multiple_of_align_rejected() {
    // align 8 but size 12 is not a multiple of 8.
    let m = module_with_layout(vec![field("a", Ty::I32)], Some(12), Some(8), true);
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::StructLayoutInconsistent {
            struct_id: 0,
            reason: "size must be a multiple of align"
        }
    )));
}

#[test]
fn target_pinned_field_offset_out_of_range_rejected() {
    // field "b" at offset 16 but struct size is only 8.
    let m = module_with_layout(
        vec![field_at("a", Ty::I32, 0), field_at("b", Ty::I32, 16)],
        Some(8),
        Some(8),
        true,
    );
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::StructLayoutInconsistent {
            struct_id: 0,
            reason: "field offset is outside the declared struct size"
        }
    )));
}

#[test]
fn target_pinned_trailing_zst_field_at_size_accepted() {
    // A trailing zero-sized field is allowed to begin exactly at the end of
    // the allocation.
    let m = module_with_layout(
        vec![field_at("a", Ty::U32, 0), field_at("b", Ty::Unit, 4)],
        Some(4),
        Some(4),
        true,
    );
    assert!(
        !has(&m, |e| matches!(
            e,
            ValidationError::StructLayoutInconsistent {
                reason: "field offset is outside the declared struct size",
                ..
            }
        )),
        "trailing ZST at offset == size must validate: {:?}",
        validate_module(&m)
    );
}

#[test]
fn target_pinned_non_zst_field_at_size_rejected() {
    // Equality is only legal for a field known to occupy no storage.
    let m = module_with_layout(
        vec![field_at("a", Ty::U32, 0), field_at("b", Ty::U8, 4)],
        Some(4),
        Some(4),
        true,
    );
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::StructLayoutInconsistent {
            struct_id: 0,
            reason: "field offset is outside the declared struct size"
        }
    )));
}

#[test]
fn layout_inconsistency_not_flagged_without_target() {
    // The SAME inconsistent layout (align 3) is left untouched without a pinned
    // target — target-independent IR may carry partial/placeholder layouts.
    let m = module_with_layout(vec![field("a", Ty::I32)], Some(12), Some(3), false);
    assert!(
        !has(&m, |e| matches!(
            e,
            ValidationError::StructLayoutInconsistent { .. }
        )),
        "layout consistency is only enforced under a pinned target"
    );
}

#[test]
fn partial_layout_under_target_not_flagged() {
    // size/align/offset all None under a pinned target: deferred to the backend,
    // not an inconsistency.
    let m = module_with_layout(vec![field("a", Ty::I32)], None, None, true);
    assert!(
        !has(&m, |e| matches!(
            e,
            ValidationError::StructLayoutInconsistent { .. }
        )),
        "absent layout fields are not inconsistent: {:?}",
        validate_module(&m)
    );
}

// --------------------------------------------------------------------------
// ABI pinning (finding #22): FFI struct-repr boundary (the Rust↔C
// struct-passing disagreement is rejected).
// --------------------------------------------------------------------------

/// A module with one struct of the given repr and one bodyless `external`
/// import declaration whose signature is `params -> returns`.
fn module_with_extern_decl(repr: StructRepr, params: Vec<Ty>, returns: Vec<Ty>) -> Module {
    let mut m = Module::new("ffi");
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields: vec![field("x", Ty::I32)],
        size: None,
        align: None,
        repr,
    });
    m.add_func_type(FuncTy {
        params,
        returns,
        is_vararg: false,
    });
    // Function::new is a bodyless External declaration (an FFI import).
    m.add_function(Function::new(
        FuncId::new(0),
        "imported",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    m
}

#[test]
fn extern_decl_passing_rust_repr_struct_by_value_is_rejected() {
    // The golden case: an FFI import takes a repr(Rust) struct by value — Rust
    // layout is unspecified, so the two objects cannot agree. Reject it.
    let m = module_with_extern_decl(StructRepr::Rust, vec![Ty::Struct(StructId::new(0))], vec![]);
    assert!(
        has(&m, |e| matches!(
            e,
            ValidationError::FfiStructReprUnpinned {
                struct_id: 0,
                position: "parameter",
                ..
            }
        )),
        "a repr(Rust) struct passed by value across an FFI boundary must be rejected: {:?}",
        validate_module(&m)
    );
}

#[test]
fn extern_decl_returning_rust_repr_struct_is_rejected() {
    let m = module_with_extern_decl(StructRepr::Rust, vec![], vec![Ty::Struct(StructId::new(0))]);
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::FfiStructReprUnpinned {
            struct_id: 0,
            position: "return",
            ..
        }
    )));
}

#[test]
fn extern_decl_passing_repr_c_struct_by_value_is_accepted() {
    // The fix: declare the struct repr(C) and the boundary is well-defined.
    let m = module_with_extern_decl(StructRepr::C, vec![Ty::Struct(StructId::new(0))], vec![]);
    assert!(
        !has(&m, |e| matches!(
            e,
            ValidationError::FfiStructReprUnpinned { .. }
        )),
        "a repr(C) struct across an FFI boundary must validate: {:?}",
        validate_module(&m)
    );
}

#[test]
fn extern_decl_passing_repr_transparent_struct_is_accepted() {
    let m = module_with_extern_decl(
        StructRepr::Transparent,
        vec![Ty::Struct(StructId::new(0))],
        vec![],
    );
    assert!(!has(&m, |e| matches!(
        e,
        ValidationError::FfiStructReprUnpinned { .. }
    )));
}

#[test]
fn extern_decl_passing_struct_by_pointer_is_accepted() {
    // Passing a pointer to the struct (not by value) does not cross the layout
    // boundary by value, so even repr(Rust) is fine.
    let m = module_with_extern_decl(StructRepr::Rust, vec![Ty::Ptr], vec![]);
    assert!(!has(&m, |e| matches!(
        e,
        ValidationError::FfiStructReprUnpinned { .. }
    )));
}

#[test]
fn body_bearing_function_with_rust_repr_struct_param_is_not_an_ffi_boundary() {
    // A body-bearing function's structs never cross an object boundary by name,
    // so a repr(Rust) struct parameter is fine (it is layout-internal).
    let mut m = Module::new("internal");
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields: vec![field("x", Ty::I32)],
        size: None,
        align: None,
        repr: StructRepr::Rust,
    });
    m.add_func_type(FuncTy {
        params: vec![Ty::Struct(StructId::new(0))],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = Function::new(
        FuncId::new(0),
        "internal_fn",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    func.linkage = Linkage::Internal;
    // Give it a trivial body so it is not a bodyless declaration.
    let mut block = trust_ir::Block::new(BlockId::new(0));
    block.params.push((
        trust_ir::value::ValueId::new(0),
        Ty::Struct(StructId::new(0)),
    ));
    block.body.push(trust_ir::node::InstrNode::new(
        trust_ir::inst::Inst::Return { values: vec![] },
    ));
    func.blocks.push(block);
    m.add_function(func);

    assert!(
        !has(&m, |e| matches!(
            e,
            ValidationError::FfiStructReprUnpinned { .. }
        )),
        "a body-bearing function is not an FFI boundary: {:?}",
        validate_module(&m)
    );
}

// --------------------------------------------------------------------------
// ABI pinning (enforcement): target_info is REQUIRED at an FFI boundary
// (Module::requires_target_info + ValidationError::TargetInfoRequired).
// --------------------------------------------------------------------------

/// A module whose single function is a bodyless `external` import declaration
/// with the trivial signature `fn() -> ()`.
fn module_with_plain_extern_decl() -> Module {
    let mut m = Module::new("ffi_required");
    m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    // Function::new is a bodyless External declaration (an FFI import).
    m.add_function(Function::new(
        FuncId::new(0),
        "imported",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    m
}

#[test]
fn extern_decl_without_target_info_rejected() {
    let m = module_with_plain_extern_decl();
    assert!(m.requires_target_info());
    assert!(
        has(&m, |e| matches!(
            e,
            ValidationError::TargetInfoRequired { .. }
        )),
        "a bodyless external declaration is an FFI boundary and must pin a target: {:?}",
        validate_module(&m)
    );
}

#[test]
fn extern_decl_with_target_info_accepted() {
    let mut m = module_with_plain_extern_decl();
    m.target_info = Some(pinned_target());
    assert!(
        !has(&m, |e| matches!(
            e,
            ValidationError::TargetInfoRequired { .. }
        )),
        "pinning a target satisfies the FFI-boundary requirement: {:?}",
        validate_module(&m)
    );
}

/// Two body-bearing functions with differing calling conventions and a direct
/// call edge between them — a cross-convention edge with no external symbol.
fn module_with_cross_conv_call(pin_target: bool) -> Module {
    let mut m = Module::new("cross_conv");
    m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });

    let mut callee = Function::new(FuncId::new(0), "c_side", FuncTyId::new(0), BlockId::new(0));
    callee.calling_conv = trust_ir::CallingConv::C;
    let mut cb = trust_ir::Block::new(BlockId::new(0));
    cb.body.push(trust_ir::node::InstrNode::new(
        trust_ir::inst::Inst::Return { values: vec![] },
    ));
    callee.blocks.push(cb);
    m.add_function(callee);

    let mut caller = Function::new(
        FuncId::new(1),
        "rust_side",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    caller.calling_conv = trust_ir::CallingConv::Rust;
    let mut rb = trust_ir::Block::new(BlockId::new(0));
    rb.body
        .push(trust_ir::node::InstrNode::new(trust_ir::inst::Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        }));
    rb.body.push(trust_ir::node::InstrNode::new(
        trust_ir::inst::Inst::Return { values: vec![] },
    ));
    caller.blocks.push(rb);
    m.add_function(caller);

    if pin_target {
        m.target_info = Some(pinned_target());
    }
    m
}

/// The Invoke form of the same cross-convention edge: an Invoke is a direct
/// call with an unwind edge, so it is the same FFI boundary a plain Call is
/// (regression: the boundary scan originally matched only Call/CallIndirect,
/// so wrapping the edge in an Invoke silently bypassed TargetInfoRequired).
fn module_with_cross_conv_invoke(pin_target: bool) -> Module {
    let mut m = module_with_cross_conv_call(pin_target);
    // Rebuild the caller's entry block as an invoke-shaped CFG:
    //   b0: invoke @c_side() -> (), normal b1, unwind b2
    //   b1: ret;   b2: landing_pad (cleanup); resume
    let caller = &mut m.functions[1];
    let b0 = BlockId::new(0);
    let b1 = BlockId::new(1);
    let b2 = BlockId::new(2);
    let exn = trust_ir::value::ValueId::new(100);
    let sel = trust_ir::value::ValueId::new(101);
    let mut eb = trust_ir::Block::new(b0);
    eb.body.push(trust_ir::node::InstrNode::new(
        trust_ir::inst::Inst::Invoke {
            callee: FuncId::new(0),
            args: vec![],
            normal_dest: b1,
            normal_args: vec![],
            unwind_dest: b2,
        },
    ));
    let mut nb = trust_ir::Block::new(b1);
    nb.body.push(trust_ir::node::InstrNode::new(
        trust_ir::inst::Inst::Return { values: vec![] },
    ));
    let mut ub = trust_ir::Block::new(b2);
    ub.body.push(
        trust_ir::node::InstrNode::new(trust_ir::inst::Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results([exn, sel]),
    );
    ub.body.push(trust_ir::node::InstrNode::new(
        trust_ir::inst::Inst::Resume { exn },
    ));
    caller.blocks = vec![eb, nb, ub];
    m
}

#[test]
fn cross_conv_invoke_edge_without_target_info_rejected() {
    let m = module_with_cross_conv_invoke(false);
    assert!(m.requires_target_info());
    assert!(
        has(&m, |e| matches!(
            e,
            ValidationError::TargetInfoRequired { .. }
        )),
        "a rustcc -> ccc INVOKE edge is an FFI boundary and must pin a target: {:?}",
        validate_module(&m)
    );
}

#[test]
fn cross_conv_invoke_edge_with_target_info_accepted() {
    let m = module_with_cross_conv_invoke(true);
    assert!(
        !has(&m, |e| matches!(
            e,
            ValidationError::TargetInfoRequired { .. }
        )),
        "pinning a target satisfies the invoke FFI boundary: {:?}",
        validate_module(&m)
    );
}

#[test]
fn cross_conv_call_edge_without_target_info_rejected() {
    let m = module_with_cross_conv_call(false);
    assert!(m.requires_target_info());
    assert!(
        has(&m, |e| matches!(
            e,
            ValidationError::TargetInfoRequired { .. }
        )),
        "a rustcc -> ccc call edge is an FFI boundary and must pin a target: {:?}",
        validate_module(&m)
    );
}

#[test]
fn cross_conv_call_edge_with_target_info_accepted() {
    let m = module_with_cross_conv_call(true);
    assert!(!has(&m, |e| matches!(
        e,
        ValidationError::TargetInfoRequired { .. }
    )));
}

#[test]
fn uniform_conv_body_bearing_module_does_not_require_target_info() {
    // Same shape as the cross-conv module but with matching conventions:
    // no FFI boundary, so target_info stays optional.
    let mut m = module_with_cross_conv_call(false);
    for f in &mut m.functions {
        f.calling_conv = trust_ir::CallingConv::Rust;
    }
    assert!(!m.requires_target_info());
    assert!(!has(&m, |e| matches!(
        e,
        ValidationError::TargetInfoRequired { .. }
    )));
}

#[test]
fn cross_conv_indirect_call_without_target_info_rejected() {
    // A CallIndirect whose declared edge convention differs from the enclosing
    // function's is an FFI boundary even with no static callee in sight.
    let mut m = Module::new("cross_conv_indirect");
    let sig = m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut caller = Function::new(FuncId::new(0), "rust_side", sig, BlockId::new(0));
    caller.calling_conv = trust_ir::CallingConv::Rust;
    let mut block = trust_ir::Block::new(BlockId::new(0));
    block
        .params
        .push((trust_ir::value::ValueId::new(0), Ty::Func(sig)));
    block.body.push(trust_ir::node::InstrNode::new(
        trust_ir::inst::Inst::CallIndirect {
            callee: trust_ir::value::ValueId::new(0),
            sig,
            args: vec![],
            calling_conv: trust_ir::CallingConv::C,
        },
    ));
    block.body.push(trust_ir::node::InstrNode::new(
        trust_ir::inst::Inst::Return { values: vec![] },
    ));
    caller.blocks.push(block);
    m.add_function(caller);

    assert!(m.requires_target_info());
    assert!(has(&m, |e| matches!(
        e,
        ValidationError::TargetInfoRequired { .. }
    )));

    // Pinning a target resolves it.
    m.target_info = Some(pinned_target());
    assert!(!has(&m, |e| matches!(
        e,
        ValidationError::TargetInfoRequired { .. }
    )));
}
