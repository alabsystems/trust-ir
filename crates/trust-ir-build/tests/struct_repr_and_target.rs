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
        origin: None,
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

/// Trust (#171 Part A): a transparent wrapper whose companion is a zero-sized STRUCT.
///
/// This is the real-world shape the spelling-only ZST test rejected:
/// `#[repr(transparent)] struct Unique<T> { pointer: NonNull<T>, _marker: PhantomData<T> }`.
/// `PhantomData<T>` lowers to `Ty::Struct(..)` with a recorded `size: Some(0)`, so counting by
/// SPELLING alone saw two non-ZST fields and rejected a well-formed module. Five such rejections
/// were measured in the ui corpus.
fn module_with_zst_companion(companion_size: Option<u64>) -> Module {
    let mut m = Module::new("repr");
    // struct 0: the zero-sized companion (PhantomData's stand-in).
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "Marker".into(),
        fields: vec![],
        size: companion_size,
        align: Some(1),
        repr: StructRepr::Rust,
        origin: None,
    });
    // struct 1: the transparent wrapper — one real field plus the ZST companion.
    m.add_struct(StructDef {
        id: StructId::new(1),
        name: "Wrapper".into(),
        fields: vec![
            field("pointer", Ty::Ptr),
            field("_marker", Ty::Struct(StructId::new(0))),
        ],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::Transparent,
        origin: None,
    });
    m
}

#[test]
fn transparent_with_zero_sized_struct_companion_ok() {
    let m = module_with_zst_companion(Some(0));
    assert!(
        !has(&m, |e| matches!(
            e,
            ValidationError::TransparentReprFieldCount { .. }
        )),
        "a companion struct with a PROVEN size of 0 must count as a ZST"
    );
}

#[test]
fn transparent_counts_an_overaligned_zst_as_nontrivial() {
    let mut m = Module::new("repr");
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "OveralignedMarker".into(),
        fields: vec![],
        size: Some(0),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    });
    m.add_struct(StructDef {
        id: StructId::new(1),
        name: "BadTransparent".into(),
        fields: vec![
            field("value", Ty::I64),
            field("marker", Ty::Struct(StructId::new(0))),
        ],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::Transparent,
        origin: None,
    });

    assert!(has(&m, |e| matches!(
        e,
        ValidationError::TransparentReprFieldCount {
            actual_non_zst: 2,
            ..
        }
    )));
}

#[test]
fn transparent_accepts_one_overaligned_zst_as_its_sole_nontrivial_field() {
    let mut m = Module::new("repr");
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "OveralignedMarker".into(),
        fields: vec![],
        size: Some(0),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    });
    m.add_struct(StructDef {
        id: StructId::new(1),
        name: "TransparentMarker".into(),
        fields: vec![
            field("marker", Ty::Struct(StructId::new(0))),
            field("unit", Ty::Unit),
        ],
        size: Some(0),
        align: Some(8),
        repr: StructRepr::Transparent,
        origin: None,
    });

    assert!(!has(&m, |e| matches!(
        e,
        ValidationError::TransparentReprFieldCount { .. }
    )));
}

#[test]
fn transparent_with_unsized_struct_companion_still_rejected() {
    // THE FAIL-CLOSED TWIN, and the reason the widening is safe. `size: None` is what both
    // producers record when rustc's layout query declines — a generic/param-bearing type, an
    // unregistered id, a non-faithful lane. An UNPROVEN ZST must still count as non-ZST, or the
    // check becomes fail-open on exactly the modules least able to afford it.
    let m = module_with_zst_companion(None);
    assert!(
        has(&m, |e| matches!(
            e,
            ValidationError::TransparentReprFieldCount {
                actual_non_zst: 2,
                ..
            }
        )),
        "a companion struct of UNPROVEN size must still count as non-ZST (fail-closed)"
    );
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

/// CORRECTED (#171 residue): zero non-ZST fields is LEGAL, not an error.
///
/// This test previously asserted the opposite, pinning an "exactly one" rule. The Rust reference
/// says a `repr(transparent)` type has "the same layout and ABI as their single non-zero-sized
/// field, IF ANY" — at most one, and zero is fine, the type then being a ZST itself.
/// `#[repr(transparent)] struct Foo(());` compiles.
///
/// It is not hypothetical: `ManuallyDrop<T>` and `MaybeDangling<T>` over a zero-sized `T` are
/// exactly this shape, and the Trust producer emits them at `size=0 align=1 repr=transparent`.
/// The old rule called 12 occurrences of correct Rust malformed across the ui corpus. The
/// original assertion carried no rationale (unlike every other check in this file) and came from
/// the batch commit that introduced repr classification generally, so it reads as a simplified
/// reading of the rule rather than a considered decision.
#[test]
fn transparent_with_zero_non_zst_fields_accepted() {
    let m = module_with_struct(vec![field("z", Ty::Unit)], StructRepr::Transparent);
    assert!(
        !has(&m, |e| matches!(
            e,
            ValidationError::TransparentReprFieldCount { .. }
        )),
        "a transparent struct whose only field is a ZST is legal Rust (at most one non-ZST)"
    );
}

/// The `> 1` half of the rule must still fire — two non-ZST fields have no single field whose
/// layout and ABI the struct can take, which is what `transparent` means.
#[test]
fn transparent_with_zero_non_zst_but_two_zsts_accepted() {
    let m = module_with_struct(
        vec![field("a", Ty::Unit), field("b", Ty::Unit)],
        StructRepr::Transparent,
    );
    assert!(!has(&m, |e| matches!(
        e,
        ValidationError::TransparentReprFieldCount { .. }
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
        origin: None,
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
fn target_pinned_layout_declines_an_unrepresented_scalar_abi() {
    // i686's Rust/LLVM layout aligns f64 to 4 bytes, unlike TrustIR's
    // canonical 8-byte scalar table. This descriptor is valid i686 layout;
    // the validator must neither call it misaligned nor silently certify it
    // from the wrong table. Until TargetInfo carries a data-layout identity,
    // the only sound answer is an explicit unsupported-layout refusal.
    let mut m = module_with_layout(
        vec![field_at("tag", Ty::U8, 0), field_at("value", Ty::F64, 4)],
        Some(12),
        Some(4),
        false,
    );
    m.target_info = Some(TargetInfo {
        triple: "i686-unknown-linux-gnu".into(),
        pointer_size: 4,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let errors = validate_module(&m);
    assert!(errors.iter().any(|error| matches!(
        error,
        ValidationError::TargetScalarLayoutUnavailable { struct_id: 0, triple }
            if triple == "i686-unknown-linux-gnu"
    )));
    assert!(!errors.iter().any(|error| matches!(
        error,
        ValidationError::StructLayoutInconsistent {
            reason: "field offset is not a multiple of the field's effective alignment",
            ..
        }
    )));
}

#[test]
fn target_pinned_layout_declines_a_forged_canonical_triple_width() {
    // The architecture spelling is not enough: an x86_64 data layout cannot
    // have 32-bit pointers. Accepting this pair as canonical would let the
    // claimed width manufacture pointer size/alignment evidence.
    let mut m = module_with_layout(
        vec![field_at("tag", Ty::U8, 0), field_at("value", Ty::Ptr, 4)],
        Some(8),
        Some(4),
        false,
    );
    m.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 4,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    assert!(validate_module(&m).iter().any(|error| matches!(
        error,
        ValidationError::TargetScalarLayoutUnavailable { struct_id: 0, triple }
            if triple == "x86_64-unknown-linux-gnu"
    )));
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

fn trailing_function_item_module() -> Module {
    // Actual Rust repr(C) layout of C<F, G> { first: F, word: u64, last: G }
    // for two distinct function items: size 8, alignment 8, offsets [0, 0, 8].
    let mut module = module_with_layout(
        vec![
            field_at("first", Ty::FnItem(FuncId::new(7)), 0),
            field_at("word", Ty::U64, 0),
            field_at("last", Ty::FnItem(FuncId::new(11)), 8),
        ],
        Some(8),
        Some(8),
        true,
    );
    let signature = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![Ty::U64], false))
        .unwrap();
    for (id, answer) in [(7, 1), (11, 2)] {
        let mut function = Function::new(
            FuncId::new(id),
            format!("pick_{answer}"),
            signature,
            BlockId::new(0),
        );
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(
            trust_ir::InstrNode::new(trust_ir::Inst::Const {
                ty: Ty::U64,
                value: trust_ir::Constant::Int(answer),
            })
            .with_result(trust_ir::ValueId::new(0)),
        );
        block
            .body
            .push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
                values: vec![trust_ir::ValueId::new(0)],
            }));
        function.blocks.push(block);
        module.functions.push(function);
    }
    module
}

#[test]
fn target_pinned_distinct_function_items_preserve_rust_trailing_zst_layout() {
    let mut module = trailing_function_item_module();
    let element = module.add_type(Ty::Struct(StructId::new(0))).unwrap();
    assert!(
        validate_module(&module).is_empty(),
        "{:?}",
        validate_module(&module)
    );
    let layouts = module.layout_table();
    let shape = layouts.ty_layout(&Ty::Struct(StructId::new(0))).unwrap();
    assert_eq!(shape.size_bytes(), Some(8));
    assert_eq!(shape.align_bits, Some(64));
    let array = layouts.ty_layout(&Ty::Array(element, 2)).unwrap();
    assert_eq!(array.size_bytes(), Some(16));
    assert_ne!(
        module.structs[0].fields[0].ty,
        module.structs[0].fields[2].ty
    );
}

#[test]
fn trailing_function_item_layout_requires_a_unique_valid_header_and_exact_bounds() {
    let mut missing = trailing_function_item_module();
    missing.functions.pop();
    let mut duplicate = trailing_function_item_module();
    duplicate.functions.push(duplicate.functions[1].clone());
    let mut bad_signature = trailing_function_item_module();
    bad_signature.functions[1].ty = FuncTyId::new(99);
    let mut beyond = trailing_function_item_module();
    beyond.structs[0].fields[2].offset = Some(9);
    let mut nonzero = trailing_function_item_module();
    nonzero.structs[0].fields[2].ty = Ty::U8;
    for (name, module) in [
        ("missing header", missing),
        ("duplicate header", duplicate),
        ("invalid signature", bad_signature),
        ("beyond allocation", beyond),
        ("nonzero field", nonzero),
    ] {
        assert!(
            has(&module, |error| matches!(
                error,
                ValidationError::StructLayoutInconsistent {
                    reason: "field offset is outside the declared struct size",
                    ..
                }
            )),
            "{name} must not grant a trailing zero-sized layout: {:?}",
            validate_module(&module)
        );
    }
    let mut misaligned = trailing_function_item_module();
    misaligned.structs[0].fields[1].offset = Some(1);
    assert!(has(&misaligned, |error| matches!(
        error,
        ValidationError::StructLayoutInconsistent {
            reason: "field offset is not a multiple of the field's effective alignment",
            ..
        }
    )));
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
fn layout_inconsistency_flagged_without_target() {
    // WS2.3 (F-031): the SAME inconsistent layout (align 3) is refused without
    // a pinned target too. The former premise — "target-independent IR may
    // carry placeholder layouts" — is withdrawn: `Module::ty_layout_shape` and
    // the interpreter already treat a declared layout as normative in a
    // target-free module (canonical reference layout), so the validator must.
    let m = module_with_layout(vec![field("a", Ty::I32)], Some(12), Some(3), false);
    assert!(m.target_info.is_none());
    assert!(
        has(&m, |e| matches!(
            e,
            ValidationError::StructLayoutInconsistent {
                struct_id: 0,
                reason: "align must be a non-zero power of two"
            }
        )),
        "declared layout consistency is enforced with or without a target: {:?}",
        validate_module(&m)
    );
    // Mutation control: an ABSENT layout stays unflagged without a target.
    let absent = module_with_layout(vec![field("a", Ty::I32)], None, None, false);
    assert!(
        !has(&absent, |e| matches!(
            e,
            ValidationError::StructLayoutInconsistent { .. }
        )),
        "absent layout fields are not inconsistent: {:?}",
        validate_module(&absent)
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
        origin: None,
    });
    m.add_func_type(FuncTy {
        params,
        returns,
        abi: None,
        is_vararg: false,
    })
    .expect("Module::add_func_type: test fixture");
    // Function::new is a bodyless External declaration (an FFI import).
    m.try_add_function(Function::new(
        FuncId::new(0),
        "imported",
        FuncTyId::new(0),
        BlockId::new(0),
    ))
    .expect("Module::try_add_function: test fixture");
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
        origin: None,
    });
    m.add_func_type(FuncTy {
        params: vec![Ty::Struct(StructId::new(0))],
        returns: vec![],
        abi: None,
        is_vararg: false,
    })
    .expect("Module::add_func_type: test fixture");
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
    m.try_add_function(func)
        .expect("Module::try_add_function: test fixture");

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
        abi: None,
        is_vararg: false,
    })
    .expect("Module::add_func_type: test fixture");
    // Function::new is a bodyless External declaration (an FFI import).
    m.try_add_function(Function::new(
        FuncId::new(0),
        "imported",
        FuncTyId::new(0),
        BlockId::new(0),
    ))
    .expect("Module::try_add_function: test fixture");
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
        abi: None,
        is_vararg: false,
    })
    .expect("Module::add_func_type: test fixture");

    let mut callee = Function::new(FuncId::new(0), "c_side", FuncTyId::new(0), BlockId::new(0));
    callee.calling_conv = trust_ir::CallingConv::C;
    let mut cb = trust_ir::Block::new(BlockId::new(0));
    cb.body.push(trust_ir::node::InstrNode::new(
        trust_ir::inst::Inst::Return { values: vec![] },
    ));
    callee.blocks.push(cb);
    m.try_add_function(callee)
        .expect("Module::try_add_function: test fixture");

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
    m.try_add_function(caller)
        .expect("Module::try_add_function: test fixture");

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
    let sig = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    m.try_add_function(caller)
        .expect("Module::try_add_function: test fixture");

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

// ===========================================================================
// Trust (wave-SG): THE FIELD-OFFSET ALIGNMENT RULE.
//
// The three checks above police `align`, `size % align` and `offset <= size` —
// none of which notices a `u64` declared at byte 3. `interpret::struct_layout`
// re-validates exactly that now the declared layout is NORMATIVE, so an offset
// this validator passed and the interpreter refuses is a module `validate_module`
// called well-formed and the executor cannot run.
//
// Each REFUSAL is paired with an ACCEPT CONTROL on a byte-identical module
// differing only in the offset (or only in the repr), without which a rule that
// rejected every struct would pass every refusal here.
// ===========================================================================

/// `module_with_layout` with an explicit `StructRepr`, so the packed clamp can be
/// exercised in both directions.
fn module_with_repr(
    fields: Vec<FieldDef>,
    size: Option<u64>,
    align: Option<u64>,
    repr: StructRepr,
) -> Module {
    let mut m = Module::new("layout");
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields,
        size,
        align,
        repr,
        origin: None,
    });
    m.target_info = Some(pinned_target());
    m
}

fn misaligned(e: &ValidationError) -> bool {
    matches!(
        e,
        ValidationError::StructLayoutInconsistent {
            struct_id: 0,
            reason: "field offset is not a multiple of the field's effective alignment"
        }
    )
}

/// **THE GATE.** `#[repr(C)] struct { a: u8, b: u64 }` with `b` declared at byte 3.
/// Every pre-existing rule is satisfied — align 8 is a power of two, size 16 is a
/// multiple of it, offset 3 is inside the struct — and the module validated.
#[test]
fn target_pinned_unaligned_scalar_field_offset_rejected() {
    let m = module_with_layout(
        vec![field_at("a", Ty::U8, 0), field_at("b", Ty::U64, 3)],
        Some(16),
        Some(8),
        true,
    );
    assert!(
        has(&m, misaligned),
        "a u64 at byte 3 must be refused: {:?}",
        validate_module(&m)
    );
    // ACCEPT CONTROL: the byte-identical module with `b` at its natural offset.
    let ok = module_with_layout(
        vec![field_at("a", Ty::U8, 0), field_at("b", Ty::U64, 8)],
        Some(16),
        Some(8),
        true,
    );
    assert!(!has(&ok, misaligned), "{:?}", validate_module(&ok));
}

/// The clamp is a MODEL of `#[repr(packed(N))]`, in BOTH directions — which is what
/// makes the rule a model rather than a blanket natural-alignment demand.
#[test]
fn packed_clamp_admits_what_it_should_and_refuses_what_it_should_not() {
    let fields = || vec![field_at("a", Ty::U8, 0), field_at("b", Ty::U64, 3)];
    let packed1 = module_with_repr(fields(), Some(11), Some(1), StructRepr::Packed(1));
    assert!(
        !has(&packed1, misaligned),
        "packed(1) makes byte 3 legal Rust: {:?}",
        validate_module(&packed1)
    );
    let packed4 = module_with_repr(fields(), Some(12), Some(4), StructRepr::Packed(4));
    assert!(
        has(&packed4, misaligned),
        "packed(4) must still refuse byte 3: {:?}",
        validate_module(&packed4)
    );
    let packed4_ok = module_with_repr(
        vec![field_at("a", Ty::U8, 0), field_at("b", Ty::U64, 4)],
        Some(12),
        Some(4),
        StructRepr::Packed(4),
    );
    assert!(
        !has(&packed4_ok, misaligned),
        "{:?}",
        validate_module(&packed4_ok)
    );
}

#[test]
fn packed_clamp_also_bounds_the_declared_struct_alignment() {
    let bad = module_with_repr(
        vec![field_at("value", Ty::U64, 0)],
        Some(8),
        Some(8),
        StructRepr::Packed(1),
    );
    let over_clamp = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::StructLayoutInconsistent {
                struct_id: 0,
                reason: "struct alignment exceeds the repr(packed) clamp"
            }
        )
    };
    assert!(
        has(&bad, over_clamp),
        "packed(1) cannot retain aggregate alignment 8: {:?}",
        validate_module(&bad)
    );

    let control = module_with_repr(
        vec![field_at("value", Ty::U64, 0)],
        Some(8),
        Some(1),
        StructRepr::Packed(1),
    );
    assert!(
        !has(&control, over_clamp),
        "{:?}",
        validate_module(&control)
    );
}

/// A `Packed(N)` whose `N` is not a power of two is ALREADY refused by
/// `PackedReprInvalidAlign`. The alignment rule must not compound it with a derived
/// error computed from a clamp it cannot trust — one malformed repr, one error.
/// (It is also why the clamp is validated rather than divided by: `Packed(0)` would
/// otherwise be a modulo by zero.)
#[test]
fn an_invalid_packed_clamp_produces_one_error_not_a_cascade() {
    for bad in [0u32, 3, 6] {
        let m = module_with_repr(
            vec![field_at("a", Ty::U8, 0), field_at("b", Ty::U64, 3)],
            Some(11),
            Some(1),
            StructRepr::Packed(bad),
        );
        assert!(
            has(&m, |e| matches!(
                e,
                ValidationError::PackedReprInvalidAlign { struct_id: 0, .. }
            )),
            "packed({bad}) must be refused as a repr: {:?}",
            validate_module(&m)
        );
        assert!(
            !has(&m, misaligned),
            "packed({bad}) must not ALSO produce a derived alignment error: {:?}",
            validate_module(&m)
        );
        // WS2.3: nor a derived "declared layout is incoherent" report from the
        // layout authority, which refuses the same malformed clamp.
        assert!(
            !has(&m, |e| matches!(
                e,
                ValidationError::StructLayoutInconsistent { .. }
            )),
            "packed({bad}) must not ALSO produce a derived layout error: {:?}",
            validate_module(&m)
        );
    }
}

/// The rule fires only on an EXPLICITLY-declared offset. `None` is the honest
/// absent-fill a producer records when its layout query declines, and flagging it
/// would reject every generic struct in the corpus.
#[test]
fn an_absent_offset_is_never_flagged_as_misaligned() {
    let m = module_with_layout(
        vec![field("a", Ty::U8), field("b", Ty::U64)],
        Some(16),
        Some(8),
        true,
    );
    assert!(!has(&m, misaligned), "{:?}", validate_module(&m));
}

/// WS2.3 (F-031): same scope as every other rule in this pass — with or without
/// a pinned target. A target-free module is judged against the canonical
/// reference layout, exactly as `Module::ty_layout_shape` and the interpreter
/// judge it; "target-independent IR may carry placeholder layouts" is withdrawn.
#[test]
fn misaligned_offset_flagged_without_target() {
    let mut m = module_with_layout(
        vec![field_at("a", Ty::U8, 0), field_at("b", Ty::U64, 3)],
        Some(16),
        Some(8),
        false,
    );
    m.target_info = None;
    assert!(has(&m, misaligned), "{:?}", validate_module(&m));
    // ACCEPT CONTROL: `b` at its natural offset validates target-free too.
    let mut ok = module_with_layout(
        vec![field_at("a", Ty::U8, 0), field_at("b", Ty::U64, 8)],
        Some(16),
        Some(8),
        false,
    );
    ok.target_info = None;
    assert!(!has(&ok, misaligned), "{:?}", validate_module(&ok));
}

/// The struct field-overlap rule (WS2.3) reports one error for a struct when
/// SOME pair of its sized, placed fields overlaps — the verdict of testing
/// every pair, now a sort-and-sweep — however the overlapping pair is
/// placed among disjoint, zero-sized, unplaced and unsized fields.
#[test]
fn the_field_overlap_rule_is_one_report_for_some_overlapping_pair() {
    let placed = |name: &str, ty: Ty, offset: u64| FieldDef {
        name: name.into(),
        ty,
        offset: Some(offset),
    };
    let with_fields = |fields: Vec<FieldDef>| {
        let mut m = Module::new("overlap");
        m.add_struct(StructDef {
            id: StructId::new(0),
            name: "S".into(),
            fields,
            size: Some(16),
            align: Some(8),
            repr: StructRepr::C,
            origin: None,
        });
        m
    };
    let overlap_reports = |m: &Module| {
        validate_module(m)
            .into_iter()
            .filter(|error| {
                matches!(
                    error,
                    ValidationError::StructLayoutInconsistent { reason, .. }
                        if *reason == trust_ir_build::validate::STRUCT_FIELDS_OVERLAP_REASON
                )
            })
            .count()
    };
    // Disjoint in reverse order, a ZST sitting inside a field, an unplaced
    // ZST, and a field with no layout: no overlap.
    let disjoint = vec![
        placed("d", Ty::U64, 8),
        placed("c", Ty::U32, 4),
        placed("z", Ty::Unit, 5),
        field("u", Ty::Unit),
        placed("x", Ty::Struct(StructId::new(9)), 0),
        placed("a", Ty::U16, 0),
        placed("b", Ty::U8, 2),
    ];
    assert_eq!(overlap_reports(&with_fields(disjoint.clone())), 0);
    // The same fields plus one late byte inside `c`: one report, however
    // many pairs overlap.
    for extra in [
        placed("o", Ty::U8, 6),
        placed("o", Ty::U64, 0),
        placed("o", Ty::U16, 3),
    ] {
        let mut fields = disjoint.clone();
        fields.push(extra.clone());
        assert_eq!(overlap_reports(&with_fields(fields)), 1, "{extra:?}");
    }
}
