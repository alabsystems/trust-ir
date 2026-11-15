// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn target_symbol_error_order_matches_complete_actual_original_rule() {
    let mut m = fixture();
    let c = sym("G", 7);
    let ty = Ty::Ref(Box::new(Ty::Bool));
    m.globals[0].initializer = None;
    m.globals[0].tls = Some(TlsModel::LocalExec);
    m.globals[0].linkage = Linkage::Weak;
    run(&m, &c, &ty);
    let duplicate = m.globals[0].clone();
    m.globals.push(duplicate);
    assert!(matches!(
        &run(&m, &c, &ty).0[..],
        [ValidationError::PointerConstantRefused {
            reason: PointerConstantRefusal::AmbiguousSymbol {
                globals: 2,
                functions: 0
            },
            ..
        }]
    ));
    run(&m, &sym("missing", 0), &ty);
}
#[test]
fn thin_addend_type_and_mutability_rules_keep_ref_ptrconst_ptrmut_distinct() {
    let mut m = fixture();
    for addend in [0, 1, -1] {
        for t in [
            Ty::Ref(Box::new(Ty::Bool)),
            Ty::PtrConst(Box::new(Ty::Bool)),
            Ty::PtrMut(Box::new(Ty::Bool)),
            Ty::Ref(Box::new(Ty::U8)),
        ] {
            run(&m, &sym("G", addend), &t);
        }
    }
    m.globals[0].mutable = true;
    assert!(
        run(&m, &sym("G", 0), &Ty::PtrMut(Box::new(Ty::Bool)))
            .0
            .is_empty()
    );
    assert!(matches!(
        &run(&m, &sym("G", 0), &Ty::Ref(Box::new(Ty::Bool))).0[..],
        [ValidationError::PointerConstantRefused {
            reason: PointerConstantRefusal::MutabilityMismatch {
                global_mutable: true
            },
            ..
        }]
    ));
}
#[test]
fn thin_pointer_compares_resolved_nominal_shapes_not_raw_type_ids() {
    let mut m = fixture();
    let mut other = m.structs[0].clone();
    other.id = StructId::new(9);
    m.structs.push(other);
    m.globals[0].ty = Ty::Struct(StructId::new(0));
    let t = Ty::PtrConst(Box::new(Ty::Struct(StructId::new(9))));
    assert!(run(&m, &sym("G", 0), &t).0.is_empty());
    m.structs[1].fields[1].ty = Ty::Bool;
    assert!(matches!(
        &run(&m, &sym("G", 0), &t).0[..],
        [ValidationError::PointerConstantRefused {
            reason: PointerConstantRefusal::PointeeTypeMismatch { .. },
            ..
        }]
    ));
}
#[test]
fn str_windows_validate_only_selected_bytes_and_exact_character_boundaries() {
    let mut m = fixture();
    let t = Ty::FatPtr(FatPtrKind::Str);
    for (offset, len) in [(0, 2), (2, 2), (4, 0), (1, 1), (0, 1), (3, 2), (-1, 0)] {
        run(&m, &fat("bytes", offset, Constant::Int(len)), &t);
    }
    assert!(run(&m, &fat("bytes", 0, Constant::Int(2)), &t).0.is_empty());
    m.globals[1].initializer = Some(Constant::Bytes {
        data: vec![0xff, b'a', 0xff],
        utf8: true,
    });
    m.globals[1].ty = Ty::Array(TyId::new(0), 3);
    assert!(run(&m, &fat("bytes", 1, Constant::Int(1)), &t).0.is_empty());
    assert!(
        !run(
            &m,
            m.globals[1].initializer.as_ref().unwrap(),
            &m.globals[1].ty
        )
        .0
        .is_empty()
    );
}
#[test]
fn fat_length_array_offset_and_initializer_errors_preserve_original_precedence() {
    let mut m = fixture();
    let t = Ty::FatPtr(FatPtrKind::Str);
    for length in [
        Constant::Bool(true),
        Constant::Int(-1),
        Constant::Int(i128::MAX),
    ] {
        run(&m, &fat("bytes", 0, length), &t);
    }
    m.globals[1].mutable = true;
    run(&m, &fat("bytes", 0, Constant::Bool(true)), &t);
    m.globals[1].mutable = false;
    m.globals[1].ty = Ty::Bool;
    run(&m, &fat("bytes", -1, Constant::Int(1)), &t);
    m.globals[1].ty = Ty::Array(TyId::new(999), 4);
    run(&m, &fat("bytes", -1, Constant::Int(1)), &t);
    m.globals[1].ty = Ty::Array(TyId::new(0), 4);
    m.globals[1].initializer = Some(Constant::Bytes {
        data: vec![1],
        utf8: false,
    });
    run(&m, &fat("bytes", 0, Constant::Int(1)), &t);
    m.globals[1].initializer = Some(Constant::Bytes {
        data: vec![1],
        utf8: true,
    });
    run(&m, &fat("bytes", 1, Constant::Int(3)), &t);
}
#[test]
fn slices_use_actual_element_layout_alignment_and_u128_window_arithmetic() {
    let m = fixture();
    let t = Ty::FatPtr(FatPtrKind::Slice(TyId::new(2)));
    for (offset, len) in [
        (0, 4),
        (2, 3),
        (1, 1),
        (8, 0),
        (8, 1),
        (i64::MAX, i128::MAX),
    ] {
        run(&m, &fat("u16", offset, Constant::Int(len)), &t);
    }
    assert!(run(&m, &fat("u16", 2, Constant::Int(3)), &t).0.is_empty());
    run(
        &m,
        &fat("u16", 0, Constant::Int(1)),
        &Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
    );
}
#[test]
fn zero_sized_slice_elements_allow_only_zero_offset_and_element_count_bounds() {
    let m = fixture();
    let t = Ty::FatPtr(FatPtrKind::Slice(TyId::new(3)));
    assert!(run(&m, &fat("zst", 0, Constant::Int(3)), &t).0.is_empty());
    for (offset, len) in [(1, 0), (0, 4), (-1, 0)] {
        assert!(matches!(
            &run(&m, &fat("zst", offset, Constant::Int(len)), &t).0[..],
            [ValidationError::PointerConstantRefused {
                reason: PointerConstantRefusal::WindowOutOfBounds { .. },
                ..
            }]
        ));
    }
}
#[test]
fn semantic_missing_layout_is_refusal_without_collapsing_operational_children() {
    let mut m = fixture();
    m.types.push(Ty::Tuple(vec![Ty::Bool]));
    m.globals.push(global(
        "tuple",
        Ty::Array(TyId::new(4), 1),
        Some(Constant::Uninit),
    ));
    let t = Ty::FatPtr(FatPtrKind::Slice(TyId::new(4)));
    assert!(matches!(
        &run(&m, &fat("tuple", 0, Constant::Int(1)), &t).0[..],
        [ValidationError::PointerConstantRefused {
            reason: PointerConstantRefusal::ElementLayoutUnknown,
            ..
        }]
    ));
}
