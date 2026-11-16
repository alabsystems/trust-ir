// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all17_opcodes_both_existing_modes_match_the_two_original_helpers_in_order() {
    let pairs = vec![
        (Ty::U32, Ty::U8),
        (Ty::U8, Ty::U32),
        (Ty::Bool, Ty::Char),
        (Ty::Char, Ty::Bool),
        (Ty::F16, Ty::F64),
        (Ty::F64, Ty::I32),
        (Ty::I32, Ty::F32),
        (Ty::Ptr, Ty::U64),
        (Ty::U64, Ty::Ptr),
        (Ty::Func(FuncTyId::new(9)), Ty::Ptr),
        (
            Ty::FatPtr(FatPtrKind::Str),
            Ty::FatPtr(FatPtrKind::ContainerLen),
        ),
        (Ty::Vector(Box::new(Ty::Bool), 8), Ty::U8),
        (handle(), Ty::Ptr),
        (Ty::Ref(Box::new(Ty::U32)), Ty::Ptr),
        (Ty::Tuple(vec![Ty::Bool]), Ty::U8),
        (
            Ty::Refine(TyId::new(0), trust_ir::value::PredId::new(0)),
            Ty::U32,
        ),
        (Ty::Vector(Box::new(Ty::U128), u32::MAX), Ty::U32),
        (Ty::Dialect(Box::new(DialectTy::new("v", "x", 1))), Ty::U32),
    ];
    for op in OPS {
        for mode in MODES {
            for (src, dst) in &pairs {
                parity(op, src, dst, &rows(Ty::I16), v(0), mode);
            }
        }
    }
}
#[test]
fn bool_identity_and_inequality_preserve_exact_reason_and_transmute_behavior() {
    assert!(
        parity(
            CastOp::Bitcast,
            &Ty::Bool,
            &Ty::Bool,
            &rows(Ty::Bool),
            v(0),
            MODES[0]
        )
        .is_empty()
    );
    assert!(matches!(
        parity(
            CastOp::Transmute,
            &Ty::Bool,
            &Ty::Bool,
            &rows(Ty::Bool),
            v(0),
            MODES[0]
        )[0],
        ValidationError::CastIncompatible { .. }
    ));
    for op in [CastOp::Bitcast, CastOp::Transmute] {
        let src = Ty::Vector(Box::new(Ty::Bool), 8);
        let errors = parity(op, &src, &Ty::U8, &rows(src.clone()), v(0), MODES[0]);
        assert_eq!(errors.len(), 1);
        assert!(
            matches!(&errors[0], ValidationError::CastLayoutUnsupported { reason,.. }
            if reason.starts_with("vector -> u8: a bool lane") && reason.ends_with("mask by comparing"))
        );
    }
}
#[test]
fn bool_reason_uses_exact_fixed_shape_names_and_dynamic_scalar_decimal_spelling() {
    for dst in [
        Ty::U8,
        Ty::I128,
        Ty::F16,
        Ty::F64,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
        Ty::Ptr,
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Unit,
        Ty::Never,
        Ty::Error,
        Ty::Tuple(vec![]),
        Ty::Vector(Box::new(Ty::U32), 0),
        Ty::Ref(Box::new(Ty::U8)),
        Ty::Func(FuncTyId::new(0)),
        handle(),
    ] {
        for op in [CastOp::Bitcast, CastOp::Transmute] {
            let errors = parity(op, &Ty::Bool, &dst, &rows(Ty::Bool), v(0), MODES[0]);
            assert_eq!(errors.len(), 1);
            assert!(matches!(
                errors[0],
                ValidationError::CastLayoutUnsupported { .. }
            ));
        }
    }
}
#[test]
fn mode_defers_only_compatibility_and_keeps_operand_matching_afterward() {
    for op in [
        CastOp::Bitcast,
        CastOp::Transmute,
        CastOp::PtrToPtr,
        CastOp::ReifyFnPointer,
    ] {
        let errors = parity(op, &Ty::Bool, &handle(), &rows(Ty::Ptr), v(0), MODES[1]);
        assert_eq!(errors.len(), 1);
        assert!(matches!(
            errors[0],
            ValidationError::CastOperandTypeMismatch { .. }
        ));
    }
}
#[test]
fn bool_char_integer_width_checks_keep_operand_before_direction_diagnostics() {
    for op in [CastOp::Trunc, CastOp::ZExt, CastOp::SExt] {
        for mode in MODES {
            for (src, dst) in [
                (Ty::Bool, Ty::Char),
                (Ty::Char, Ty::Bool),
                (Ty::U32, Ty::I32),
                (Ty::Isize, Ty::Usize),
                (
                    Ty::Vector(Box::new(Ty::U32), 2),
                    Ty::Vector(Box::new(Ty::U32), 4),
                ),
            ] {
                parity(op, &src, &dst, &rows(Ty::Ptr), v(0), mode);
            }
        }
    }
    let errors = parity(
        CastOp::Trunc,
        &Ty::Bool,
        &Ty::U128,
        &rows(Ty::Ptr),
        v(0),
        MODES[0],
    );
    assert_eq!(errors.len(), 2);
    assert!(matches!(
        errors[0],
        ValidationError::CastOperandTypeMismatch { .. }
    ));
    assert!(
        matches!(&errors[1], ValidationError::CastWidthDirectionInvalid { reason,.. }
        if reason=="trunc requires src width (1) > dst width (128)")
    );
}
#[test]
fn pointer_metadata_identity_and_function_width_fallback_match_original_rules() {
    let kinds = [
        FatPtrKind::Str,
        FatPtrKind::Slice(TyId::new(0)),
        FatPtrKind::TraitObject { trait_id: 9 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ];
    for from in kinds {
        for to in kinds {
            for op in [CastOp::PtrToPtr, CastOp::Bitcast] {
                let src = Ty::FatPtr(from);
                let dst = Ty::FatPtr(to);
                parity(op, &src, &dst, &rows(src.clone()), v(0), MODES[0]);
            }
        }
    }
    for dst in [
        Ty::Ptr,
        Ty::U64,
        Ty::Ref(Box::new(Ty::U8)),
        Ty::FatPtr(FatPtrKind::Str),
    ] {
        for op in [CastOp::Bitcast, CastOp::PtrToPtr, CastOp::ReifyFnPointer] {
            let src = Ty::Func(FuncTyId::new(0));
            parity(op, &src, &dst, &rows(src.clone()), v(0), MODES[0]);
        }
    }
}
#[test]
fn inline_handle_guard_traverses_pointer_children_and_nominal_ids_stay_opaque() {
    for src in [
        handle(),
        Ty::Ref(Box::new(handle())),
        Ty::Tuple(vec![Ty::U32, handle()]),
        Ty::Array(TyId::new(0), 1),
        Ty::Refine(TyId::new(0), trust_ir::value::PredId::new(0)),
    ] {
        for op in [CastOp::PtrToPtr, CastOp::Bitcast, CastOp::FPToUISat] {
            for mode in MODES {
                parity(op, &src, &Ty::Ptr, &rows(src.clone()), v(0), mode);
            }
        }
    }
}
#[test]
fn unknown_operand_and_unknown_or_overflow_widths_do_not_invent_extra_errors() {
    for (src, dst) in [
        (Ty::Ptr, Ty::U8),
        (Ty::Usize, Ty::Isize),
        (
            Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::U128), u32::MAX)), 0),
            Ty::U8,
        ),
        (
            Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::U128), 0)), u32::MAX),
            Ty::U8,
        ),
    ] {
        for op in [CastOp::Trunc, CastOp::ZExt, CastOp::SExt, CastOp::Bitcast] {
            parity(op, &src, &dst, &[], v(99), MODES[0]);
        }
    }
}
#[test]
fn last_definition_map_and_refinements_keep_exact_full_operand_identity() {
    let entries = vec![(v(0), Ty::U8), (v(0), Ty::U32)];
    assert!(parity(CastOp::ZExt, &Ty::U32, &Ty::U64, &entries, v(0), MODES[0]).is_empty());
    let refined = Ty::Refine(TyId::new(0), trust_ir::value::PredId::new(0));
    parity(
        CastOp::Trunc,
        &refined,
        &Ty::U8,
        &rows(refined.clone()),
        v(0),
        MODES[0],
    );
    let errors = parity(
        CastOp::Trunc,
        &Ty::U32,
        &Ty::U8,
        &rows(refined),
        v(0),
        MODES[0],
    );
    assert!(matches!(
        errors[0],
        ValidationError::CastOperandTypeMismatch { .. }
    ));
}
#[test]
fn malformed_unicode_type_spelling_is_diagnostic_text_without_validation_or_normalization() {
    let src = Ty::Tuple(vec![
        handle(),
        Ty::Dialect(Box::new(DialectTy::new("λ\0", "raw\n", u32::MAX))),
    ]);
    for mode in MODES {
        parity(CastOp::FPToSI, &src, &Ty::F32, &rows(handle()), v(0), mode);
    }
}
#[test]
fn bounded_decimal_and_all17_opcode_spellings_match_original_display() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    for number in [0, 1, 9, 10, 127, 128, 999_999_999, u32::MAX] {
        let mut text = String::new();
        work.decimal(number, &mut text).unwrap();
        assert_eq!(text, number.to_string());
        work.flat(text);
    }
    for op in OPS {
        assert_eq!(work.opcode(op).unwrap(), op.to_string());
    }
}

#[test]
fn nominal_item_explicit_zero_byte_casts_and_reification_match_current_rules() {
    let one = Ty::FnItem(FuncId::new(7));
    let two = Ty::FnItem(FuncId::new(42));
    for op in [CastOp::Bitcast, CastOp::Transmute] {
        for (src, dst) in [(&one, &two), (&one, &Ty::Unit), (&Ty::Unit, &two)] {
            assert!(parity(op, src, dst, &rows(src.clone()), v(0), MODES[0]).is_empty());
        }
    }
    assert!(
        parity(
            CastOp::ReifyFnPointer,
            &one,
            &Ty::Func(FuncTyId::new(0)),
            &rows(one.clone()),
            v(0),
            MODES[0]
        )
        .is_empty()
    );
}
