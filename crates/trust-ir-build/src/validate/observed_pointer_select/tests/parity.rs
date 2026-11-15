// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_four_families_preserve_diagnostic_order_and_valid_routes() {
    let errors = parity(&fixture(), 64);
    assert_eq!(errors.len(), 3);
    assert!(matches!(&errors[0],ValidationError::OperandTypeMismatch{role,..} if role=="data"));
    assert!(matches!(&errors[1],ValidationError::OperandTypeMismatch{role,..} if role=="metadata"));
    assert!(matches!(
        &errors[2],
        ValidationError::PointerMetadataTypeMismatch { .. }
    ));
    for inst in [
        Inst::PtrData {
            ptr_ty: Ty::Ptr,
            ptr: v(0),
        },
        Inst::PtrMetadata {
            ptr_ty: Ty::FatPtr(FatPtrKind::Str),
            metadata_ty: Ty::U64,
            ptr: v(4),
        },
        Inst::PtrFromParts {
            ptr_ty: Ty::FatPtr(FatPtrKind::Str),
            metadata_ty: Ty::U64,
            data: v(0),
            metadata: v(3),
        },
        Inst::Select {
            ty: Ty::I32,
            cond: v(2),
            then_val: v(1),
            else_val: v(1),
        },
    ] {
        assert!(parity(&function(inst), 64).is_empty());
    }
}
#[test]
fn all_fat_kinds_and_supported_and_unsupported_pointer_widths_match_metadata_classifier() {
    for kind in [
        FatPtrKind::Str,
        FatPtrKind::Slice(TyId::new(7)),
        FatPtrKind::TraitObject { trait_id: 9 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ] {
        for bits in [0, 8, 16, 32, 64, 128, u32::MAX] {
            let ty = Ty::FatPtr(kind);
            let metadata = ty.pointer_metadata_ty(bits).unwrap_or(Ty::U16);
            assert!(matches!(
                &metadata,
                Ty::Unit | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 | Ty::Ptr
            ));
            let mut f = function(Inst::PtrMetadata {
                ptr_ty: ty.clone(),
                metadata_ty: metadata,
                ptr: v(4),
            });
            f.blocks[0].params[4].1 = ty;
            let errors = parity(&f, bits);
            if matches!(
                kind,
                FatPtrKind::TraitObject { .. } | FatPtrKind::ContainerVtable
            ) || [8, 16, 32, 64, 128].contains(&bits)
            {
                assert!(errors.is_empty());
            } else {
                assert!(matches!(
                    errors.as_slice(),
                    [ValidationError::PointerOpInvalid { .. }]
                ));
            }
        }
    }
}
#[test]
fn thin_pointer_kinds_have_unit_metadata_and_invalid_declared_types_keep_both_errors() {
    for ty in [
        Ty::Ptr,
        Ty::Ref(Box::new(Ty::U32)),
        Ty::RefMut(Box::new(Ty::U32)),
        Ty::PtrConst(Box::new(Ty::U32)),
        Ty::PtrMut(Box::new(Ty::U32)),
        Ty::Rc(Box::new(Ty::U32)),
        Ty::Func(FuncTyId::new(1)),
    ] {
        let mut f = function(Inst::PtrMetadata {
            ptr_ty: ty.clone(),
            metadata_ty: Ty::Unit,
            ptr: v(4),
        });
        f.blocks[0].params[4].1 = ty;
        assert!(parity(&f, 0).is_empty());
    }
    let errors = parity(
        &function(Inst::PtrData {
            ptr_ty: Ty::U64,
            ptr: v(0),
        }),
        64,
    );
    assert!(
        matches!(errors.as_slice(),[ValidationError::OperandTypeMismatch{..},ValidationError::PointerOpInvalid{reason,..}] if reason=="type is not pointer-like")
    );
}
#[test]
fn logical_vector_masks_physical_integer_masks_and_wrong_lanes_keep_exact_pair() {
    for lanes in [0, 4, 5] {
        let mut f = function(Inst::Select {
            ty: Ty::Vector(Box::new(Ty::I32), lanes),
            cond: v(6),
            then_val: v(7),
            else_val: v(7),
        });
        f.blocks[0].params[7].1 = Ty::Vector(Box::new(Ty::I32), lanes);
        f.blocks[0].params[6].1 = Ty::Vector(Box::new(Ty::Bool), lanes);
        assert!(parity(&f, 64).is_empty());
        f.blocks[0].params[6].1 = Ty::Vector(Box::new(Ty::U32), lanes);
        assert!(matches!(
            parity(&f, 64).as_slice(),
            [ValidationError::SelectConditionTypeMismatch { .. }]
        ));
        f.blocks[0].params[6].1 = Ty::Vector(Box::new(Ty::Bool), lanes + 1);
        assert!(matches!(
            parity(&f, 64).as_slice(),
            [ValidationError::SelectConditionTypeMismatch { .. }]
        ));
    }
}
#[test]
fn unknown_operands_only_skip_the_original_lookup_dependent_checks() {
    for inst in [
        Inst::PtrData {
            ptr_ty: Ty::U32,
            ptr: v(99),
        },
        Inst::PtrMetadata {
            ptr_ty: Ty::U32,
            metadata_ty: Ty::U64,
            ptr: v(99),
        },
        Inst::PtrFromParts {
            ptr_ty: Ty::U32,
            metadata_ty: Ty::U64,
            data: v(99),
            metadata: v(98),
        },
    ] {
        assert_eq!(parity(&function(inst), 64).len(), 1);
    }
    assert!(
        parity(
            &function(Inst::Select {
                ty: Ty::U32,
                cond: v(99),
                then_val: v(98),
                else_val: v(97)
            }),
            64
        )
        .is_empty()
    );
}
#[test]
fn outer_refine_is_never_exempted_for_pointer_words_or_selected_values() {
    let refined = Ty::Refine(TyId::new(0), PredId::new(0));
    let errors = parity(
        &function(Inst::PtrFromParts {
            ptr_ty: refined.clone(),
            metadata_ty: Ty::U64,
            data: v(5),
            metadata: v(5),
        }),
        64,
    );
    assert_eq!(errors.len(), 3);
    let errors = parity(
        &function(Inst::Select {
            ty: refined,
            cond: v(5),
            then_val: v(1),
            else_val: v(1),
        }),
        64,
    );
    assert_eq!(errors.len(), 3);
}
#[test]
fn structural_comparisons_and_unicode_diagnostic_spelling_match_original() {
    let ty = Ty::Tuple(vec![
        Ty::Handle(Box::new(HandleTy::new("λ\n\0", "runtime")));
        12
    ]);
    let mut f = function(Inst::Select {
        ty,
        cond: v(3),
        then_val: v(1),
        else_val: v(2),
    });
    assert_eq!(parity(&f, 64).len(), 3);
    f.blocks[0].params[1].1 = Ty::Tuple(vec![Ty::U32; 12]);
    assert_eq!(parity(&f, 64).len(), 3);
}
#[test]
fn wrong_instruction_family_is_typed_refusal_not_empty_diagnostics() {
    let f = function(Inst::Copy {
        ty: Ty::I32,
        operand: v(1),
    });
    let values = values(&f);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_pointer_select_operands_observed(
            0,
            &f.blocks[0].body[0].inst,
            &values,
            64,
            &mut session,
            site()
        ),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(session.first_refusal().is_none());
    assert!(
        observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
