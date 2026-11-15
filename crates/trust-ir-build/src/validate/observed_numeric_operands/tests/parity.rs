// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn all26_binary_tokens_and_scalar_vector_category_cells_match_the_ordinary_pass() {
    for op in BINARY {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        assert_eq!(tokens::binary(op, &mut work).unwrap(), op.to_string());
        for ty in categories() {
            parity(
                &f(Inst::BinOp {
                    op,
                    ty,
                    lhs: v(999),
                    rhs: v(999),
                }),
                None,
            );
        }
    }
}

#[test]
fn all13_unary_tokens_categories_and_scalar_bool_not_keep_their_original_refusal() {
    for op in UNARY {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        assert_eq!(tokens::unary(op, &mut work).unwrap(), op.to_string());
        for ty in categories() {
            parity(
                &f(Inst::UnOp {
                    op,
                    ty,
                    operand: v(999),
                }),
                None,
            );
        }
    }
    assert_eq!(
        parity(
            &f(Inst::UnOp {
                op: UnOp::Not,
                ty: Ty::Bool,
                operand: v(2)
            }),
            None
        ),
        vec![ValidationError::UnOpNotOnScalarBool { block: 0 }]
    );
    let errors = parity(
        &f(Inst::UnOp {
            op: UnOp::Not,
            ty: Ty::Bool,
            operand: v(0),
        }),
        None,
    );
    assert_eq!(errors.len(), 2);
    assert!(matches!(
        errors[1],
        ValidationError::UnOpNotOnScalarBool { block: 0 }
    ));
    assert!(
        parity(
            &f(Inst::UnOp {
                op: UnOp::Not,
                ty: Ty::Vector(Box::new(Ty::Bool), 4),
                operand: v(999)
            }),
            None
        )
        .is_empty()
    );
}

#[test]
fn actual_pair_lhs_rhs_and_category_diagnostics_have_exact_original_order_and_payloads() {
    let errors = parity(&fixture(), None);
    assert_eq!(errors.len(), 4);
    assert!(matches!(
        errors[0],
        ValidationError::BinOpTypeMismatch { .. }
    ));
    assert!(matches!(&errors[1],ValidationError::OperandTypeMismatch {role,..} if role=="lhs"));
    assert!(matches!(&errors[2],ValidationError::OperandTypeMismatch {role,..} if role=="rhs"));
    assert!(matches!(
        errors[3],
        ValidationError::BinOpRequiresInteger { .. }
    ));
    for inst in [
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::F32,
            lhs: v(1),
            rhs: v(2),
        },
        Inst::FCmp {
            op: FCmpOp::OEq,
            ty: Ty::U32,
            lhs: v(1),
            rhs: v(2),
        },
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::F32,
            lhs: v(1),
            rhs: v(2),
        },
    ] {
        assert_eq!(parity(&f(inst), None).len(), 4);
    }
}

#[test]
fn binary_representation_peels_one_exact_base_without_erasing_recorded_refinement_names() {
    let module = module();
    for declared in [
        Ty::U32,
        Ty::F32,
        Ty::Refine(TyId::new(0), PredId::new(9)),
        Ty::Refine(TyId::new(1), PredId::new(0)),
        Ty::Refine(TyId::new(99), PredId::new(0)),
        Ty::Refine(TyId::new(2), PredId::new(0)),
    ] {
        for (lhs, rhs) in [(v(6), v(7)), (v(6), v(8)), (v(0), v(1)), (v(999), v(6))] {
            let function = f(Inst::BinOp {
                op: BinOp::Add,
                ty: declared.clone(),
                lhs,
                rhs,
            });
            parity(&function, Some(&module));
            parity(&function, None);
        }
    }
    assert!(
        parity(
            &f(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U32,
                lhs: v(6),
                rhs: v(7)
            }),
            Some(&module)
        )
        .is_empty()
    );
    let errors = parity(
        &f(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: v(6),
            rhs: v(8),
        }),
        Some(&module),
    );
    assert!(
        matches!(&errors[0],ValidationError::BinOpTypeMismatch {lhs_ty,rhs_ty,..} if lhs_ty==&Ty::Refine(TyId::new(0),PredId::new(0)).to_string() && rhs_ty==&Ty::Refine(TyId::new(1),PredId::new(0)).to_string())
    );
}

#[test]
fn comparison_identity_stays_strict_and_char_ptr_bool_zero_and_nested_vectors_match_original() {
    let module = module();
    for ty in categories().into_iter().chain([
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Ref(Box::new(Ty::U32)),
    ]) {
        for inst in [
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: ty.clone(),
                lhs: v(6),
                rhs: v(7),
            },
            Inst::FCmp {
                op: FCmpOp::OEq,
                ty,
                lhs: v(6),
                rhs: v(7),
            },
        ] {
            parity(&f(inst), Some(&module));
        }
    }
    for (ty, value) in [(Ty::Char, v(4)), (Ty::Ptr, v(5)), (Ty::Bool, v(2))] {
        assert!(
            parity(
                &f(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty,
                    lhs: value,
                    rhs: value
                }),
                None
            )
            .is_empty()
        );
    }
}

#[test]
fn all_overflow_tokens_require_integer_and_never_gain_binary_refinement_deferral() {
    let module = module();
    for op in [
        OverflowOp::AddOverflow,
        OverflowOp::SubOverflow,
        OverflowOp::MulOverflow,
    ] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        assert_eq!(tokens::overflow(op, &mut work).unwrap(), op.to_string());
        for ty in categories()
            .into_iter()
            .chain([Ty::Refine(TyId::new(0), PredId::new(9))])
        {
            parity(
                &f(Inst::Overflow {
                    op,
                    ty,
                    lhs: v(6),
                    rhs: v(7),
                }),
                Some(&module),
            );
        }
    }
}

#[test]
fn missing_bases_and_unknown_values_do_not_hide_declared_category_checks_or_invent_authority() {
    let module = module();
    assert_eq!(
        parity(
            &f(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::F32,
                lhs: v(999),
                rhs: v(999)
            }),
            None
        )
        .len(),
        1
    );
    assert!(
        parity(
            &f(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::Refine(TyId::new(99), PredId::new(0)),
                lhs: v(6),
                rhs: v(999)
            }),
            Some(&module)
        )
        .is_empty()
    );
    // The original separate refinement-surface pass owns this standalone
    // refusal; an empty numeric constituent never licenses that function.
    let function = f(Inst::BinOp {
        op: BinOp::Add,
        ty: Ty::U32,
        lhs: v(6),
        rhs: v(0),
    });
    assert!(parity(&function, None).is_empty());
    assert!(!super::super::super::validate_standalone_refinement_surface(&function).is_empty());
}

#[test]
fn complete_last_definition_map_fat_types_and_nested_unicode_spellings_are_preserved() {
    let mut function = f(Inst::UnOp {
        op: UnOp::Neg,
        ty: Ty::U32,
        operand: v(0),
    });
    function.blocks[0].params.push((v(0), Ty::I32));
    assert_eq!(parity(&function, None).len(), 1);
    let ty = Ty::Tuple(vec![Ty::Handle(Box::new(HandleTy::new(
        "λ'\n",
        "runtime\0",
    )))]);
    function.blocks[0].params[0].1 = ty;
    function.blocks[0].params.pop();
    assert_eq!(parity(&function, None).len(), 1);
    let function = f(Inst::BinOp {
        op: BinOp::Add,
        ty: Ty::FatPtr(FatPtrKind::Str),
        lhs: v(9),
        rhs: v(9),
    });
    assert_eq!(parity(&function, None).len(), 1);
}

#[test]
fn actual_borrow_correction_from_the_complete_map_is_used_by_a_numeric_consumer() {
    let mut function = f(Inst::UnOp {
        op: UnOp::Neg,
        ty: Ty::U32,
        operand: v(20),
    });
    function.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Borrow { ptr: v(9) }).with_result(v(20)),
    );
    let values = values(&function, None);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual = validate_instruction_numeric_type_operands_observed(
        0,
        &function.blocks[0].body[1].inst,
        &values,
        None,
        &mut session,
        site(),
    )
    .unwrap();
    let ordinary = super::super::super::validate_types(
        &function,
        ValidationContext {
            cast_mode: CastValidationMode::FunctionOnly,
            pointer_bits: DEFAULT_POINTER_BITS,
            module: None,
        },
    );
    assert_eq!(
        actual,
        ordinary.into_iter().filter(included).collect::<Vec<_>>()
    );
    assert_eq!(actual.len(), 1);
    assert!(
        matches!(&actual[0],ValidationError::OperandTypeMismatch {actual,..} if actual=="fatptr<str>")
    );
}
