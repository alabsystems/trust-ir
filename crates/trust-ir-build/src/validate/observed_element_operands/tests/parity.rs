// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn missing_and_invalid_aggregate_still_check_index_types_without_range_errors() {
    for kind in [Kind::Extract, Kind::Insert] {
        for aggregate in [None, Some(Ty::Struct(StructId::new(0))), Some(Ty::U32)] {
            let known = aggregate.is_some();
            let function = fixture(kind, aggregate, Some(Ty::Bool), Some(Ty::F32), Ty::U32);
            let errors = parity(&function, &[(1, -1)], None);
            assert_eq!(errors.len(), if known { 2 } else { 1 });
            assert_eq!(
                reasons(&errors).last(),
                Some(&"index must be integer, got bool")
            );
            assert!(
                reasons(&errors)
                    .iter()
                    .all(|reason| !reason.contains("negative") && !reason.contains("range"))
            );
        }
    }
}

#[test]
fn insert_result_lane_index_type_and_range_have_exact_order_and_text() {
    let errors = parity(&failing(), &[(1, -1)], None);
    assert_eq!(
        reasons(&errors),
        vec![
            "result type must match operand type <2 x u32>, got <2 x f32>",
            "inserted value must match vector lane type u32, got i32",
            "index must be integer, got bool",
            "constant lane index -1 is out of range for 2 lanes",
        ]
    );
}

#[test]
fn vector_zero_max_counts_and_i128_min_max_indices_match_ordinary_signed_spelling() {
    for lanes in [0, 1, u32::MAX] {
        for index in [i128::MIN, -1, 0, 1, i128::from(lanes), i128::MAX] {
            let vector = Ty::Vector(Box::new(Ty::U32), lanes);
            for kind in [Kind::Extract, Kind::Insert] {
                let declared = match kind {
                    Kind::Extract => Ty::U32,
                    Kind::Insert => vector.clone(),
                };
                let function = fixture(
                    kind,
                    Some(vector.clone()),
                    Some(Ty::U128),
                    Some(Ty::U32),
                    declared,
                );
                let errors = parity(&function, &[(1, index)], None);
                assert_eq!(
                    errors.len(),
                    usize::from(index < 0 || index >= i128::from(lanes))
                );
                if let Some(reason) = reasons(&errors).first() {
                    assert!(reason.contains(&index.to_string()));
                }
            }
        }
    }
}

#[test]
fn array_count_narrowing_is_exact_including_lengths_larger_than_u32_max() {
    let module = module();
    for length in [0, 1, u64::from(u32::MAX), u64::from(u32::MAX) + 1, u64::MAX] {
        for index in [i128::MIN, -1, 0, i128::from(u32::MAX), i128::MAX] {
            let array = Ty::Array(TyId::new(0), length);
            for kind in [Kind::Extract, Kind::Insert] {
                let declared = match kind {
                    Kind::Extract => Ty::U32,
                    Kind::Insert => array.clone(),
                };
                let function = fixture(
                    kind,
                    Some(array.clone()),
                    Some(Ty::Usize),
                    Some(Ty::U32),
                    declared,
                );
                let errors = parity(&function, &[(1, index)], Some(&module));
                assert_eq!(
                    errors.len(),
                    usize::from(
                        index < 0 || (length <= u64::from(u32::MAX) && index >= i128::from(length))
                    )
                );
                if length > u64::from(u32::MAX) && index < 0 {
                    let expected = format!("constant element index {index} is negative");
                    assert_eq!(reasons(&errors), vec![expected.as_str()]);
                }
            }
        }
    }
}

#[test]
fn sequence_signed_type_then_negative_constant_and_unknown_type_exemptions_are_exact() {
    let module = module();
    for index_ty in [
        None,
        Some(Ty::I32),
        Some(Ty::Usize),
        Some(Ty::Bool),
        Some(Ty::Refine(TyId::new(0), PredId::new(0))),
    ] {
        for constant in [None, Some(-1), Some(i128::MAX)] {
            let function = fixture(
                Kind::Extract,
                Some(Ty::Sequence(TyId::new(0))),
                index_ty.clone(),
                None,
                Ty::U32,
            );
            let rows = constant.map(|value| vec![(1, value)]).unwrap_or_default();
            let errors = parity(&function, &rows, Some(&module));
            let type_error = usize::from(
                index_ty
                    .as_ref()
                    .is_some_and(|ty| !ty.is_integer() || ty.is_signed()),
            );
            assert_eq!(errors.len(), type_error + usize::from(constant == Some(-1)));
        }
    }
    let function = fixture(
        Kind::Extract,
        Some(Ty::Sequence(TyId::new(0))),
        Some(Ty::I32),
        None,
        Ty::U32,
    );
    assert_eq!(
        reasons(&parity(&function, &[(1, -1)], Some(&module))),
        vec![
            "a sequence index must be an unsigned integer (a sequence has no static length, so non-negativity is decidable only from the index type), got i32",
            "constant element index -1 is negative",
        ]
    );
}

#[test]
fn table_types_require_module_resolution_and_unknown_insert_values_do_not_invent_demands() {
    let module = module();
    for aggregate in [
        Ty::Sequence(TyId::new(0)),
        Ty::Array(TyId::new(0), 3),
        Ty::Sequence(TyId::new(u32::MAX)),
        Ty::Array(TyId::new(u32::MAX), 3),
    ] {
        for kind in [Kind::Extract, Kind::Insert] {
            let declared = match kind {
                Kind::Extract => Ty::I32,
                Kind::Insert => aggregate.clone(),
            };
            let function = fixture(
                kind,
                Some(aggregate.clone()),
                Some(Ty::U32),
                Some(Ty::I32),
                declared,
            );
            assert_eq!(parity(&function, &[], Some(&module)).len(), 1);
            assert!(parity(&function, &[], None).is_empty());
        }
    }
    let array = Ty::Array(TyId::new(u32::MAX), 3);
    let function = fixture(
        Kind::Insert,
        Some(array.clone()),
        Some(Ty::U32),
        None,
        array,
    );
    assert!(parity(&function, &[], Some(&module)).is_empty());
}

#[test]
fn refinement_consumption_exemptions_do_not_weaken_insert_result_identity() {
    let module = module();
    let refine = Ty::Refine(TyId::new(0), PredId::new(1));
    for lane in [Ty::U32, refine.clone()] {
        for demand in [Ty::I32, refine.clone()] {
            let vector = Ty::Vector(Box::new(lane.clone()), 3);
            let extract = fixture(
                Kind::Extract,
                Some(vector.clone()),
                None,
                None,
                demand.clone(),
            );
            let expected = usize::from(
                !matches!(lane, Ty::Refine(..))
                    && !matches!(demand, Ty::Refine(..))
                    && lane != demand,
            );
            assert_eq!(parity(&extract, &[], Some(&module)).len(), expected);
            let insert = fixture(
                Kind::Insert,
                Some(vector.clone()),
                None,
                Some(demand.clone()),
                refine.clone(),
            );
            assert_eq!(parity(&insert, &[], Some(&module)).len(), expected + 1);
        }
    }
    for element in [0, 2] {
        let function = fixture(
            Kind::Extract,
            Some(Ty::Array(TyId::new(element), 2)),
            None,
            None,
            refine.clone(),
        );
        assert!(parity(&function, &[], Some(&module)).is_empty());
    }
}

#[test]
fn nested_lane_identity_and_unicode_diagnostics_match_complete_original_helpers() {
    let mut lane = Ty::Tuple(vec![
        Ty::Handle(Box::new(HandleTy::new("λ'\n", "runtime\0"))),
        Ty::U32,
    ]);
    let mut other = Ty::Tuple(vec![
        Ty::Handle(Box::new(HandleTy::new("λ'\n", "runtime\0"))),
        Ty::I32,
    ]);
    for _ in 0..96 {
        lane = Ty::Ref(Box::new(lane));
        other = Ty::Ref(Box::new(other));
    }
    let vector = Ty::Vector(Box::new(lane.clone()), 2);
    let extract = fixture(
        Kind::Extract,
        Some(vector.clone()),
        Some(Ty::U32),
        None,
        other.clone(),
    );
    assert_eq!(parity(&extract, &[], None).len(), 1);
    let insert = fixture(
        Kind::Insert,
        Some(vector.clone()),
        Some(Ty::U32),
        Some(other),
        vector,
    );
    assert_eq!(parity(&insert, &[], None).len(), 1);
}

#[test]
fn aggregate_refinements_are_not_expanded_and_nominal_elements_keep_exact_identities() {
    let mut module = module();
    module.types = vec![
        Ty::Vector(Box::new(Ty::U32), 4),
        Ty::Struct(StructId::new(0)),
    ];
    let function = fixture(
        Kind::Extract,
        Some(Ty::Refine(TyId::new(0), PredId::new(0))),
        Some(Ty::U32),
        None,
        Ty::U32,
    );
    assert_eq!(parity(&function, &[(1, -1)], Some(&module)).len(), 1);
    for declared in [Ty::Struct(StructId::new(0)), Ty::Struct(StructId::new(1))] {
        let expected = usize::from(declared != Ty::Struct(StructId::new(0)));
        let function = fixture(
            Kind::Extract,
            Some(Ty::Array(TyId::new(1), 4)),
            Some(Ty::U32),
            None,
            declared,
        );
        assert_eq!(parity(&function, &[], Some(&module)).len(), expected);
    }
}

#[test]
fn constants_keep_last_qualifying_definition_across_nonconstant_redefinitions() {
    let mut function = fixture(
        Kind::Extract,
        Some(Ty::Vector(Box::new(Ty::U32), 4)),
        Some(Ty::U32),
        None,
        Ty::U32,
    );
    function.blocks[0].body.splice(
        0..0,
        [
            InstrNode::new(Inst::Const {
                ty: Ty::I128,
                value: Constant::Int(2),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::I128,
                value: Constant::Int(-1),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Copy {
                ty: Ty::U32,
                operand: v(999),
            })
            .with_result(v(1)),
            // Noninteger Const is not a qualifying update either.
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        ],
    );
    let actual = parity(&function, &[(1, 2), (1, -1)], None);
    let full = super::super::super::validate_types(
        &function,
        ValidationContext {
            cast_mode: CastValidationMode::FunctionOnly,
            pointer_bits: DEFAULT_POINTER_BITS,
            module: None,
        },
    )
    .into_iter()
    .filter(|error| matches!(error, ValidationError::InvalidVectorElementOp { .. }))
    .collect::<Vec<_>>();
    assert_eq!(actual, full);
    assert_eq!(
        reasons(&actual),
        vec![
            "index must be integer, got bool",
            "constant lane index -1 is out of range for 4 lanes"
        ]
    );
}

#[test]
fn wrong_instruction_family_is_typed_operational_refusal() {
    let function = failing();
    let values = values(&function, None);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_element_operands_observed(
            0,
            &Inst::NullPtr,
            &values,
            &[],
            None,
            &mut session,
            site()
        ),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(session.first_refusal().is_none());
}
