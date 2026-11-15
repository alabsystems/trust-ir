// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_mixed_operand_families_preserve_all_diagnostics_and_global_order() {
    let errors = parity(&fixture(), None);
    assert_eq!(errors.len(), 8);
    assert!(matches!(
        errors[0],
        ValidationError::OperandTypeMismatch { .. }
    ));
    assert!(matches!(
        errors[2],
        ValidationError::PointerMetadataTypeMismatch { .. }
    ));
    assert!(matches!(
        errors[3],
        ValidationError::CastOperandTypeMismatch { .. }
    ));
    assert!(matches!(
        errors[4],
        ValidationError::CastWidthDirectionInvalid { .. }
    ));
    assert!(matches!(
        errors[7],
        ValidationError::SelectConditionTypeMismatch { .. }
    ));
}
#[test]
fn first_pass_checks_each_physical_parameter_and_every_result_against_last_definition() {
    let invalid = Ty::Vector(Box::new(Ty::U32), 0);
    let mut f = function(vec![
        node(Inst::Undef { ty: Ty::U32 }, &[9, 10]),
        node(
            Inst::Undef {
                ty: invalid.clone(),
            },
            &[9, 10],
        ),
    ]);
    f.blocks[0].params.push((v(8), invalid));
    let errors = parity(&f, None);
    assert_eq!(errors.len(), 5);
    assert!(
        errors
            .iter()
            .all(|e| matches!(e, ValidationError::InvalidVectorType { block: 0, .. }))
    );
}
#[test]
fn declared_vector_second_pass_is_distinct_even_when_instruction_has_no_results() {
    let bad = Ty::Vector(Box::new(Ty::U32), 0);
    let f = function(vec![
        node(
            Inst::Alloca {
                ty: bad.clone(),
                count: None,
                align: Some(8),
            },
            &[],
        ),
        node(
            Inst::UnOp {
                op: UnOp::Neg,
                ty: bad,
                operand: v(99),
            },
            &[],
        ),
    ]);
    let errors = parity(&f, None);
    assert!(errors.len() >= 2);
    assert!(matches!(
        errors[0],
        ValidationError::InvalidVectorType { .. }
    ));
    assert!(matches!(
        errors[1],
        ValidationError::InvalidVectorType { .. }
    ));
}
#[test]
fn last_qualifying_constant_survives_noninteger_nonconstant_and_multi_result_redefinitions() {
    let f = function(vec![
        node(
            Inst::Const {
                ty: Ty::I128,
                value: Constant::Int(2),
            },
            &[6],
        ),
        node(
            Inst::Const {
                ty: Ty::I128,
                value: Constant::Int(-1),
            },
            &[6],
        ),
        node(
            Inst::Copy {
                ty: Ty::U32,
                operand: v(99),
            },
            &[6],
        ),
        node(
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Int(0),
            },
            &[6],
        ),
        node(
            Inst::Const {
                ty: Ty::I128,
                value: Constant::Int(1),
            },
            &[6, 7],
        ),
        node(
            Inst::ExtractElement {
                ty: Ty::U32,
                array: v(4),
                index: v(6),
            },
            &[],
        ),
    ]);
    let errors = parity(&f, None);
    assert!(
        matches!(errors.last(),Some(ValidationError::InvalidVectorElementOp{reason,..}) if reason=="constant lane index -1 is out of range for 4 lanes")
    );
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    seed_values(&mut s, &f, &mut work);
    s.first_pass(&f, &mut work).unwrap();
    assert_eq!(s.constants, vec![(6, -1)]);
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
}
#[test]
fn later_constant_updates_apply_even_to_element_uses_in_earlier_blocks() {
    let mut f = function(vec![node(
        Inst::ExtractElement {
            ty: Ty::U32,
            array: v(4),
            index: v(6),
        },
        &[],
    )]);
    let mut tail = Block::new(BlockId::new(8));
    tail.body = vec![node(
        Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(4),
        },
        &[6],
    )];
    f.blocks.push(tail);
    let errors = parity(&f, None);
    assert_eq!(errors.len(), 1);
    assert!(
        matches!(&errors[0],ValidationError::InvalidVectorElementOp{block:0,reason,..} if reason=="constant lane index 4 is out of range for 4 lanes")
    );
}
#[test]
fn complete_module_call_results_feed_scalar_consumers_without_unknown_exemption() {
    let mut module = Module::new("call-types");
    module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U32, Ty::Bool],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    module.functions.push(Function::new(
        FuncId::new(0),
        "callee",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    let f = function(vec![
        node(
            Inst::Call {
                callee: FuncId::new(0),
                args: vec![],
            },
            &[8, 9],
        ),
        node(
            Inst::UnOp {
                op: UnOp::Neg,
                ty: Ty::U32,
                operand: v(9),
            },
            &[],
        ),
    ]);
    assert!(parity(&f, None).is_empty());
    let errors = parity(&f, Some(&module));
    assert_eq!(errors.len(), 1);
    assert!(matches!(&errors[0],ValidationError::OperandTypeMismatch{actual,..} if actual=="bool"));
}
#[test]
fn module_mode_defers_only_layout_sensitive_compatibility_and_keeps_operand_checks() {
    let module = Module::new("layout-pass-separate");
    let f = function(vec![node(
        Inst::Cast {
            op: CastOp::Transmute,
            src_ty: Ty::I32,
            dst_ty: Ty::U32,
            operand: v(0),
        },
        &[],
    )]);
    assert!(matches!(
        parity(&f, None).as_slice(),
        [ValidationError::CastIncompatible { .. }]
    ));
    assert!(parity(&f, Some(&module)).is_empty());
    let f = function(vec![node(
        Inst::Cast {
            op: CastOp::Transmute,
            src_ty: Ty::U32,
            dst_ty: Ty::I32,
            operand: v(0),
        },
        &[],
    )]);
    assert!(matches!(
        parity(&f, Some(&module)).as_slice(),
        [ValidationError::CastOperandTypeMismatch { .. }]
    ));
}
#[test]
fn table_backed_element_checks_are_connected_with_original_module_context() {
    let mut module = Module::new("elements");
    module.types.push(Ty::U32);
    let mut f = function(vec![node(
        Inst::ExtractElement {
            ty: Ty::I32,
            array: v(8),
            index: v(3),
        },
        &[],
    )]);
    f.blocks[0].params.push((v(8), Ty::Array(TyId::new(0), 4)));
    assert!(parity(&f, None).is_empty());
    assert!(matches!(
        parity(&f, Some(&module)).as_slice(),
        [ValidationError::InvalidVectorElementOp { .. }]
    ));
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 2,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::default(),
    });
    let mut f = function(vec![node(
        Inst::PtrMetadata {
            ptr_ty: Ty::FatPtr(FatPtrKind::Str),
            metadata_ty: Ty::U16,
            ptr: v(8),
        },
        &[],
    )]);
    f.blocks[0].params.push((v(8), Ty::FatPtr(FatPtrKind::Str)));
    assert!(parity(&f, Some(&module)).is_empty());
    assert!(matches!(
        parity(&f, None).as_slice(),
        [ValidationError::PointerMetadataTypeMismatch { .. }]
    ));
}
#[test]
fn borrow_structure_then_rust_reference_tail_follow_all_operand_diagnostics() {
    let mut f = function(vec![
        node(Inst::BorrowMut { ptr: v(8) }, &[9]),
        node(Inst::EndBorrow { borrow_ptr: v(2) }, &[]),
        node(
            Inst::UnOp {
                op: UnOp::Neg,
                ty: Ty::U32,
                operand: v(0),
            },
            &[],
        ),
    ]);
    f.blocks[0].params.push((v(8), Ty::Ref(Box::new(Ty::U32))));
    f.producer = Some(Producer::TRust);
    let errors = parity(&f, None);
    assert!(matches!(
        errors[0],
        ValidationError::OperandTypeMismatch { .. }
    ));
    assert!(matches!(
        errors[1],
        ValidationError::BorrowMutThroughSharedRef { .. }
    ));
    assert!(matches!(
        errors[2],
        ValidationError::EndBorrowOfNonBorrow { .. }
    ));
    assert_eq!(errors.len(), 5);
}
#[test]
fn empty_function_and_ignored_families_keep_success_and_retire_context_before_publication() {
    for f in [
        Function::new(FuncId::new(121), "empty", FuncTyId::new(0), BlockId::new(0)),
        function(vec![
            node(Inst::NullPtr, &[8]),
            node(Inst::Return { values: vec![] }, &[]),
        ]),
    ] {
        let (errors, observer) = run(&f, None);
        assert!(errors.is_empty());
        assert!(parity(&f, None).is_empty());
        assert!(
            observer
                .events
                .iter()
                .any(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
        assert_eq!(
            observer.events.last().unwrap().phase,
            ExecutionPhase::Publication
        );
    }
}
