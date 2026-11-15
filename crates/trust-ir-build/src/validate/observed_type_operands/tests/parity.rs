// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn cmpxchg_keeps_pointer_failure_ordering_expected_desired_diagnostic_order() {
    let errors = parity(&fixture(), None);
    assert_eq!(errors.len(), 4);
    assert!(matches!(&errors[0],ValidationError::OperandNotPointer {op,..} if op=="cmpxchg"));
    assert!(
        matches!(&errors[1],ValidationError::IllegalAtomicOrdering {role:"failure ordering",ordering,..} if ordering=="release")
    );
    assert!(
        matches!(&errors[2],ValidationError::OperandTypeMismatch {role,..} if role=="expected")
    );
    assert!(matches!(&errors[3],ValidationError::OperandTypeMismatch {role,..} if role=="desired"));
}

#[test]
fn proved_atomic_tables_and_all_success_failure_strengths_keep_original_rules() {
    for ordering in [
        Ordering::Relaxed,
        Ordering::Acquire,
        Ordering::Release,
        Ordering::AcqRel,
        Ordering::SeqCst,
    ] {
        for inst in [
            Inst::AtomicLoad {
                ty: Ty::U32,
                ptr: v(0),
                ordering,
            },
            Inst::AtomicStore {
                ty: Ty::U32,
                ptr: v(0),
                value: v(1),
                ordering,
            },
            Inst::AtomicRMW {
                op: AtomicRMWOp::Xchg,
                ty: Ty::U32,
                ptr: v(0),
                value: v(1),
                ordering,
            },
            Inst::Fence { ordering },
        ] {
            parity(&f(inst), None);
        }
        for success in [
            Ordering::Relaxed,
            Ordering::Acquire,
            Ordering::Release,
            Ordering::AcqRel,
            Ordering::SeqCst,
        ] {
            for weak in [false, true] {
                parity(
                    &f(Inst::CmpXchg {
                        ty: Ty::U32,
                        ptr: v(0),
                        expected: v(1),
                        desired: v(1),
                        success,
                        failure: ordering,
                        weak,
                    }),
                    None,
                );
            }
        }
    }
}

#[test]
fn every_pointer_consumer_accepts_exact_original_pointer_like_types_only() {
    for ty in [
        Ty::Ptr,
        Ty::Ref(Box::new(Ty::U32)),
        Ty::RefMut(Box::new(Ty::U32)),
        Ty::PtrConst(Box::new(Ty::U32)),
        Ty::PtrMut(Box::new(Ty::U32)),
        Ty::Rc(Box::new(Ty::U32)),
        Ty::Func(FuncTyId::new(2)),
        Ty::FatPtr(FatPtrKind::Str),
        Ty::U32,
        Ty::Refine(TyId::new(0), PredId::new(0)),
    ] {
        for inst in [
            Inst::Load {
                ty: Ty::U32,
                ptr: v(0),
                volatile: false,
                align: None,
            },
            Inst::Dealloc { ptr: v(0) },
            Inst::Borrow { ptr: v(0) },
            Inst::BorrowMut { ptr: v(0) },
            Inst::EndBorrow { borrow_ptr: v(0) },
            Inst::Retain { ptr: v(0) },
            Inst::Release { ptr: v(0) },
            Inst::IsUnique { ptr: v(0) },
            Inst::CoroSuspend {
                frame: v(0),
                state_slot: 0,
                next_state: 1,
                value: v(1),
            },
        ] {
            let mut function = f(inst);
            function.blocks[0].params[0].1 = ty.clone();
            let errors = parity(&function, None);
            assert_eq!(errors.len(), usize::from(!ty.is_pointer_like()));
        }
    }
}

#[test]
fn bulk_count_context_and_byte_pointer_roles_are_exact_and_do_not_defer_refinements() {
    let mut plain = Module::new("plain");
    plain.types.push(Ty::Usize);
    let mut pinned = plain.clone();
    target(&mut pinned);
    for module in [None, Some(&plain), Some(&pinned)] {
        for bytes in [v(4), v(5), v(1), v(7), v(999)] {
            parity(
                &f(Inst::MemCopy {
                    dst: v(1),
                    src: v(2),
                    bytes,
                    overlap: true,
                }),
                module,
            );
            parity(
                &f(Inst::MemSet {
                    dst: v(1),
                    byte: v(2),
                    bytes,
                }),
                module,
            );
        }
    }
    assert!(
        parity(
            &f(Inst::MemSet {
                dst: v(0),
                byte: v(3),
                bytes: v(4)
            }),
            None
        )
        .is_empty()
    );
    assert!(
        parity(
            &f(Inst::MemSet {
                dst: v(0),
                byte: v(3),
                bytes: v(5)
            }),
            Some(&pinned)
        )
        .is_empty()
    );
}

#[test]
fn boolean_conditions_and_both_assert_message_pairs_preserve_role_order() {
    for cond in [v(6), v(1), v(7), v(999)] {
        parity(
            &f(Inst::CondBr {
                cond,
                then_target: BlockId::new(1),
                then_args: vec![],
                else_target: BlockId::new(2),
                else_args: vec![],
            }),
            None,
        );
        parity(&f(Inst::Assume { cond }), None);
        for kind in [
            AssertKind::BoundsCheck {
                index: v(1),
                len: v(2),
            },
            AssertKind::MisalignedPtr {
                required: v(1),
                found: v(2),
            },
            AssertKind::NullPtr,
            AssertKind::Unspecified,
            AssertKind::Overflow(trust_ir::inst::AssertOverflowOp::Add),
            AssertKind::DivByZero,
            AssertKind::RemByZero,
        ] {
            let site = PanicSite {
                entry: FuncId::new(9),
                location: PanicLocation::Value(v(0)),
            };
            for inst in [
                Inst::Assert {
                    cond,
                    kind,
                    site: Some(site),
                },
                Inst::AssertInvoke {
                    cond,
                    kind,
                    site,
                    normal_dest: BlockId::new(1),
                    normal_args: vec![],
                    unwind_dest: BlockId::new(2),
                },
            ] {
                parity(&f(inst), None);
            }
        }
    }
}

#[test]
fn checked_consumption_positions_defer_only_outer_refine_while_copy_remains_exact() {
    for ty in [
        Ty::U32,
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Tuple(vec![Ty::Refine(TyId::new(0), PredId::new(0))]),
    ] {
        for value in [v(1), v(2), v(7), v(999)] {
            parity(
                &f(Inst::Store {
                    ty: ty.clone(),
                    ptr: v(0),
                    value,
                    volatile: false,
                    align: None,
                }),
                None,
            );
            parity(
                &f(Inst::AtomicStore {
                    ty: ty.clone(),
                    ptr: v(0),
                    value,
                    ordering: Ordering::Acquire,
                }),
                None,
            );
            parity(
                &f(Inst::Copy {
                    ty: ty.clone(),
                    operand: value,
                }),
                None,
            );
        }
    }
}

#[test]
fn gep_checks_base_then_each_known_index_with_duplicate_order_and_scalar_integer_rule() {
    let function = f(Inst::GEP {
        pointee_ty: Ty::U32,
        base: v(1),
        indices: vec![v(6), v(2), v(3), v(7), v(999), v(6)],
        inbounds: false,
    });
    let errors = parity(&function, None);
    assert_eq!(errors.len(), 4);
    assert!(matches!(
        errors[0],
        ValidationError::OperandNotPointer { .. }
    ));
    assert!(
        errors[1..]
            .iter()
            .all(|e| matches!(e, ValidationError::GepIndexNotInteger { .. }))
    );
}

#[test]
fn duplicate_type_definitions_and_fat_borrow_inference_use_the_complete_original_map() {
    let mut function = f(Inst::Copy {
        ty: Ty::U32,
        operand: v(1),
    });
    function.blocks[0].params.push((v(1), Ty::I32));
    assert_eq!(parity(&function, None).len(), 1);
    function.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Borrow { ptr: v(8) }).with_result(v(1)),
    );
    // Compare this constituent's selected copy against a one-copy function
    // carrying the same inferred source rather than assuming first-definition.
    let values = values(&function, None);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual = validate_instruction_basic_type_operands_observed(
        0,
        &function.blocks[0].body[1].inst,
        &values,
        None,
        &mut session,
        site(),
    )
    .unwrap();
    let all = super::super::super::validate_types(
        &function,
        ValidationContext {
            cast_mode: CastValidationMode::FunctionOnly,
            pointer_bits: DEFAULT_POINTER_BITS,
            module: None,
        },
    );
    assert_eq!(actual, all.into_iter().filter(included).collect::<Vec<_>>());
    assert!(
        matches!(&actual[0],ValidationError::OperandTypeMismatch {actual,..} if actual=="fatptr<str>")
    );
}

#[test]
fn nested_unicode_type_spelling_and_unknown_inputs_preserve_exact_diagnostics() {
    let mut function = f(Inst::Copy {
        ty: Ty::Tuple(vec![Ty::U32]),
        operand: v(1),
    });
    function.blocks[0].params[1].1 = Ty::Handle(Box::new(HandleTy::new("λ'\n", "runtime\0")));
    assert_eq!(parity(&function, None).len(), 1);
    assert!(
        parity(
            &f(Inst::Load {
                ty: Ty::U32,
                ptr: v(999),
                volatile: false,
                align: None
            }),
            None
        )
        .is_empty()
    );
}
