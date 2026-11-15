// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn shared_root_and_direct_end_rules_preserve_physical_error_order() {
    assert_eq!(parity(&fixture()), vec![shared(), end()]);
}

#[test]
fn supplied_last_write_type_context_controls_static_shared_reference_checks() {
    for ty in [Ty::Ref(Box::new(Ty::U8)), Ty::PtrConst(Box::new(Ty::U8))] {
        let mut f = function(vec![node(Inst::BorrowMut { ptr: v(1) }, &[2])]);
        f.blocks[0].params.push((v(1), ty));
        assert_eq!(parity(&f), vec![shared()]);
        f.blocks[0]
            .body
            .insert(0, node(Inst::Undef { ty: Ty::Ptr }, &[1]));
        assert!(parity(&f).is_empty());
    }
    for ty in [Ty::RefMut(Box::new(Ty::U8)), Ty::PtrMut(Box::new(Ty::U8))] {
        let mut f = function(vec![node(Inst::BorrowMut { ptr: v(1) }, &[2])]);
        f.blocks[0].params.push((v(1), ty));
        assert!(parity(&f).is_empty());
    }
}

#[test]
fn caller_module_call_types_are_used_without_reconstructing_a_standalone_map() {
    let f = function(vec![
        node(
            Inst::Call {
                callee: FuncId::new(0),
                args: vec![],
            },
            &[1],
        ),
        node(Inst::BorrowMut { ptr: v(1) }, &[2]),
    ]);
    let mut module = Module::new("context");
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::Ref(Box::new(Ty::U8))],
        abi: None,
        is_vararg: false,
    });
    module.functions.push(Function::new(
        FuncId::new(0),
        "callee",
        FuncTyId::new(0),
        b(0),
    ));
    let ordinary = super::super::super::build_module_value_types(&f, &module);
    assert_eq!(
        run(&f, Some(&module)).0,
        super::super::super::claims::validate_borrow_structure(&f, &ordinary)
    );
    assert_eq!(run(&f, Some(&module)).0, vec![shared()]);
    assert!(parity(&f).is_empty());
}

#[test]
fn any_duplicate_definition_may_supply_a_shared_root_but_end_requires_all_nonempty_defs() {
    let mut f = function(vec![
        node(Inst::Undef { ty: Ty::Ptr }, &[1]),
        node(Inst::Borrow { ptr: v(99) }, &[1, 1]),
        node(Inst::BorrowMut { ptr: v(1) }, &[2]),
        node(Inst::EndBorrow { borrow_ptr: v(1) }, &[]),
    ]);
    assert_eq!(parity(&f), vec![shared(), end()]);
    f.blocks[0].body.remove(0);
    assert_eq!(parity(&f), vec![shared()]);
    f.blocks[0].params.push((v(1), Ty::Ptr));
    assert_eq!(parity(&f), vec![shared(), end()]);
    assert_eq!(
        parity(&function(vec![node(
            Inst::EndBorrow { borrow_ptr: v(99) },
            &[]
        )])),
        vec![end()]
    );
}

#[test]
fn transparent_copy_gep_and_ptrtoptr_paths_reject_shared_roots() {
    for instruction in [
        Inst::Copy {
            ty: Ty::Ptr,
            operand: v(1),
        },
        Inst::GEP {
            pointee_ty: Ty::U8,
            base: v(1),
            indices: vec![v(99)],
            inbounds: false,
        },
        Inst::Cast {
            op: CastOp::PtrToPtr,
            src_ty: Ty::Ptr,
            dst_ty: Ty::Ptr,
            operand: v(1),
        },
    ] {
        let f = function(vec![
            node(Inst::Borrow { ptr: v(99) }, &[1]),
            node(instruction, &[2]),
            node(Inst::BorrowMut { ptr: v(2) }, &[3]),
        ]);
        assert_eq!(parity(&f), vec![shared()]);
    }
}

#[test]
fn select_follows_both_arms_and_cycles_do_not_hide_a_shared_definition() {
    for (then_val, else_val) in [(v(1), v(99)), (v(99), v(1)), (v(1), v(1))] {
        let f = function(vec![
            node(Inst::Borrow { ptr: v(99) }, &[1]),
            node(
                Inst::Select {
                    ty: Ty::Ptr,
                    cond: v(99),
                    then_val,
                    else_val,
                },
                &[2],
            ),
            node(Inst::BorrowMut { ptr: v(2) }, &[3]),
        ]);
        assert_eq!(parity(&f), vec![shared()]);
    }
    let mut f = function(vec![
        node(
            Inst::Copy {
                ty: Ty::Ptr,
                operand: v(2),
            },
            &[1],
        ),
        node(
            Inst::Copy {
                ty: Ty::Ptr,
                operand: v(1),
            },
            &[2],
        ),
        node(Inst::BorrowMut { ptr: v(2) }, &[3]),
    ]);
    assert!(parity(&f).is_empty());
    f.blocks[0]
        .body
        .insert(0, node(Inst::Borrow { ptr: v(99) }, &[1]));
    assert_eq!(parity(&f), vec![shared()]);
}

#[test]
fn loads_calls_integer_round_trips_and_pointer_parts_remain_opaque_roots() {
    for instruction in [
        Inst::Load {
            ty: Ty::Ptr,
            ptr: v(1),
            volatile: false,
            align: None,
        },
        Inst::Call {
            callee: FuncId::new(9),
            args: vec![v(1)],
        },
        Inst::Cast {
            op: CastOp::IntToPtr,
            src_ty: Ty::Usize,
            dst_ty: Ty::Ptr,
            operand: v(1),
        },
        Inst::PtrFromParts {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Usize,
            data: v(1),
            metadata: v(1),
        },
    ] {
        let f = function(vec![
            node(Inst::Borrow { ptr: v(99) }, &[1]),
            node(instruction, &[2]),
            node(Inst::BorrowMut { ptr: v(2) }, &[3]),
        ]);
        assert!(parity(&f).is_empty());
    }
}

#[test]
fn all_four_invokes_contribute_normal_incoming_even_before_a_nonterminating_tail() {
    for invoke in invokes() {
        let mut f = function(vec![
            node(Inst::Borrow { ptr: v(99) }, &[1]),
            node(invoke, &[]),
            node(Inst::Return { values: vec![] }, &[]),
        ]);
        for (block, value) in [(1, 7), (2, 8)] {
            let mut target = Block::new(b(block)).with_param(v(value), Ty::Ptr);
            target
                .body
                .push(node(Inst::BorrowMut { ptr: v(value) }, &[10 + block]));
            f.blocks.push(target);
        }
        assert_eq!(
            parity(&f),
            vec![ValidationError::BorrowMutThroughSharedRef { block: 1 }]
        );
    }
}

#[test]
fn actual_default_first_incoming_preserves_duplicate_edges_extra_args_and_missing_targets() {
    let switch = Inst::Switch {
        value: v(99),
        default: b(1),
        default_args: vec![v(1), v(2)],
        exhaustive_enum_unreachable: false,
        cases: vec![
            trust_ir::SwitchCase {
                value: trust_ir::Constant::Int(0),
                target: b(1),
                args: vec![v(3)],
            },
            trust_ir::SwitchCase {
                value: trust_ir::Constant::Int(0),
                target: b(9),
                args: vec![v(4)],
            },
        ],
    };
    let f = function(vec![node(switch, &[])]);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.need_incoming(&f, &mut work).unwrap();
    assert_eq!(
        state.incoming.as_deref(),
        Some([(1, 0, v(1)), (1, 1, v(2)), (1, 0, v(3)), (9, 0, v(4))].as_slice())
    );
    assert!(state.edges.is_empty() && state.edges.capacity() == 0);
    state.retire_scratch(&mut work);
}

#[test]
fn duplicate_block_parameter_keys_join_all_normal_incoming_even_for_extra_arity() {
    let mut f = function(vec![
        node(Inst::Borrow { ptr: v(99) }, &[1]),
        node(
            Inst::Br {
                target: b(1),
                args: vec![v(99), v(1)],
            },
            &[],
        ),
    ]);
    f.blocks.push(Block::new(b(1)).with_param(v(7), Ty::Ptr));
    let mut duplicate = Block::new(b(1))
        .with_param(v(8), Ty::Ptr)
        .with_param(v(9), Ty::Ptr);
    duplicate
        .body
        .push(node(Inst::BorrowMut { ptr: v(9) }, &[10]));
    f.blocks.push(duplicate);
    assert_eq!(
        parity(&f),
        vec![ValidationError::BorrowMutThroughSharedRef { block: 1 }]
    );
}

#[test]
fn lazy_construction_keeps_no_borrow_tables_until_a_relevant_instruction() {
    for instructions in [
        vec![node(Inst::Return { values: vec![] }, &[])],
        vec![node(Inst::EndBorrow { borrow_ptr: v(99) }, &[])],
        vec![node(Inst::BorrowMut { ptr: v(99) }, &[1])],
    ] {
        let mut f = function(instructions);
        if matches!(f.blocks[0].body[0].inst, Inst::BorrowMut { .. }) {
            f.blocks[0].params.push((v(99), Ty::Ref(Box::new(Ty::U8))));
        }
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let types =
            super::super::super::build_function_value_types_observed(&f, &mut session, site())
                .unwrap();
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        state.borrows(&f, &types, &mut work).unwrap();
        let inst = &f.blocks[0].body[0].inst;
        assert_eq!(
            state.definitions.is_some(),
            !matches!(inst, Inst::Return { .. })
        );
        assert_eq!(
            state.incoming.is_some(),
            matches!(inst, Inst::BorrowMut { .. })
        );
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
    }
}

#[test]
fn rust_rule_only_uses_trust_stamp_and_copies_raw_names_and_physical_indices() {
    let mut f = fixture();
    f.name = "raw'λ\n\0".repeat(700);
    for producer in [
        None,
        Some(Producer::Clean),
        Some(Producer::TrustIr),
        Some(Producer::TSwift),
        Some(Producer::TC),
        Some(Producer::Other("TRust".repeat(100_000))),
    ] {
        f.producer = producer;
        assert!(reference_parity(&f).is_empty());
    }
    f.producer = Some(Producer::TRust);
    let errors = reference_parity(&f);
    assert_eq!(errors.len(), 4);
    for (error, index) in errors.iter().zip([0, 2, 3, 4]) {
        assert!(
            matches!(error, ValidationError::RustReferenceAsPermissionBorrow { function, block: 0, inst_index } if function == &f.name && *inst_index == index)
        );
    }
}
