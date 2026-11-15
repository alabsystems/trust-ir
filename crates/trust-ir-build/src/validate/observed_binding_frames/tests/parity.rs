// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn ordinary_fixed_and_nested_string_diagnostics_keep_exact_phase_and_use_order() {
    let errors = parity(&fixture());
    assert_eq!(errors.len(), 6);
    assert!(matches!(
        errors[0],
        ValidationError::BindingBindTypeMismatch { .. }
    ));
    assert!(matches!(
        errors[1],
        ValidationError::BindingUseAfterClose { .. }
    ));
    assert!(matches!(
        errors[2],
        ValidationError::BindingSlotTypeMismatch { .. }
    ));
    assert!(matches!(
        errors[3],
        ValidationError::BindingFrameNotOpen {
            frame_value: 99,
            ..
        }
    ));
    assert!(matches!(
        errors[4],
        ValidationError::BindingFrameUnopened {
            frame_value: 99,
            ..
        }
    ));
    assert!(matches!(
        errors[5],
        ValidationError::BindingUseAfterClose { .. }
    ));
}

#[test]
fn valid_open_bind_load_close_and_empty_declarations_remain_clean() {
    assert!(
        parity(&function(vec![
            open(1, vec![Ty::U32], 1),
            bind(1, 0, 10, 2),
            load(2, 0, Ty::U32),
            close(2)
        ]))
        .is_empty()
    );
    assert!(parity(&function(vec![])).is_empty());
    let mut f = function(vec![]);
    f.blocks.clear();
    assert!(parity(&f).is_empty());
}

#[test]
fn first_frame_signature_and_last_result_frame_assignment_match_original_maps() {
    let f = function(vec![
        open(7, vec![Ty::U32], 1),
        open(7, vec![Ty::I32], 2),
        load(2, 0, Ty::U32),
        close(2),
    ]);
    assert_eq!(
        parity(&f),
        vec![ValidationError::BindingFrameIdReused {
            block: 0,
            frame_id: 7
        }]
    );
    let f = function(vec![
        open(1, vec![Ty::U32], 1),
        open(2, vec![Ty::I32], 1),
        load(1, 0, Ty::I32),
        close(1),
    ]);
    assert_eq!(
        parity(&f),
        vec![ValidationError::BindingFrameUnclosed {
            block: 0,
            frame_id: 1
        }]
    );
}

#[test]
fn reverse_block_bind_and_edge_chain_reaches_the_same_fixed_point() {
    let mut f = function(vec![]);
    f.blocks.clear();
    let mut end = Block::new(b(2));
    end.params.push((v(20), Ty::Ptr));
    end.body = vec![load(20, 0, Ty::U32), close(20)];
    let mut middle = Block::new(b(1));
    middle.params.push((v(15), Ty::Ptr));
    middle.body = vec![
        bind(15, 0, 10, 16),
        InstrNode::new(Inst::Br {
            target: b(2),
            args: vec![v(16)],
        }),
    ];
    let mut start = Block::new(b(0));
    start.params.push((v(10), Ty::U32));
    start.body = vec![
        open(7, vec![Ty::U32], 1),
        InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(1)],
        }),
    ];
    f.blocks = vec![end, middle, start];
    assert!(parity(&f).is_empty());
}

#[test]
fn every_invoke_family_propagates_normal_edge_frame_handles_even_in_malformed_target_types() {
    for kind in 0..4 {
        let term = match kind {
            0 => Inst::Invoke {
                callee: FuncId::new(9),
                args: vec![],
                normal_dest: b(1),
                normal_args: vec![v(1)],
                unwind_dest: b(2),
            },
            1 => Inst::InvokeIndirect {
                callee: v(10),
                sig: FuncTyId::new(0),
                args: vec![],
                calling_conv: CallingConv::C,
                normal_dest: b(1),
                normal_args: vec![v(1)],
                unwind_dest: b(2),
            },
            2 => Inst::DropInvoke {
                ty: Ty::U32,
                ptr: v(10),
                normal_dest: b(1),
                normal_args: vec![v(1)],
                unwind_dest: b(2),
            },
            _ => Inst::AssertInvoke {
                cond: v(10),
                kind: trust_ir::AssertKind::NullPtr,
                site: trust_ir::PanicSite {
                    entry: FuncId::new(9),
                    location: trust_ir::PanicLocation::Value(v(10)),
                },
                normal_dest: b(1),
                normal_args: vec![v(1)],
                unwind_dest: b(2),
            },
        };
        let mut f = function(vec![open(7, vec![Ty::U32], 1), InstrNode::new(term)]);
        let mut target = Block::new(b(1));
        target.params.push((v(20), Ty::Bool));
        target.body = vec![load(20, 0, Ty::U32), close(20)];
        f.blocks.push(target);
        assert!(parity(&f).is_empty()); // Separate arity/type passes own Bool.
    }
}

#[test]
fn unreachable_block_checks_do_not_invent_a_path_from_the_closed_block() {
    let mut f = function(vec![
        open(7, vec![Ty::U32], 1),
        bind(1, 0, 10, 2),
        close(1),
        load(2, 0, Ty::U32),
    ]);
    let mut other = Block::new(b(1));
    other.body = vec![load(1, 0, Ty::U32)];
    f.blocks.push(other);
    assert_eq!(
        parity(&f),
        vec![ValidationError::BindingUseAfterClose {
            block: 0,
            frame_value: 2,
        }]
    );
}

#[test]
fn slot_bounds_and_absent_values_preserve_checks_without_new_type_exemptions() {
    let f = function(vec![
        open(7, vec![Ty::U32], 1),
        bind(1, 1, 11, 2),
        load(1, 2, Ty::I32),
        bind(1, 0, 999, 3),
        close(1),
    ]);
    let errors = parity(&f);
    assert_eq!(errors.len(), 2);
    assert!(
        errors
            .iter()
            .all(|e| matches!(e, ValidationError::BindingSlotOutOfRange { .. }))
    );
}

#[test]
fn first_typeable_definition_query_not_last_write_map_drives_slot_writes() {
    let mut f = function(vec![
        open(7, vec![Ty::U32], 1),
        InstrNode::new(Inst::Undef { ty: Ty::I32 }).with_result(v(10)),
        bind(1, 0, 10, 2),
        close(2),
    ]);
    assert!(parity(&f).is_empty());
    f.blocks[0].params.clear();
    assert_eq!(parity(&f).len(), 1);
    f.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        })
        .with_result(v(10)),
    );
    assert_eq!(parity(&f).len(), 1);
}

#[test]
fn outer_refinement_defers_but_nested_refinement_and_unicode_identity_mismatches_report_exactly() {
    let refined = Ty::Refine(TyId::new(0), PredId::new(0));
    let mut f = function(vec![
        open(7, vec![refined.clone()], 1),
        bind(1, 0, 11, 2),
        load(2, 0, Ty::I32),
        close(2),
    ]);
    assert!(parity(&f).is_empty());
    f.blocks[0].params[1].1 = Ty::Tuple(vec![Ty::I32]);
    f.blocks[0].body[0] = open(7, vec![Ty::Tuple(vec![refined])], 1);
    assert_eq!(parity(&f).len(), 2);
    let ty = Ty::Handle(Box::new(trust_ir::HandleTy::new("λ'\n", "runtime\0")));
    f.blocks[0].body[0] = open(7, vec![ty], 1);
    assert_eq!(parity(&f).len(), 2);
}

#[test]
fn unclosed_frame_ids_sort_ascending_and_name_the_first_physical_opening_block() {
    let mut f = function(vec![open(15, vec![], 1)]);
    f.blocks[0].id = b(9);
    f.entry = b(9);
    let mut second = Block::new(b(8));
    second.body = vec![open(2, vec![], 2)];
    f.blocks.push(second);
    assert_eq!(
        parity(&f),
        vec![
            ValidationError::BindingFrameUnclosed {
                block: 8,
                frame_id: 2
            },
            ValidationError::BindingFrameUnclosed {
                block: 9,
                frame_id: 15
            }
        ]
    );
}

#[test]
fn duplicate_signature_is_refused_without_panicking_either_entry_point() {
    let f = function(vec![
        open(7, vec![], 1),
        open(7, vec![Ty::U32], 2),
        load(2, 0, Ty::U32),
    ]);
    let errors = parity(&f);
    assert_eq!(
        errors,
        vec![
            ValidationError::BindingFrameIdReused {
                block: 0,
                frame_id: 7
            },
            ValidationError::BindingSlotOutOfRange {
                block: 0,
                frame_id: 7,
                slot: 0,
                arity: 0
            },
            ValidationError::BindingFrameUnclosed {
                block: 0,
                frame_id: 7
            },
        ]
    );
}

#[test]
fn real_frame_index_growth_and_all_open_results_preserve_original_stored_behavior() {
    let mut nodes = Vec::new();
    for id in (0..64).rev() {
        nodes.push(open(id, vec![], id + 100).with_results([v(id + 100), v(id + 1000)]));
        nodes.push(close(id + 1000));
    }
    assert!(parity(&function(nodes)).is_empty());
}

#[test]
fn closing_a_lineage_rejects_sibling_reads_writes_and_second_closes() {
    for operation in [load(1, 0, Ty::U32), bind(3, 0, 10, 4), close(3)] {
        let errors = parity(&function(vec![
            open(0, vec![Ty::U32], 1),
            bind(1, 0, 10, 2),
            bind(2, 0, 10, 3),
            close(2),
            operation,
        ]));
        assert!(
            errors
                .iter()
                .any(|error| matches!(error, ValidationError::BindingUseAfterClose { .. }))
        );
    }
}

#[test]
fn older_snapshot_before_close_and_another_open_lineage_remain_valid() {
    let errors = parity(&function(vec![
        open(0, vec![Ty::U32], 1),
        bind(1, 0, 10, 2),
        load(1, 0, Ty::U32),
        open(1, vec![Ty::U32], 3),
        bind(3, 0, 10, 4),
        close(2),
        load(4, 0, Ty::U32),
        close(4),
    ]));
    assert!(errors.is_empty());
}
