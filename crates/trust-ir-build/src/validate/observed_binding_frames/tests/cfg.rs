// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

fn branch(target: u32, args: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Br {
        target: b(target),
        args: args.iter().copied().map(v).collect(),
    })
}
fn conditional(yes: u32, yes_args: &[u32], no: u32, no_args: &[u32]) -> InstrNode {
    InstrNode::new(Inst::CondBr {
        cond: v(11),
        then_target: b(yes),
        then_args: yes_args.iter().copied().map(v).collect(),
        else_target: b(no),
        else_args: no_args.iter().copied().map(v).collect(),
    })
}
fn block(id: u32, params: &[u32], body: Vec<InstrNode>) -> Block {
    let mut block = Block::new(b(id));
    block.params = params.iter().copied().map(|id| (v(id), Ty::Ptr)).collect();
    block.body = body;
    block
}
fn linear(closed: bool, operation: InstrNode) -> Function {
    let mut f = function(vec![open(0, vec![Ty::U32], 1), bind(1, 0, 10, 2)]);
    if closed {
        f.blocks[0].body.push(close(1));
    }
    f.blocks[0].body.push(branch(1, &[2]));
    let mut body = vec![operation];
    if !closed {
        body.push(close(20));
    }
    f.blocks.push(block(1, &[20], body));
    f
}

#[test]
fn closed_alias_read_write_and_second_close_cross_block_boundaries() {
    for operation in [load(20, 0, Ty::U32), bind(20, 0, 10, 21), close(20)] {
        let errors = parity(&linear(true, operation));
        assert_eq!(
            errors,
            vec![ValidationError::BindingUseAfterClose {
                block: 1,
                frame_value: 20
            }]
        );
    }
    assert!(parity(&linear(false, load(20, 0, Ty::U32))).is_empty());
}

#[test]
fn a_fresh_open_on_each_loop_iteration_does_not_reuse_closed_generation_state() {
    let mut f = function(vec![branch(1, &[])]);
    f.blocks.push(block(
        1,
        &[],
        vec![
            open(0, vec![Ty::U32], 1),
            bind(1, 0, 10, 2),
            load(2, 0, Ty::U32),
            close(2),
            conditional(1, &[], 2, &[]),
        ],
    ));
    f.blocks.push(block(2, &[], vec![]));
    assert!(parity(&f).is_empty());
}

fn generation_loop(read_old: bool) -> Function {
    let mut f = function(vec![
        open(1, vec![Ty::U32], 1),
        bind(1, 0, 10, 2),
        close(2),
        branch(1, &[2]),
    ]);
    f.blocks.push(block(
        1,
        &[20],
        vec![
            open(0, vec![Ty::U32], 3),
            bind(3, 0, 10, 4),
            conditional(2, &[4], 3, &[20, 4]),
        ],
    ));
    f.blocks
        .push(block(2, &[40], vec![close(40), branch(1, &[40])]));
    f.blocks.push(block(
        3,
        &[30, 31],
        vec![load(if read_old { 30 } else { 31 }, 0, Ty::U32), close(31)],
    ));
    f
}

#[test]
fn reopening_a_static_frame_does_not_revive_an_old_carried_handle() {
    let errors = parity(&generation_loop(true));
    assert_eq!(
        errors,
        vec![ValidationError::BindingUseAfterClose {
            block: 3,
            frame_value: 30
        }]
    );
    assert!(parity(&generation_loop(false)).is_empty());
}

#[test]
fn self_edge_parameters_are_assigned_in_parallel_without_inventing_aliases() {
    let mut f = function(vec![
        open(0, vec![Ty::U32], 1),
        open(1, vec![Ty::U32], 2),
        branch(1, &[1, 2]),
    ]);
    f.blocks.push(block(
        1,
        &[20, 21],
        vec![conditional(1, &[21, 20], 2, &[20, 21])],
    ));
    f.blocks
        .push(block(2, &[30, 31], vec![close(30), close(31)]));
    // Both exit handles may originate from either declaration after a swap.
    // The non-relational close census cannot credit either one, but the
    // parallel transfer must not invent an alias between these two handles.
    let errors = parity(&f);
    assert!(
        !errors
            .iter()
            .any(|error| matches!(error, ValidationError::BindingUseAfterClose { .. }))
    );
    assert_eq!(
        errors,
        vec![
            ValidationError::BindingFrameUnclosed {
                block: 0,
                frame_id: 0
            },
            ValidationError::BindingFrameUnclosed {
                block: 0,
                frame_id: 1
            },
        ]
    );

    // A genuinely unambiguous close of each original handle is accepted
    // after the same swapping loop; the loop itself is not refused.
    f.blocks[2].body = vec![close(1), close(2)];
    assert!(parity(&f).is_empty());
}

fn signature_join(other: Ty) -> Function {
    let mut f = function(vec![
        open(0, vec![Ty::U32], 1),
        open(1, vec![other], 2),
        conditional(1, &[1], 2, &[2]),
    ]);
    f.blocks.push(block(1, &[20], vec![branch(3, &[20])]));
    f.blocks.push(block(2, &[21], vec![branch(3, &[21])]));
    f.blocks.push(block(
        3,
        &[30],
        vec![load(30, 0, Ty::U32), close(1), close(2)],
    ));
    f
}

#[test]
fn mixed_signature_join_checks_every_origin_independent_of_block_order() {
    let f = signature_join(Ty::I32);
    let errors = parity(&f);
    assert!(matches!(
        errors.as_slice(),
        [ValidationError::BindingSlotTypeMismatch { frame_id: 1, .. }]
    ));
    let mut reordered = f;
    reordered.blocks.reverse();
    assert_eq!(parity(&reordered), errors);
    assert!(parity(&signature_join(Ty::U32)).is_empty());
}

#[test]
fn a_non_frame_or_closed_path_at_a_join_cannot_borrow_the_other_paths_live_origin() {
    let mut f = signature_join(Ty::U32);
    f.blocks[0].body[2] = conditional(1, &[1], 2, &[10]);
    let errors = parity(&f);
    assert!(errors.iter().any(|e| matches!(
        e,
        ValidationError::BindingFrameNotOpen {
            frame_value: 30,
            ..
        }
    )));
    let mut f = signature_join(Ty::U32);
    f.blocks[1].body.insert(0, close(20));
    let errors = parity(&f);
    assert!(errors.iter().any(|e| matches!(
        e,
        ValidationError::BindingUseAfterClose {
            frame_value: 30,
            ..
        }
    )));
}

#[test]
fn every_unwind_edge_preserves_dominating_handles_lifetime() {
    for kind in 0..4 {
        for closed in [false, true] {
            let term = match kind {
                0 => Inst::Invoke {
                    callee: FuncId::new(9),
                    args: vec![],
                    normal_dest: b(1),
                    normal_args: vec![],
                    unwind_dest: b(2),
                },
                1 => Inst::InvokeIndirect {
                    callee: v(10),
                    sig: FuncTyId::new(0),
                    args: vec![],
                    calling_conv: CallingConv::C,
                    normal_dest: b(1),
                    normal_args: vec![],
                    unwind_dest: b(2),
                },
                2 => Inst::DropInvoke {
                    ty: Ty::U32,
                    ptr: v(10),
                    normal_dest: b(1),
                    normal_args: vec![],
                    unwind_dest: b(2),
                },
                _ => Inst::AssertInvoke {
                    cond: v(11),
                    kind: trust_ir::AssertKind::NullPtr,
                    site: trust_ir::PanicSite {
                        entry: FuncId::new(9),
                        location: trust_ir::PanicLocation::Value(v(10)),
                    },
                    normal_dest: b(1),
                    normal_args: vec![],
                    unwind_dest: b(2),
                },
            };
            let mut f = function(vec![open(0, vec![Ty::U32], 1), bind(1, 0, 10, 2)]);
            if closed {
                f.blocks[0].body.push(close(2));
            }
            f.blocks[0].body.push(InstrNode::new(term));
            f.blocks
                .push(block(1, &[], if closed { vec![] } else { vec![close(2)] }));
            f.blocks.push(block(
                2,
                &[],
                if closed {
                    vec![load(2, 0, Ty::U32)]
                } else {
                    vec![load(2, 0, Ty::U32), close(2)]
                },
            ));
            let errors = parity(&f);
            if closed {
                assert_eq!(
                    errors,
                    vec![ValidationError::BindingUseAfterClose {
                        block: 2,
                        frame_value: 2
                    }]
                );
            } else {
                assert!(errors.is_empty());
            }
        }
    }
}

#[test]
fn absent_unwind_arguments_do_not_inherit_a_parameter_from_a_different_edge() {
    let mut f = function(vec![
        open(0, vec![Ty::U32], 1),
        InstrNode::new(Inst::Invoke {
            callee: FuncId::new(9),
            args: vec![],
            normal_dest: b(1),
            normal_args: vec![v(1)],
            unwind_dest: b(1),
        }),
    ]);
    f.blocks
        .push(block(1, &[20], vec![load(20, 0, Ty::U32), close(1)]));
    assert!(parity(&f).iter().any(|e| matches!(
        e,
        ValidationError::BindingFrameNotOpen {
            frame_value: 20,
            ..
        }
    )));
}

#[test]
fn a_frame_cfg_without_an_entry_refuses_analysis_in_both_apis() {
    let mut f = function(vec![open(0, vec![], 1), close(1)]);
    f.entry = b(99);
    assert!(matches!(
        validate_binding_frames(&f).as_slice(),
        [ValidationError::BindingFrameAnalysisFailed { .. }]
    ));
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_binding_frames_observed(&f, &mut session, site()),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(session.first_refusal().is_none());
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::ScratchRetirement
    );
}

#[test]
fn one_ambiguous_close_cannot_credit_every_possible_open_declaration() {
    let mut f = signature_join(Ty::U32);
    f.blocks[3].body = vec![close(30)];
    let errors = parity(&f);
    assert_eq!(
        errors,
        vec![
            ValidationError::BindingFrameUnclosed {
                block: 0,
                frame_id: 0
            },
            ValidationError::BindingFrameUnclosed {
                block: 0,
                frame_id: 1
            },
        ]
    );
}
