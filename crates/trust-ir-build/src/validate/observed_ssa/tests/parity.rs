// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn duplicate_then_missing_then_dominance_groups_match_complete_original_ssa() {
    assert_eq!(
        parity(&fixture()),
        vec![
            ValidationError::DuplicateValueDef { value: 0, block: 0 },
            ValidationError::UseBeforeDef {
                value: 99,
                block: 0
            },
            ValidationError::UseBeforeDef {
                value: 777,
                block: 2
            },
            ValidationError::UseBeforeDefInBlock { value: 2, block: 0 },
        ]
    );
}
#[test]
fn local_params_forward_self_uses_and_last_definition_replacement_keep_original_order() {
    for body in [
        vec![copy(0, 1), ret(&[1])],
        vec![copy(2, 1), copy(0, 2), ret(&[1])],
        vec![copy(1, 1), ret(&[1])],
        vec![copy(0, 1), copy(0, 1), ret(&[1])],
    ] {
        let f = function(vec![block(0, body).with_param(ValueId::new(0), Ty::Bool)]);
        parity(&f);
    }
    let f = function(vec![
        block(0, vec![copy(0, 1), copy(1, 2), copy(0, 1), ret(&[1])])
            .with_param(ValueId::new(0), Ty::Bool),
    ]);
    assert_eq!(
        parity(&f),
        vec![
            ValidationError::DuplicateValueDef { value: 1, block: 0 },
            ValidationError::UseBeforeDefInBlock { value: 1, block: 0 }
        ]
    );
}
#[test]
fn cross_block_dominance_requires_all_paths_and_preserves_unreachable_missing_checks() {
    let entry = block(
        0,
        vec![InstrNode::new(Inst::CondBr {
            cond: ValueId::new(0),
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        })],
    )
    .with_param(ValueId::new(0), Ty::Bool);
    let f = function(vec![
        entry,
        block(1, vec![copy(0, 1), branch(3, &[])]),
        block(2, vec![branch(3, &[])]),
        block(3, vec![ret(&[1, 1])]),
        block(4, vec![ret(&[999])]),
    ]);
    assert_eq!(
        parity(&f),
        vec![
            ValidationError::UseBeforeDef {
                value: 999,
                block: 4
            },
            ValidationError::UseBeforeDefInBlock { value: 1, block: 3 },
            ValidationError::UseBeforeDefInBlock { value: 1, block: 3 }
        ]
    );
}
#[test]
fn malformed_cfg_skips_dominance_but_never_skips_missing_operands() {
    let mut f = fixture();
    f.blocks[0].body.push(ret(&[888]));
    let errors = parity(&f);
    assert!(
        !errors
            .iter()
            .any(|error| matches!(error, ValidationError::UseBeforeDefInBlock { .. }))
    );
    assert!(errors.iter().any(|error| matches!(
        error,
        ValidationError::UseBeforeDef {
            value: 888,
            block: 0
        }
    )));
    let mut f = fixture();
    f.blocks.push(f.blocks[0].clone());
    parity(&f);
    let mut f = fixture();
    f.entry = BlockId::new(123);
    parity(&f);
    assert!(parity(&function(vec![])).is_empty());
}
#[test]
fn invoke_direct_and_indirect_use_call_arguments_before_and_normal_arguments_after_results() {
    for indirect in [false, true] {
        let normal_dest = BlockId::new(1);
        let unwind_dest = BlockId::new(2);
        let instruction = if indirect {
            Inst::InvokeIndirect {
                callee: ValueId::new(0),
                sig: FuncTyId::new(0),
                args: vec![ValueId::new(1), ValueId::new(99)],
                calling_conv: CallingConv::C,
                normal_dest,
                normal_args: vec![ValueId::new(1)],
                unwind_dest,
            }
        } else {
            Inst::Invoke {
                callee: FuncId::new(999),
                args: vec![ValueId::new(1), ValueId::new(99)],
                normal_dest,
                normal_args: vec![ValueId::new(1)],
                unwind_dest,
            }
        };
        let entry = block(
            0,
            vec![InstrNode::new(instruction).with_result(ValueId::new(1))],
        )
        .with_param(ValueId::new(0), Ty::Ptr);
        let f = function(vec![
            entry,
            block(1, vec![ret(&[1])]),
            block(2, vec![ret(&[1])]),
        ]);
        let errors = parity(&f);
        assert_eq!(
            errors,
            vec![
                ValidationError::UseBeforeDef {
                    value: 99,
                    block: 0
                },
                ValidationError::UseBeforeDefInBlock { value: 1, block: 0 },
                ValidationError::UseBeforeDefInBlock { value: 1, block: 2 }
            ]
        );
    }
}
#[test]
fn other_invoke_families_keep_ordinary_before_instruction_coordinates() {
    let normal_dest = BlockId::new(1);
    let unwind_dest = BlockId::new(2);
    for instruction in [
        Inst::DropInvoke {
            ty: Ty::Bool,
            ptr: ValueId::new(0),
            normal_dest,
            normal_args: vec![ValueId::new(1)],
            unwind_dest,
        },
        Inst::AssertInvoke {
            cond: ValueId::new(0),
            kind: AssertKind::BoundsCheck {
                index: ValueId::new(99),
                len: ValueId::new(0),
            },
            site: PanicSite {
                entry: FuncId::new(999),
                location: PanicLocation::Value(ValueId::new(77)),
            },
            normal_dest,
            normal_args: vec![ValueId::new(1)],
            unwind_dest,
        },
    ] {
        let entry = block(
            0,
            vec![InstrNode::new(instruction).with_result(ValueId::new(1))],
        )
        .with_param(ValueId::new(0), Ty::Bool);
        let errors = parity(&function(vec![
            entry,
            block(1, vec![ret(&[])]),
            block(2, vec![ret(&[])]),
        ]));
        assert!(errors.iter().any(|error| matches!(
            error,
            ValidationError::UseBeforeDefInBlock { value: 1, block: 0 }
        )));
    }
}
#[test]
fn unused_deep_type_payload_is_borrowed_without_hidden_type_clone_or_walk() {
    let shallow = function(vec![
        block(0, vec![ret(&[0])]).with_param(ValueId::new(0), Ty::U8),
    ]);
    let mut wide = shallow.clone();
    wide.blocks[0].params[0].1 = Ty::Tuple(vec![Ty::Bool; 100_000]);
    let (a, first) = observed(&shallow);
    let (b, second) = observed(&wide);
    assert_eq!(a, b);
    assert_eq!(first.events, second.events);
    assert_eq!((first.work, first.bytes), (second.work, second.bytes));
}
#[test]
fn wide_definition_chain_reuses_actual_dominance_and_checks_every_operand() {
    let mut blocks = Vec::new();
    for id in 0..64 {
        let mut body = if id == 0 {
            vec![InstrNode::new(Inst::NullPtr).with_result(ValueId::new(0))]
        } else {
            vec![copy(id - 1, id)]
        };
        body.push(if id == 63 {
            ret(&[id])
        } else {
            branch(id + 1, &[])
        });
        blocks.push(block(id, body));
    }
    assert!(parity(&function(blocks)).is_empty());
}
