// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn formal_parameter_requires_exactly_one_physical_entry_block() {
    let mut f = function(Vec::new());
    assert_eq!(
        run(&f, 1),
        [Root::Place(EffectPlace::ParamPointee { index: 0 })]
    );
    f.entry = BlockId::new(99);
    assert_eq!(run(&f, 1), [Root::Untraceable]);
    f.entry = BlockId::new(0);
    f.blocks.push(Block::new(BlockId::new(0)));
    assert_eq!(run(&f, 1), [Root::Untraceable]);
}
#[test]
fn every_normal_or_unwind_entry_edge_blocks_the_formal_parameter_exemption() {
    let mut count = 0;
    for mut inst in witnesses::all() {
        let branch = match &mut inst {
            Inst::Br { target, .. } => {
                *target = BlockId::new(0);
                true
            }
            Inst::CondBr { else_target, .. } => {
                *else_target = BlockId::new(0);
                true
            }
            Inst::Switch { default, .. } => {
                *default = BlockId::new(0);
                true
            }
            Inst::Invoke { unwind_dest, .. }
            | Inst::InvokeIndirect { unwind_dest, .. }
            | Inst::AssertInvoke { unwind_dest, .. }
            | Inst::DropInvoke { unwind_dest, .. } => {
                *unwind_dest = BlockId::new(0);
                true
            }
            _ => false,
        };
        if branch {
            count += 1;
            assert_eq!(
                run(&function(vec![node(inst, &[])]), 1),
                [Root::Untraceable]
            );
        }
    }
    assert_eq!(count, 7);
}
#[test]
fn switch_case_reentry_counts_even_when_default_leaves_and_arguments_are_empty() {
    let f = function(vec![node(
        Inst::Switch {
            value: v(123),
            cases: vec![SwitchCase {
                value: Constant::Int(9),
                target: BlockId::new(0),
                args: Vec::new(),
            }],
            default: BlockId::new(2),
            default_args: Vec::new(),
            exhaustive_enum_unreachable: false,
        },
        &[],
    )]);
    assert_eq!(run(&f, 1), [Root::Untraceable]);
}
#[test]
fn all_physical_nodes_are_inspected_including_a_nonfinal_branch() {
    let f = function(vec![
        node(
            Inst::Br {
                target: BlockId::new(0),
                args: Vec::new(),
            },
            &[],
        ),
        node(Inst::Unreachable, &[]),
    ]);
    assert_eq!(run(&f, 1), [Root::Untraceable]);
}
#[test]
fn edge_argument_payloads_are_not_walked_when_only_targets_determine_reentry() {
    let f = function(vec![node(
        Inst::Br {
            target: BlockId::new(2),
            args: Vec::new(),
        },
        &[],
    )]);
    let mut changed = f.clone();
    if let Inst::Br { args, .. } = &mut changed.blocks[0].body[0].inst {
        *args = vec![v(999); 30000];
    }
    let trace = |f: &Function| {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let body = ObservedBody::new_observed(f, &mut s, site()).unwrap();
        body.retire_observed(&mut s, site()).unwrap();
        drop(s);
        o.events
    };
    assert_eq!(trace(&f), trace(&changed));
    assert_eq!(
        run(&changed, 1),
        [Root::Place(EffectPlace::ParamPointee { index: 0 })]
    );
}
