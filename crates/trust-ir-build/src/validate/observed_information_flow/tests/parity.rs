// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

#[test]
fn reverse_chain_cycle_and_stored_unreachable_blocks_keep_sink_order_and_duplicates() {
    assert_eq!(
        parity(&fixture()),
        errors(&[(7, 4), (7, 1), (7, 4), (2, 2), (2, 1)])
    );
}

#[test]
fn unseeded_cycle_empty_and_bodyless_functions_remain_clean() {
    for function in [
        function(vec![]),
        function(vec![block(9, vec![])]),
        function(vec![block(0, vec![copy(2, 1), copy(1, 2), sink(&[1, 2])])]),
    ] {
        assert!(parity(&function).is_empty());
    }
}

#[test]
fn duplicate_seed_and_result_ids_and_multiple_results_preserve_set_semantics() {
    let mut producer = copy(1, 2).with_results(ids(&[2, 3, 2]));
    producer.proofs = vec![ProofAnnotation::TrustedSink, ProofAnnotation::TrustedSink];
    let mut seed = seed(1).with_results(ids(&[1, 1]));
    seed.proofs.push(ProofAnnotation::Tainted);
    let f = function(vec![block(0, vec![producer, seed, sink(&[3, 2, 2, 1])])]);
    assert_eq!(
        parity(&f),
        errors(&[(0, 1), (0, 3), (0, 2), (0, 2), (0, 1)])
    );
}

#[test]
fn only_node_markers_count_and_marker_only_nodes_do_not_taint_operands() {
    let mut no_result = InstrNode::new(Inst::Return { values: ids(&[4]) });
    no_result.proofs = vec![ProofAnnotation::Tainted];
    let mut f = function(vec![block(0, vec![no_result, copy(4, 5), sink(&[4, 5])])]);
    f.proofs = vec![ProofAnnotation::Tainted, ProofAnnotation::TrustedSink];
    f.blocks[0].params.push((v(4), Ty::U32));
    assert!(parity(&f).is_empty());
    f.blocks[0].body.insert(0, seed(4));
    assert_eq!(parity(&f), errors(&[(0, 4), (0, 5)]));
}

#[test]
fn duplicate_block_ids_and_undefined_same_value_ids_keep_physical_node_order() {
    let f = function(vec![
        block(8, vec![sink(&[42, 42])]),
        block(8, vec![seed(42), sink(&[42])]),
        block(1, vec![sink(&[42, 7])]),
    ]);
    assert_eq!(parity(&f), errors(&[(8, 42), (8, 42), (8, 42), (1, 42)]));
}

#[test]
fn switch_assert_and_invoke_sink_ids_are_operands_not_definition_metadata() {
    let instructions = [
        Inst::Switch {
            value: v(1),
            default: BlockId::new(1),
            default_args: ids(&[2, 1]),
            cases: vec![SwitchCase {
                value: Constant::Int(1),
                target: BlockId::new(1),
                args: ids(&[3, 3]),
            }],
            exhaustive_enum_unreachable: false,
        },
        Inst::AssertInvoke {
            cond: v(1),
            kind: AssertKind::BoundsCheck {
                index: v(2),
                len: v(3),
            },
            site: PanicSite {
                entry: FuncId::new(1),
                location: PanicLocation::Value(v(4)),
            },
            normal_dest: BlockId::new(1),
            normal_args: ids(&[5, 1]),
            unwind_dest: BlockId::new(1),
        },
        Inst::InvokeIndirect {
            callee: v(4),
            sig: FuncTyId::new(1),
            args: ids(&[2, 3]),
            calling_conv: CallingConv::C,
            normal_dest: BlockId::new(1),
            normal_args: ids(&[5, 1]),
            unwind_dest: BlockId::new(1),
        },
    ];
    let expected = [
        vec![(0, 1), (0, 2), (0, 1), (0, 3), (0, 3)],
        vec![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 1)],
        vec![(0, 4), (0, 2), (0, 3), (0, 5), (0, 1)],
    ];
    for (instruction, expected) in instructions.into_iter().zip(expected) {
        let mut nodes = (1..=5).map(seed).collect::<Vec<_>>();
        nodes.push(InstrNode::new(instruction).with_proof(ProofAnnotation::TrustedSink));
        assert_eq!(parity(&function(vec![block(0, nodes)])), errors(&expected));
    }
}

#[test]
fn excluded_types_constants_function_ids_and_heap_contents_do_not_become_value_flow() {
    let f = function(vec![block(
        0,
        vec![
            seed(1),
            InstrNode::new(Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(1),
            })
            .with_result(v(2))
            .with_proof(ProofAnnotation::TrustedSink),
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![],
            })
            .with_result(v(3))
            .with_proof(ProofAnnotation::TrustedSink),
            InstrNode::new(Inst::Undef {
                ty: Ty::Array(TyId::new(1), 1),
            })
            .with_result(v(4))
            .with_proof(ProofAnnotation::TrustedSink),
            InstrNode::new(Inst::Store {
                ty: Ty::U32,
                ptr: v(9),
                value: v(1),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Load {
                ty: Ty::U32,
                ptr: v(9),
                volatile: false,
                align: None,
            })
            .with_result(v(5)),
            sink(&[2, 3, 4, 5]),
        ],
    )]);
    assert!(parity(&f).is_empty());
}

#[test]
fn wide_sink_preserves_every_duplicate_error_and_actual_operand_storage() {
    let values = vec![1; 2048];
    let f = function(vec![block(0, vec![seed(1), sink(&values)])]);
    assert_eq!(parity(&f), errors(&vec![(0, 1); 2048]));
}
