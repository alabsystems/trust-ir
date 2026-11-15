// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_original_unwind_diagnostic_order_and_text_match() {
    let errors = parity(&fixture());
    assert_eq!(errors, vec![
        ValidationError::MisplacedLandingPad { block: 2, reason: "also entered by a non-unwind edge from bb1".into() },
        ValidationError::MisplacedLandingPad { block: 3, reason: "not the first instruction of its block (position 1)".into() },
        ValidationError::MisplacedLandingPad { block: 2, reason: "resume of a value no landing pad produced: the operand is a landingpad's type selector, not its exception object".into() },
    ]);
}
#[test]
fn all_four_invokes_check_padless_and_normal_alias_targets_but_not_missing_targets() {
    for (normal, unwind) in [(1, 2), (2, 2), (1, 99)] {
        for instruction in invokes(normal, unwind) {
            let f = function(vec![
                block(0, vec![node(instruction)]),
                block(1, vec![ret()]),
                block(2, vec![ret()]),
            ]);
            let errors = parity(&f);
            assert_eq!(errors.len(), usize::from(unwind != 99));
        }
    }
    for instruction in invokes(1, 2) {
        assert!(
            parity(&function(vec![
                block(0, vec![node(instruction)]),
                block(1, vec![ret()]),
                block(2, vec![pad(&[3, 4]), resume(3)])
            ]))
            .is_empty()
        );
    }
}
#[test]
fn duplicate_block_ids_require_every_twin_to_lead_with_a_pad_in_either_order() {
    for reverse in [false, true] {
        let mut twins = vec![
            block(2, vec![pad(&[3, 4]), resume(3)]),
            block(2, vec![ret()]),
        ];
        if reverse {
            twins.reverse();
        }
        let mut blocks = vec![
            block(0, vec![node(invokes(1, 2).remove(0))]),
            block(1, vec![ret()]),
        ];
        blocks.extend(twins);
        assert!(matches!(
            &parity(&function(blocks))[0],
            ValidationError::UnwindDestWithoutLandingPad {
                block: 0,
                target: 2
            }
        ));
    }
}
#[test]
fn pad_placement_precedence_and_duplicate_normal_sources_keep_exact_join_order() {
    let switch = Inst::Switch {
        value: ValueId::new(0),
        default: BlockId::new(2),
        default_args: vec![],
        cases: vec![SwitchCase {
            value: Constant::Int(0),
            target: BlockId::new(2),
            args: vec![],
        }],
        exhaustive_enum_unreachable: false,
    };
    let f = function(vec![
        block(0, vec![pad(&[]), node(invokes(1, 2).remove(0))]),
        block(7, vec![node(switch)]),
        block(8, vec![branch(2)]),
        block(2, vec![pad(&[3, 4]), ret()]),
        block(4, vec![pad(&[5, 6]), ret()]),
    ]);
    let errors = parity(&f);
    assert!(
        matches!(&errors[0], ValidationError::MisplacedLandingPad { reason, .. } if reason.contains("entry block"))
    );
    assert!(
        matches!(&errors[1], ValidationError::MisplacedLandingPad { reason, .. } if reason == "also entered by a non-unwind edge from bb7, bb7, bb8")
    );
    assert!(
        matches!(&errors[2], ValidationError::MisplacedLandingPad { reason, .. } if reason == "no invoke names this block as its unwind_dest")
    );
}
#[test]
fn resume_precedence_last_result_replacement_and_permissive_shared_cleanup_match() {
    let mut literal = node(Inst::NullPtr);
    literal.results = vec![ValueId::new(10), ValueId::new(11)];
    let f = function(vec![
        block(0, vec![node(invokes(1, 2).remove(0))]),
        block(1, vec![ret()]),
        block(2, vec![pad(&[10, 11]), pad(&[11, 10]), literal, resume(10)]),
        block(3, vec![resume(11)]),
        block(4, vec![resume(99)]),
    ]);
    let errors = parity(&f);
    assert!(errors.iter().any(|error| matches!(error, ValidationError::MisplacedLandingPad { block: 2, reason } if reason.ends_with("type selector, not its exception object"))));
    assert!(errors.iter().any(|error| matches!(error, ValidationError::MisplacedLandingPad { block: 3, reason } if reason.ends_with("the operand is a literal"))));
    assert!(
        !errors
            .iter()
            .any(|error| matches!(error, ValidationError::MisplacedLandingPad { block: 4, .. }))
    );
    let no_pad = function(vec![block(0, vec![resume(0)])]);
    assert!(
        matches!(&parity(&no_pad)[0], ValidationError::MisplacedLandingPad { reason, .. } if reason.ends_with("contains no landingpad"))
    );
}
#[test]
fn wide_normal_entry_source_list_is_built_and_spelled_under_real_observation() {
    let mut blocks = vec![
        block(0, vec![node(invokes(1, 2).remove(0))]),
        block(1, vec![ret()]),
    ];
    blocks.extend((3..300).map(|id| block(id, vec![branch(2)])));
    blocks.push(block(2, vec![pad(&[3, 4]), ret()]));
    let errors = parity(&function(blocks));
    assert!(
        matches!(&errors[0], ValidationError::MisplacedLandingPad { reason, .. } if reason.starts_with("also entered by a non-unwind edge from bb3, bb4") && reason.ends_with("bb299"))
    );
}
