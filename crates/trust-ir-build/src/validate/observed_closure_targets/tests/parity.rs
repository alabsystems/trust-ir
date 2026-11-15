// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_seed_and_reverse_instruction_copy_chain_match_complete_original_map() {
    run(&fixture());
}
#[test]
fn copy_fixedpoint_resolves_reverse_physical_block_order_without_new_round_owner() {
    let mut f = fixture();
    f.blocks.clear();
    for (id, node) in [(3, copy(12, 11)), (2, copy(11, 10)), (1, constant(10, 99))] {
        let mut b = Block::new(BlockId::new(id));
        b.body.push(node);
        f.blocks.push(b);
    }
    run(&f);
}
#[test]
fn duplicate_constant_seed_keeps_last_physical_target_even_on_malformed_ssa() {
    let mut f = fixture();
    f.blocks[0]
        .body
        .extend([constant(10, 77), constant(10, 79)]);
    run(&f);
    assert_eq!(
        super::super::super::local_closure_constant_targets(&f)[&10],
        FuncId::new(79)
    );
}
#[test]
fn first_copy_owner_is_retained_and_later_duplicate_copy_cannot_overwrite_it() {
    let mut f = fixture();
    f.blocks[0].body = vec![constant(10, 1), constant(20, 2), copy(30, 10), copy(30, 20)];
    run(&f);
    assert_eq!(
        super::super::super::local_closure_constant_targets(&f)[&30],
        FuncId::new(1)
    );
}
#[test]
fn only_first_result_of_seed_and_copy_is_read_as_original_requires() {
    let mut f = fixture();
    f.blocks[0].body[2].results = vec![v(10), v(20)];
    f.blocks[0].body[1].results = vec![v(11), v(21)];
    run(&f);
    let old = super::super::super::local_closure_constant_targets(&f);
    assert!(!old.contains_key(&20) && !old.contains_key(&21));
}
#[test]
fn unseeded_copy_cycles_and_unrelated_constants_stay_dynamic_empty_data() {
    let mut f = fixture();
    f.blocks[0].body = vec![
        copy(10, 11),
        copy(11, 10),
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(3),
        })
        .with_result(v(12)),
    ];
    run(&f);
    assert!(super::super::super::local_closure_constant_targets(&f).is_empty());
}
#[test]
fn large_unrelated_capture_payloads_are_not_walked_by_this_exact_original_map() {
    let small = fixture();
    let mut huge = small.clone();
    if let Inst::Const {
        value: Constant::Closure { captures, .. },
        ..
    } = &mut huge.blocks[0].body[2].inst
    {
        captures.push(Constant::Bytes {
            data: "λ\0unread".repeat(100000).into_bytes(),
            utf8: true,
        });
    }
    let (a, ae) = run(&small);
    let (b, be) = run(&huge);
    assert_eq!(ae, be);
    assert_eq!(a.events[..ae], b.events[..be]);
}
#[test]
fn missing_pointer_query_is_semantic_none_and_source_function_remains_unchanged() {
    let f = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = ObservedLocalClosureTargets::new_observed(&f, &mut s, site()).unwrap();
    assert!(
        a.get_observed(v(u32::MAX), &mut s, site())
            .unwrap()
            .is_none()
    );
    a.retire_observed(&mut s, site()).unwrap();
    assert_eq!(f.blocks[0].body.len(), 3);
}
