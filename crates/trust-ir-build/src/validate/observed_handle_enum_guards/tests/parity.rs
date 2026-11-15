// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn sparse_diamonds_loops_parallel_edges_and_unreachable_queries_match_ordinary() {
    for edges in [
        vec![vec![1, 2], vec![3], vec![3], vec![]],
        vec![vec![1, 1], vec![]],
        vec![vec![1], vec![0, 2], vec![]],
        vec![vec![1, 2], vec![2], vec![1]],
        vec![vec![1], vec![], vec![]],
    ] {
        parity(&graph(&edges));
    }
}
#[test]
fn last_physical_tag_definition_wins_while_no_result_and_nonzero_fields_are_ignored() {
    let mut f = fixture();
    for b in &mut f.blocks {
        b.body
            .retain(|n| !matches!(&n.inst, Inst::ExtractField { .. }));
    }
    f.blocks[0].body.insert(0, tag(55, Some(7)));
    f.blocks[0].body.insert(1, tag(66, Some(7)));
    f.blocks[0].body.insert(2, tag(99, None));
    let mut ignored = tag(111, Some(7));
    if let Inst::ExtractField { field, .. } = &mut ignored.inst {
        *field = 1;
    }
    f.blocks[0].body.insert(3, ignored);
    let expected = Ordinary::new(&f);
    assert_eq!(expected.edges[0].2, 66);
    parity(&f);
}
#[test]
fn only_final_switch_and_explicit_case_edges_are_offered_never_default() {
    let mut f = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
    assert_eq!(selected(&g, f.blocks[1].id, 55, &[0], &mut s), vec![0]);
    assert!(selected(&g, f.blocks[2].id, 55, &[0], &mut s).is_empty());
    g.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let switch = f.blocks[0].body.last().unwrap().clone();
    f.blocks[0].body.insert(0, switch);
    *f.blocks[0].body.last_mut().unwrap() = InstrNode::new(Inst::Return { values: vec![] });
    assert!(Ordinary::new(&f).edges.is_empty());
    parity(&f);
}
#[test]
fn malformed_cfgs_preserve_empty_fail_closed_dominator_answers_without_repair() {
    let mut cases = vec![graph(&[])];
    let mut f = fixture();
    f.entry = BlockId::new(888);
    cases.push(f);
    let mut f = fixture();
    f.blocks.push(f.blocks[0].clone());
    cases.push(f);
    let mut f = fixture();
    f.blocks[1].body.clear();
    cases.push(f);
    let mut f = fixture();
    f.blocks[0].body.push(InstrNode::new(Inst::NullPtr));
    cases.push(f);
    for f in cases {
        assert!(!Ordinary::new(&f).dominators.is_well_formed());
        parity(&f);
    }
}
#[test]
fn selector_scalars_preserve_signed_unsigned_and_boolean_bounds_without_payload_walks() {
    let values = vec![
        Constant::Int(i128::MIN),
        Constant::Int(i128::MAX),
        Constant::U128(0),
        Constant::U128(i128::MAX as u128),
        Constant::U128(i128::MAX as u128 + 1),
        Constant::U128(u128::MAX),
        Constant::Bool(false),
        Constant::Bool(true),
        Constant::Float(f64::NAN),
        Constant::Bytes {
            data: vec![3; 100_000],
            utf8: true,
        },
        Constant::Aggregate(vec![Constant::Bool(true); 4096]),
    ];
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    for value in &values {
        assert_eq!(
            build::selector(
                value,
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            )
            .unwrap(),
            super::super::super::constant_selector_value(value)
        );
    }
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
}
#[test]
fn duplicate_discriminant_stops_at_second_match_and_does_not_read_tail() {
    let f = fixture();
    let trace = |ds: &[i128]| {
        let mut o = Observer::default();
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
        let begin = calls.get();
        assert!(selected(&g, f.blocks[1].id, 55, ds, &mut s).is_empty());
        let end = calls.get();
        g.retire_observed(&mut s, site()).unwrap();
        drop(s);
        o.events[begin..end].to_vec()
    };
    assert_eq!(trace(&[0, 0]), trace(&[0, 0, i128::MIN, i128::MAX]));
}
#[test]
fn non_tag_predicate_short_circuits_without_reading_later_types_or_results() {
    let mut a = fixture();
    if let Inst::ExtractField { field, .. } = &mut a.blocks[0].body[0].inst {
        *field = 1;
    }
    let mut b = a.clone();
    for _ in 0..10_000 {
        b.blocks[0].body.push(tag(66, Some(8)));
    }
    let trace = |f: &Function| {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            ObservedHandleEnumGuards::function_reads_a_non_tag_lane_observed(f, &mut s, site())
                .unwrap()
        );
        drop(s);
        o.events
    };
    assert_eq!(trace(&a), trace(&b));
    parity(&a);
}
#[test]
fn unread_selector_payload_changes_leave_exact_constructor_trace_unchanged() {
    let mut a = fixture();
    if let Inst::Switch { cases, .. } = &mut a.blocks[0].body.last_mut().unwrap().inst {
        cases[0].value = Constant::Bytes {
            data: vec![],
            utf8: false,
        };
    }
    let mut b = a.clone();
    if let Inst::Switch { cases, .. } = &mut b.blocks[0].body.last_mut().unwrap().inst {
        cases[0].value = Constant::Bytes {
            data: vec![0; 1_000_000],
            utf8: true,
        };
    }
    let trace = |f: &Function| {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        ObservedHandleEnumGuards::new_observed(f, &mut s, site())
            .unwrap()
            .retire_observed(&mut s, site())
            .unwrap();
        drop(s);
        o.events
    };
    assert_eq!(trace(&a), trace(&b));
    parity(&b);
}
