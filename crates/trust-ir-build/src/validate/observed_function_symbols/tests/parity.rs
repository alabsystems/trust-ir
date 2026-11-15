// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_and_distinct_symbols_produce_no_diagnostics() {
    assert!(run(&module(vec![])).0.is_empty());
    assert!(
        run(&module(vec![function(7, "a"), function(0, "b")]))
            .0
            .is_empty()
    );
}
#[test]
fn synthetic_is_exact_case_sensitive_substring_at_every_byte_position() {
    for (i, name) in [
        "<shadowed-by-",
        "prefix<shadowed-by-tail",
        "λ<shadowed-by-中",
        "<shadowed-by-<shadowed-by-",
    ]
    .iter()
    .enumerate()
    {
        assert_eq!(
            run(&module(vec![function(i as u32, name)])).0,
            vec![ValidationError::SyntheticSymbolName {
                function: i as u32,
                name: (*name).into()
            }]
        );
    }
    for name in [
        "",
        "<shadowed-by",
        "shadowed-by-",
        "<Shadowed-by-",
        "<shadowed_by-",
        "λ<retired:by>",
    ] {
        assert!(run(&module(vec![function(0, name)])).0.is_empty());
    }
}
#[test]
fn synthetic_precedes_each_rows_duplicate_and_first_physical_holder_is_never_replaced() {
    let m = fixtures::fixture();
    let (out, _) = run(&m);
    assert_eq!(out.len(), 4);
    assert!(matches!(
        &out[0],
        ValidationError::SyntheticSymbolName { function: 99, .. }
    ));
    assert!(matches!(
        &out[1],
        ValidationError::SyntheticSymbolName { function: 0, .. }
    ));
    assert!(matches!(
        &out[2],
        ValidationError::DuplicateFunctionSymbol {
            first: 99,
            second: 0,
            ..
        }
    ));
    assert!(matches!(
        &out[3],
        ValidationError::DuplicateFunctionSymbol {
            first: 99,
            second: u32::MAX,
            ..
        }
    ));
    let mut m = module(vec![
        function(40, "same"),
        function(2, "same"),
        function(1, "same"),
    ]);
    assert!(run(&m).0.iter().all(|e| matches!(
        e,
        ValidationError::DuplicateFunctionSymbol { first: 40, .. }
    )));
    m.functions.reverse();
    assert!(
        run(&m)
            .0
            .iter()
            .all(|e| matches!(e, ValidationError::DuplicateFunctionSymbol { first: 1, .. }))
    );
}
#[test]
fn all_recorded_producer_pairs_including_none_and_full_other_payload_are_diagnostic_only() {
    for a in fixtures::producers() {
        for b in fixtures::producers() {
            let mut first = function(3, "same");
            first.producer = a.clone();
            let mut second = function(8, "same");
            second.producer = b.clone();
            assert_eq!(
                run(&module(vec![first, second])).0,
                vec![ValidationError::DuplicateFunctionSymbol {
                    name: "same".into(),
                    first: 3,
                    second: 8,
                    first_producer: a.clone(),
                    second_producer: b,
                    first_display_path: None,
                    second_display_path: None,
                }]
            );
        }
    }
}
#[test]
fn optional_display_paths_preserve_none_some_empty_unicode_and_full_raw_tails() {
    for a in [None, Some(""), Some(" λ\n\0"), Some("crate::item")] {
        for b in [None, Some(""), Some(" λ\n\0"), Some("crate::item")] {
            let mut first = function(9, "same");
            first.display_path = a.map(str::to_owned);
            let mut second = function(4, "same");
            second.display_path = b.map(str::to_owned);
            assert_eq!(
                run(&module(vec![first, second])).0,
                vec![ValidationError::DuplicateFunctionSymbol {
                    name: "same".into(),
                    first: 9,
                    second: 4,
                    first_producer: None,
                    second_producer: None,
                    first_display_path: a.map(str::to_owned),
                    second_display_path: b.map(str::to_owned),
                }]
            );
        }
    }
}
#[test]
fn every_unicode_name_byte_and_long_attribution_tail_survives_actual_copies() {
    let name = "λ".repeat(3000) + "tail";
    let mut first = function(7, &name);
    first.producer = Some(Producer::Other("p".repeat(4000) + "producer-tail"));
    first.display_path = Some("中".repeat(2000) + "path-tail");
    let mut second = first.clone();
    second.id = FuncId::new(8);
    second.display_path = Some("".into());
    let mut distinct = first.clone();
    distinct.name = "λ".repeat(3000) + "fail";
    let m = module(vec![first, distinct, second]);
    let (out, _) = run(&m);
    assert_eq!(out.len(), 1);
    assert_eq!(out, fixtures::ordinary(&m));
    for names in [["é", "e\u{301}"], ["x", " x"], ["x", "X"], ["λ\0", "λ"]] {
        assert!(
            run(&module(vec![function(1, names[0]), function(2, names[1])]))
                .0
                .is_empty()
        );
    }
    assert_eq!(
        run(&module(vec![function(1, ""), function(2, "")])).0.len(),
        1
    );
}
#[test]
fn duplicate_ids_do_not_merge_distinct_names_or_exempt_same_name_physical_rows() {
    assert!(
        run(&module(vec![function(5, "a"), function(5, "b")]))
            .0
            .is_empty()
    );
    let (out, _) = run(&module(vec![function(5, "a"), function(5, "a")]));
    assert!(matches!(
        &out[..],
        [ValidationError::DuplicateFunctionSymbol {
            first: 5,
            second: 5,
            ..
        }]
    ));
}
#[test]
fn unrelated_large_type_and_function_body_metadata_is_not_traversed_by_name_rule() {
    let mut m = module(vec![function(0, "one")]);
    m.types = vec![trust_ir::ty::Ty::Tuple(vec![
        trust_ir::ty::Ty::Error;
        10000
    ])];
    let mut block = trust_ir::Block::new(BlockId::new(0));
    block
        .body
        .push(trust_ir::InstrNode::new(trust_ir::inst::Inst::Const {
            ty: trust_ir::ty::Ty::Tuple(vec![trust_ir::ty::Ty::U8; 10000]),
            value: trust_ir::Constant::Aggregate(vec![trust_ir::Constant::Int(3); 10000]),
        }));
    m.functions[0].blocks.push(block);
    let (out, observer) = run(&m);
    assert!(out.is_empty());
    assert!(observer.work < 1000);
}
