// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn group_order_is_functions_then_global_shadows_then_global_and_body_symbol_addresses() {
    let (mut m, r) = bad_fixture();
    m.globals = vec![
        global("pinned", Some(address("pinned"))),
        global("data", Some(address("pinned"))),
    ];
    m.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Const {
            ty: Ty::Ptr,
            value: address("pinned"),
        }));
    let out = run(&m, &r).0;
    assert_eq!(out.len(), 6);
    assert!(matches!(
        out[0],
        ValidationError::HandleEntryPointSignatureMismatch { .. }
    ));
    assert!(matches!(
        out[1],
        ValidationError::HandleEntryPointDefinedLocally { .. }
    ));
    assert!(matches!(
        out[2],
        ValidationError::HandleEntryPointShadowedByGlobal { .. }
    ));
    assert!(
        matches!(&out[3],ValidationError::HandleEntryPointAddressTaken{location,..}if location=="global 'pinned'")
    );
    assert!(
        matches!(&out[4],ValidationError::HandleEntryPointAddressTaken{location,..}if location=="global 'data'")
    );
    assert!(
        matches!(&out[5],ValidationError::HandleEntryPointAddressTaken{location,..}if location=="function 'pinned' bb3")
    );
}
#[test]
fn every_immediate_child_variant_preserves_original_stored_push_then_reverse_visit_order() {
    let (mut m, r) = fixture();
    let nested = Constant::Aggregate(vec![
        Constant::Array(vec![address("pinned"), Constant::Int(1)]),
        Constant::Vector(vec![address("pinned")]),
        Constant::Sequence(vec![address("pinned")]),
        Constant::Set(vec![address("pinned")]),
        Constant::Record(vec![("unread name".into(), address("pinned"))]),
        Constant::Closure {
            func: FuncId::new(123),
            captures: vec![address("pinned")],
        },
        Constant::Splat {
            elem: Box::new(address("pinned")),
            len: u64::MAX,
        },
    ]);
    m.globals.push(global("raw λ'\n", Some(nested)));
    let out = run(&m, &r).0;
    assert_eq!(out.len(), 7);
    assert!(out.iter().all(|e|matches!(e,ValidationError::HandleEntryPointAddressTaken{location,..}if location=="global 'raw λ'\n'")));
}
#[test]
fn exact_different_symbols_expose_original_lifo_order_duplicates_and_first_match_only() {
    let (mut m, mut r) = fixture();
    r.pins[0].entry_points = Box::leak(
        vec![
            entry("pinned", vec![], vec![]),
            entry("other", vec![], vec![]),
        ]
        .into_boxed_slice(),
    );
    m.functions.clear();
    m.globals.push(global(
        "G",
        Some(Constant::Aggregate(vec![
            address("pinned"),
            Constant::Record(vec![("name".into(), address("other"))]),
            address("pinned"),
        ])),
    ));
    let out = run(&m, &r).0;
    assert_eq!(
        out.iter()
            .map(|e| match e {
                ValidationError::HandleEntryPointAddressTaken { symbol, .. } => symbol.as_str(),
                _ => panic!("wrong error"),
            })
            .collect::<Vec<_>>(),
        vec!["pinned", "other", "pinned"]
    );
}
#[test]
fn absent_initializers_and_unmatched_symbols_ignore_unrelated_scalar_record_and_splat_payloads() {
    let (mut m, r) = fixture();
    m.globals = vec![
        global("none", None),
        global(
            "data",
            Some(Constant::Record(vec![(
                "record λ\0".repeat(1000),
                Constant::Aggregate(vec![
                    Constant::Bytes {
                        data: vec![255; 100000],
                        utf8: true,
                    },
                    Constant::Float(f64::from_bits(0x7ff0000000000001)),
                    Constant::FnDef(FuncId::new(u32::MAX)),
                    Constant::Bool(false),
                    Constant::U128(u128::MAX),
                    Constant::PhantomData,
                    Constant::Uninit,
                    address("not_pinned"),
                ]),
            )])),
        ),
    ];
    assert!(run(&m, &r).0.is_empty());
}
#[test]
fn repeated_unreachable_physical_blocks_and_constants_are_all_checked_without_deduplication() {
    let (mut m, r) = fixture();
    let mut b = Block::new(BlockId::new(u32::MAX));
    b.body = vec![InstrNode::new(Inst::Const {
        ty: Ty::Error,
        value: address("pinned"),
    })];
    m.functions[0].blocks = vec![b.clone(), b];
    let out = run(&m, &r).0;
    assert_eq!(out.len(), 3);
    assert!(matches!(
        out[0],
        ValidationError::HandleEntryPointDefinedLocally { .. }
    ));
    assert!(out[1..].iter().all(|e|matches!(e,ValidationError::HandleEntryPointAddressTaken{location,..}if location.ends_with("bb4294967295"))));
}
#[test]
fn deep_and_wide_actual_constant_trees_have_no_truncation_and_scalar_payloads_are_unread() {
    let (mut m, r) = fixture();
    let mut tree = address("pinned");
    for _ in 0..256 {
        tree = Constant::Splat {
            elem: Box::new(tree),
            len: u64::MAX,
        };
    }
    m.globals.push(global("deep", Some(tree)));
    m.globals.push(global(
        "wide",
        Some(Constant::Aggregate(
            (0..128).map(|_| address("pinned")).collect(),
        )),
    ));
    assert_eq!(run(&m, &r).0.len(), 129);
}
