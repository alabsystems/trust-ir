// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn group_order_is_function_mismatch_definition_global_shadows_then_global_and_body_addresses() {
    let mut m = bad_fixture();
    m.globals = vec![
        global("clean_inc", Some(address("clean_dec"))),
        global("data", Some(address("clean_inc"))),
    ];
    m.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Const {
            ty: Ty::Ptr,
            value: address("clean_is_exclusive"),
        }));
    let out = run(&m).0;
    assert_eq!(out.len(), 6);
    assert!(matches!(
        out[0],
        ValidationError::RcEntryPointSignatureMismatch { .. }
    ));
    assert!(matches!(
        out[1],
        ValidationError::RcEntryPointDefinedLocally { .. }
    ));
    assert!(matches!(
        out[2],
        ValidationError::RcEntryPointShadowedByGlobal { .. }
    ));
    assert!(
        matches!(&out[3],ValidationError::RcEntryPointAddressTaken{location,symbol}if location=="global 'clean_inc'"&&symbol=="clean_dec")
    );
    assert!(
        matches!(&out[5],ValidationError::RcEntryPointAddressTaken{location,..}if location=="function 'clean_inc' bb4294967295")
    );
}
#[test]
fn all_actual_constant_child_variants_preserve_lifo_order_and_splat_visits_once() {
    let mut m = fixture();
    m.globals.push(global(
        "raw λ'\n",
        Some(Constant::Aggregate(vec![
            Constant::Array(vec![address("clean_inc")]),
            Constant::Vector(vec![address("clean_dec")]),
            Constant::Sequence(vec![address("clean_inc")]),
            Constant::Set(vec![address("clean_dec")]),
            Constant::Record(vec![("unread".into(), address("clean_inc"))]),
            Constant::Closure {
                func: FuncId::new(10),
                captures: vec![address("clean_dec")],
            },
            Constant::Splat {
                elem: Box::new(address("clean_is_exclusive")),
                len: u64::MAX,
            },
        ])),
    ));
    let out = run(&m).0;
    let names: Vec<_> = out
        .iter()
        .map(|e| match e {
            ValidationError::RcEntryPointAddressTaken { location, symbol } => {
                assert_eq!(location, "global 'raw λ'\n'");
                symbol.as_str()
            }
            _ => panic!("wrong kind"),
        })
        .collect();
    assert_eq!(
        names,
        vec![
            "clean_is_exclusive",
            "clean_dec",
            "clean_inc",
            "clean_dec",
            "clean_inc",
            "clean_dec",
            "clean_inc"
        ]
    );
}
#[test]
fn scalar_and_record_payloads_unmatched_symbols_and_absent_initializers_remain_unread() {
    let mut m = fixture();
    m.globals = vec![
        global("none", None),
        global(
            "data",
            Some(Constant::Record(vec![(
                "unread".repeat(1000),
                Constant::Aggregate(vec![
                    Constant::Bytes {
                        data: vec![255; 100000],
                        utf8: true,
                    },
                    Constant::Float(f64::NAN),
                    Constant::FnDef(FuncId::new(u32::MAX)),
                    Constant::U128(u128::MAX),
                    Constant::PhantomData,
                    Constant::Uninit,
                    address("not_pinned"),
                ]),
            )])),
        ),
    ];
    assert!(run(&m).0.is_empty());
}
#[test]
fn duplicate_unreachable_physical_blocks_and_addresses_are_not_deduplicated() {
    let mut m = fixture();
    let mut b = Block::new(BlockId::new(u32::MAX));
    b.body.push(InstrNode::new(Inst::Const {
        ty: Ty::Error,
        value: address("clean_dec"),
    }));
    m.functions[0].blocks = vec![b.clone(), b];
    let out = run(&m).0;
    assert_eq!(out.len(), 3);
    assert!(matches!(
        out[0],
        ValidationError::RcEntryPointDefinedLocally { .. }
    ));
    assert!(out[1..].iter().all(|e|matches!(e,ValidationError::RcEntryPointAddressTaken{location,..}if location.ends_with("bb4294967295"))));
}
#[test]
fn deep_and_wide_actual_constants_have_no_fixed_depth_or_count_truncation() {
    let mut m = fixture();
    let mut tree = address("clean_dec");
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
            (0..128).map(|_| address("clean_inc")).collect(),
        )),
    ));
    assert_eq!(run(&m).0.len(), 129);
}
