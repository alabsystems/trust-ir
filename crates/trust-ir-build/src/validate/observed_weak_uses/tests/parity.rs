// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_four_direct_routes_and_actual_panic_entry_keep_order_and_locations() {
    let mut m = fixture();
    m.types = vec![Ty::U8];
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        }),
        InstrNode::new(Inst::CallCannotUnwind {
            callee: FuncId::new(9),
            args: vec![],
        }),
        InstrNode::new(Inst::Invoke {
            callee: FuncId::new(9),
            args: vec![],
            normal_dest: BlockId::new(8),
            normal_args: vec![],
            unwind_dest: BlockId::new(9),
        }),
        InstrNode::new(Inst::SeqMap {
            ty: Ty::Sequence(trust_ir::value::TyId::new(0)),
            seq: v(5),
            fwd: FuncId::new(9),
        }),
        InstrNode::new(Inst::Assert {
            cond: v(0),
            kind: AssertKind::BoundsCheck {
                index: v(1),
                len: v(2),
            },
            site: Some(PanicSite {
                entry: FuncId::new(9),
                location: PanicLocation::Value(v(3)),
            }),
        }),
    ];
    let (out, _, _) = run(&m);
    assert_eq!(out.len(), 5);
    assert!(
        matches!(&out[4],ValidationError::DirectCallToWeakDeclaration{location,..}if location.ends_with("instruction 4 (panic site entry)"))
    );
}
#[test]
fn all_three_indirect_routes_preserve_convention_then_complete_signature_errors() {
    for variant in 0..3 {
        let mut m = fixture();
        m.functions[0].blocks[0].body = vec![
            definition(1, symbol("weak")),
            call(variant, 1, 0, CallingConv::Rust),
        ];
        let (out, _, _) = run(&m);
        assert_eq!(out.len(), 2);
        assert!(matches!(
            out[0],
            ValidationError::CallEdgeConvMismatch { .. }
        ));
        assert!(
            matches!(&out[1],ValidationError::CallEdgeSignatureMismatch{declared,actual,..}if declared=="call functy.0 (()) -> (()) through the weak address"&&actual=="target functy.1 ((bool)) -> ((u64))")
        );
    }
}
#[test]
fn equal_nullable_signature_through_copy_keeps_ordinary_success() {
    let mut m = fixture();
    m.functions[0].blocks[0].body.truncate(3);
    m.functions[0].blocks[0].body[2] = call(0, 2, 1, CallingConv::C);
    assert!(run(&m).0.is_empty());
}
#[test]
fn same_name_weak_resolution_uses_last_record_and_not_first_or_id_uniqueness() {
    let mut m = fixture();
    m.functions[0].blocks[0].body =
        vec![definition(1, symbol("weak")), call(0, 1, 0, CallingConv::C)];
    m.functions.push(weak(19, "weak", 0));
    assert!(run(&m).0.is_empty());
    m.functions.swap(1, 2);
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn bodyless_externalweak_only_and_early_no_weak_skip_preserve_success() {
    for body in [false, true] {
        let mut m = fixture();
        if body {
            m.functions[1].blocks.push(Block::new(BlockId::new(0)));
        } else {
            m.functions[1].linkage = Linkage::External;
        }
        let (out, o, end) = run(&m);
        assert!(out.is_empty());
        assert!(
            !o.events[..end]
                .iter()
                .any(|e| e.copy_bytes == size_of::<(u32, &Inst)>() * 3)
        );
    }
}
#[test]
fn duplicate_ids_skip_direct_and_fndef_but_symbol_membership_stays_last_name_based() {
    let mut m = fixture();
    m.functions.push(weak(9, "other", 1));
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        }),
        switch(vec![Constant::FnDef(FuncId::new(9)), symbol("weak")]),
    ];
    let (out, _, _) = run(&m);
    assert_eq!(out.len(), 1);
    assert!(matches!(
        out[0],
        ValidationError::WeakDeclarationAddressNotNullable { .. }
    ));
}
#[test]
fn missing_signatures_keep_convention_error_and_do_not_fabricate_signature_error() {
    for missing_target in [false, true] {
        let mut m = fixture();
        m.functions[0].blocks[0].body = vec![
            definition(1, symbol("weak")),
            call(
                0,
                1,
                if missing_target { 0 } else { 999 },
                CallingConv::Rust,
            ),
        ];
        if missing_target {
            m.functions[1].ty = FuncTyId::new(999);
        }
        let (out, _, _) = run(&m);
        assert_eq!(out.len(), 1);
        assert!(matches!(
            out[0],
            ValidationError::CallEdgeConvMismatch { .. }
        ));
    }
}
#[test]
fn last_singleton_definition_wins_while_multiresult_rows_are_ignored() {
    let mut m = fixture();
    m.functions[0].blocks[0].body = vec![
        definition(1, Constant::Int(1)),
        definition(1, symbol("weak")),
        InstrNode::new(Inst::Const {
            ty: Ty::Ptr,
            value: Constant::Int(0),
        })
        .with_results(vec![v(1), v(2)]),
        call(0, 1, 0, CallingConv::Rust),
    ];
    assert_eq!(run(&m).0.len(), 2);
    m.functions[0].blocks[0].body.swap(0, 1);
    assert!(run(&m).0.is_empty());
}
#[test]
fn cyclic_missing_and_noncopy_origins_terminate_at_exact_local_boundary() {
    let mut m = fixture();
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Copy {
            ty: Ty::Ptr,
            operand: v(2),
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Copy {
            ty: Ty::Ptr,
            operand: v(1),
        })
        .with_result(v(2)),
        call(0, 1, 0, CallingConv::Rust),
        call(1, 99, 0, CallingConv::Rust),
        InstrNode::new(Inst::NullPtr).with_result(v(3)),
        call(2, 3, 0, CallingConv::Rust),
    ];
    assert!(run(&m).0.is_empty());
}
#[test]
fn nested_case_walk_is_root_then_reverse_sibling_order_and_stored_splat_once() {
    let mut m = fixture();
    m.functions.push(weak(19, "second", 1));
    m.functions[0].blocks[0].body = vec![switch(vec![Constant::Closure {
        func: FuncId::new(9),
        captures: vec![
            Constant::FnDef(FuncId::new(19)),
            Constant::Record(vec![
                ("ignored".into(), symbol("weak")),
                (
                    "last".into(),
                    Constant::Splat {
                        elem: Box::new(Constant::FnDef(FuncId::new(9))),
                        len: u64::MAX,
                    },
                ),
            ]),
        ],
    }])];
    let (out, _, _) = run(&m);
    assert_eq!(out.len(), 4);
    assert!(matches!(
        out[0],
        ValidationError::WeakDeclarationAsFnDef { function: 9, .. }
    ));
    assert!(matches!(
        out[1],
        ValidationError::WeakDeclarationAsFnDef { function: 9, .. }
    ));
    assert!(matches!(
        out[2],
        ValidationError::WeakDeclarationAddressNotNullable { .. }
    ));
    assert!(matches!(
        out[3],
        ValidationError::WeakDeclarationAsFnDef { function: 19, .. }
    ));
}
#[test]
fn complete_leaf_and_container_families_keep_nonweak_cases_unchanged() {
    let mut m = fixture();
    m.functions[0].blocks[0].body = vec![switch(vec![Constant::Aggregate(vec![
        Constant::Int(1),
        Constant::U128(u128::MAX),
        Constant::Float(f64::from_bits(0x7ff8000000000001)),
        Constant::Bool(false),
        Constant::Bytes {
            data: vec![0xff],
            utf8: false,
        },
        Constant::PhantomData,
        Constant::Uninit,
        Constant::FnDef(FuncId::new(999)),
        symbol("missing"),
        Constant::Array(vec![]),
        Constant::Vector(vec![]),
        Constant::Sequence(vec![]),
        Constant::Set(vec![]),
    ])])];
    assert!(run(&m).0.is_empty());
}
#[test]
fn actual_unreachable_blocks_and_case_indices_keep_full_unicode_source_locations() {
    let mut m = fixture();
    m.functions[0].name = "é🦀".repeat(300);
    m.functions[0].blocks[0].body.clear();
    let mut b = Block::new(BlockId::new(90));
    b.body = vec![switch(vec![Constant::Int(0), symbol("weak")])];
    m.functions[0].blocks.push(b);
    let (out, _, _) = run(&m);
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::WeakDeclarationAddressNotNullable{location,..}if location==&format!("function '{}' bb90 instruction 0 case 1",m.functions[0].name))
    );
}
