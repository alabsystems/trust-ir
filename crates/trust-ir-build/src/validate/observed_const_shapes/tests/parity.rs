// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_and_scalar_only_sources_match_complete_original_funnel() {
    for m in [Module::new(""), fixture()] {
        run(&m, false);
        run(&m, true);
    }
    let mut m = fixture();
    m.globals.clear();
    m.functions[0].blocks[0].body = vec![literal(Ty::Bool, Constant::Bool(true))];
    assert!(run(&m, false).0.is_empty());
}
#[test]
fn canonical_u128_error_precedes_typed_error_and_keeps_exact_whitespace() {
    let mut m = fixture();
    m.functions.clear();
    let out = run(&m, false).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::ConstTypeMismatch{location,expected,actual}if location=="global 'G'"&&expected=="canonical integer spelling (values <= i128::MAX are Constant::Int;                        Constant::U128 only above)"&&actual=="int")
    );
}
#[test]
fn nested_first_bad_integer_spelling_is_one_canonical_error_per_root() {
    let mut m = fixture();
    m.functions.clear();
    m.types.push(Ty::U128);
    m.globals[0].ty = Ty::Array(TyId::new(3), 2);
    m.globals[0].initializer = Some(Constant::Array(vec![Constant::U128(1), Constant::U128(2)]));
    let out = run(&m, false).0;
    assert_eq!(out.len(), 1);
    assert!(matches!(&out[0],ValidationError::ConstTypeMismatch{actual,..}if actual=="array[2]"));
}
#[test]
fn nominal_global_storage_is_handle_first_additive_to_initializer_and_checks_externs() {
    let mut m = fixture();
    m.functions.clear();
    let h = Ty::handle("H", "rt::H");
    let dialect = Ty::Dialect(Box::new(trust_ir::DialectTy::new("d", "T", 1)));
    m.globals = vec![
        global("handle", h.clone(), None),
        global("dialect", dialect.clone(), None),
        global(
            "both",
            Ty::Tuple(vec![h, dialect]),
            Some(Constant::Aggregate(vec![
                Constant::Int(0),
                Constant::Int(0),
            ])),
        ),
    ];
    let out = run(&m, true).0;
    assert!(matches!(out[0], ValidationError::InvalidHandleUse { .. }));
    assert!(matches!(out[1], ValidationError::InvalidDialectType { .. }));
    assert!(matches!(out[2], ValidationError::InvalidHandleUse { .. }));
    run(&m, false);
}
#[test]
fn original_global_then_interleaved_const_switch_const_error_order_and_locations() {
    let m = fixture();
    let out = run(&m, false).0;
    let locations: Vec<_> = out
        .iter()
        .filter_map(|e| {
            if let ValidationError::ConstTypeMismatch { location, .. } = e {
                Some(location.as_str())
            } else {
                None
            }
        })
        .collect();
    assert_eq!(
        locations,
        vec![
            "global 'G'",
            "global 'G'",
            "function 'body' bb7",
            "function 'body' bb7 switch case 0",
            "function 'body' bb7 switch case 1",
            "function 'body' bb7 switch case 1",
            "function 'body' bb7",
            "function 'body' bb7"
        ]
    );
}
#[test]
fn sparse_direct_selector_return_is_typed_but_duplicate_id_is_not_chosen() {
    let mut m = fixture();
    m.globals.clear();
    m.functions[0].blocks[0].params.clear();
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(900),
            args: vec![],
        })
        .with_result(v(1)),
        switch(v(1), vec![Constant::Int(300)]),
    ];
    assert_eq!(run(&m, false).0.len(), 1);
    let duplicate = m.functions[1].clone();
    m.functions.push(duplicate);
    assert!(run(&m, false).0.is_empty());
}
#[test]
fn selector_refinement_unwraps_exactly_one_recorded_row() {
    let mut m = fixture();
    m.globals.clear();
    m.functions[0].blocks[0].body = vec![switch(v(1), vec![Constant::Int(300)])];
    for (ty, errors) in [
        (Ty::Refine(TyId::new(0), PredId::new(0)), 1),
        (Ty::Refine(TyId::new(2), PredId::new(0)), 0),
        (Ty::Refine(TyId::new(999), PredId::new(0)), 0),
    ] {
        m.functions[0].blocks[0].params[0].1 = ty;
        assert_eq!(run(&m, false).0.len(), errors);
    }
}
#[test]
fn absent_bool_and_other_noninteger_selectors_keep_local_literal_skip() {
    let mut m = fixture();
    m.globals.clear();
    m.functions[0].blocks[0].body = vec![switch(v(1), vec![Constant::U128(1), Constant::Int(300)])];
    for ty in [Ty::Bool, Ty::F64, Ty::Tuple(vec![Ty::U8]), Ty::Ptr] {
        m.functions[0].blocks[0].params[0].1 = ty;
        assert!(run(&m, false).0.is_empty());
    }
    m.functions[0].blocks[0].params.clear();
    assert!(run(&m, false).0.is_empty());
}
#[test]
fn char_and_every_integer_selector_use_actual_target_range_and_case_order() {
    let mut m = fixture();
    m.globals.clear();
    for ty in [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::Isize,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Usize,
        Ty::Char,
    ] {
        m.functions[0].blocks[0].params[0].1 = ty;
        m.functions[0].blocks[0].body = vec![switch(
            v(1),
            vec![
                Constant::Int(-1),
                Constant::Int(i128::MAX),
                Constant::Int(0xd800),
            ],
        )];
        run(&m, false);
    }
}
#[test]
fn later_physical_definition_and_function_local_cache_scopes_match_original() {
    let mut m = fixture();
    m.globals.clear();
    m.functions[0].blocks[0].params[0].1 = Ty::Bool;
    m.functions[0].blocks[0].body = vec![switch(v(1), vec![Constant::Int(300)])];
    let mut later = Block::new(BlockId::new(99));
    later.params = vec![(v(1), Ty::U8)];
    m.functions[0].blocks.push(later);
    let mut second = m.functions[0].clone();
    second.id = FuncId::new(99);
    second.name = "second".into();
    second.blocks.pop();
    m.functions.push(second);
    let out = run(&m, false).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::ConstTypeMismatch{location,..}if location=="function 'body' bb7 switch case 0")
    );
}
#[test]
fn splat_canonicality_visits_one_stored_child_not_its_logical_count() {
    let mut m = fixture();
    m.functions.clear();
    m.types.push(Ty::U128);
    m.globals[0].ty = Ty::Array(TyId::new(3), u64::MAX);
    m.globals[0].initializer = Some(Constant::Splat {
        elem: Box::new(Constant::U128(1)),
        len: u64::MAX,
    });
    let out = run(&m, false).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::ConstTypeMismatch{actual,..}if actual.starts_with("splat["))
    );
}
#[test]
fn global_names_block_ids_and_case_locations_preserve_full_unicode_source() {
    let mut m = fixture();
    m.globals[0].name = "é🦀Global".repeat(100);
    m.functions[0].name = "é🦀Function".repeat(100);
    m.functions[0].blocks[0].id = BlockId::new(u32::MAX);
    run(&m, true);
}
#[test]
fn tensor_blob_rules_match_the_original_funnel() {
    let mut m = fixture();
    m.globals.clear();
    let digest = m.intern_blob(vec![1, 2, 3, 4]);
    let absent = trust_ir::blob::BlobDigest::of(&[9u8]);
    let tensor = Ty::Tensor(Box::new(Ty::U8), 1);
    let pair = Ty::Tuple(vec![tensor.clone(), Ty::U8]);
    let blob = |digest, dims: &[u64]| Constant::TensorBlob {
        digest,
        dims: dims.to_vec(),
    };
    m.globals
        .push(global("W", tensor.clone(), Some(blob(digest, &[4]))));
    m.globals.push(global(
        "T",
        pair.clone(),
        Some(Constant::Aggregate(vec![
            blob(digest, &[4]),
            Constant::Int(0),
        ])),
    ));
    m.functions[0].blocks[0].body = vec![
        literal(tensor.clone(), blob(digest, &[4])),
        literal(tensor.clone(), blob(digest, &[2, 2])),
        literal(tensor.clone(), blob(digest, &[5])),
        literal(tensor.clone(), blob(absent, &[1])),
        literal(
            pair,
            Constant::Aggregate(vec![blob(digest, &[4]), Constant::Int(0)]),
        ),
        literal(
            Ty::Tensor(Box::new(Ty::U64), 2),
            blob(digest, &[u64::MAX, 2]),
        ),
    ];
    let out = run(&m, false).0;
    let reasons: Vec<_> = out
        .iter()
        .filter_map(|e| match e {
            ValidationError::InvalidTensorBlob { reason, .. } => Some(&reason[..4]),
            ValidationError::MissingBlob { .. } => Some("miss"),
            _ => None,
        })
        .collect();
    assert_eq!(
        reasons,
        ["(C1)", "(C1)", "(C2)", "(C4)", "miss", "(C1)", "(C3)"],
        "{out:?}"
    );
}
