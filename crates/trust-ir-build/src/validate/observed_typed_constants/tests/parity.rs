// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_scalar_carriers_match_original_integer_char_pointer_width_and_float_rules() {
    let mut m = fixture();
    for (c, t) in [
        (Constant::Int(-1), Ty::U8),
        (Constant::Int(255), Ty::U8),
        (Constant::U128(u128::MAX), Ty::U128),
        (Constant::U128(1), Ty::U128),
        (Constant::Float(f64::from_bits(0x7ff8000000000042)), Ty::F64),
        (Constant::Bool(true), Ty::Bool),
        (Constant::PhantomData, Ty::Unit),
        (sym("raw", 0), Ty::Ptr),
    ] {
        run(&m, &c, &t);
    }
    m.target_info.as_mut().unwrap().pointer_size = 4;
    assert_eq!(run(&m, &Constant::Int(1i128 << 32), &Ty::Usize).0.len(), 1);
    m.target_info.as_mut().unwrap().pointer_size = 8;
    assert!(
        run(&m, &Constant::Int(1i128 << 32), &Ty::Usize)
            .0
            .is_empty()
    );
}
#[test]
fn invalid_char_keeps_both_original_range_then_fallback_errors() {
    let m = fixture();
    let out = run(&m, &Constant::Int(0xd800), &Ty::Char).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::ConstTypeMismatch{expected,..}if expected.contains("Unicode scalar"))
    );
    run(&m, &Constant::Int(0x10ffff), &Ty::Char);
}
#[test]
fn uninit_is_local_type_agnostic_without_placement_authority() {
    let m = fixture();
    for t in [
        Ty::Bool,
        Ty::Ref(Box::new(Ty::Bool)),
        Ty::Enum(EnumId::new(999)),
    ] {
        assert!(run(&m, &Constant::Uninit, &t).0.is_empty());
    }
}
#[test]
fn array_arity_precedes_missing_element_and_uniformity_preserves_children() {
    let m = fixture();
    let c = Constant::Array(vec![Constant::Int(300); 2]);
    let out = run(&m, &c, &Ty::Array(TyId::new(0), 2)).0;
    assert_eq!(out.len(), 3);
    assert!(
        matches!(&out[0],ValidationError::NonCanonicalUniformArray{spelling,..}if spelling=="an array of 2 equal elements is spelled `splat[ 300; 2 ]`")
    );
    let out = run(&m, &c, &Ty::Array(TyId::new(999), 3)).0;
    assert_eq!(out.len(), 1);
    assert!(matches!(out[0], ValidationError::ConstTypeMismatch { .. }));
}
#[test]
fn uniform_composite_float_and_list_alias_spellings_match_original_exactly() {
    let mut m = fixture();
    m.types.push(Ty::Tuple(vec![Ty::Bool]));
    for c in [
        Constant::Array(vec![Constant::Aggregate(vec![Constant::Bool(true)]); 2]),
        Constant::Aggregate(vec![Constant::Array(vec![]), Constant::Aggregate(vec![])]),
    ] {
        run(&m, &c, &Ty::Array(TyId::new(4), 2));
    }
    m.types[4] = Ty::F64;
    run(
        &m,
        &Constant::Array(vec![Constant::Float(-0.0); 2]),
        &Ty::Array(TyId::new(4), 2),
    );
}
#[test]
fn splat_uses_one_stored_child_and_count_is_never_expanded() {
    let m = fixture();
    for n in [0, 1, 2, u64::MAX] {
        let c = Constant::Splat {
            elem: Box::new(Constant::Int(300)),
            len: n,
        };
        let out = run(&m, &c, &Ty::Array(TyId::new(0), n)).0;
        assert_eq!(out.len(), if n < 2 { 2 } else { 1 });
    }
    let c = Constant::Splat {
        elem: Box::new(Constant::Int(300)),
        len: 3,
    };
    assert_eq!(run(&m, &c, &Ty::Array(TyId::new(0), 2)).0.len(), 1);
}
#[test]
fn bytes_preserve_element_length_utf8_and_raw_uniform_error_order() {
    let m = fixture();
    let c = Constant::Bytes {
        data: vec![0xff, 0xff],
        utf8: true,
    };
    let out = run(&m, &c, &Ty::Array(TyId::new(1), 3)).0;
    assert_eq!(out.len(), 3);
    assert!(
        matches!(&out[2],ValidationError::ConstTypeMismatch{expected,..}if expected=="valid UTF-8 under the utf8 claim")
    );
    for utf8 in [false, true] {
        for data in [vec![], vec![7], vec![7, 7], "é".as_bytes().to_vec()] {
            run(
                &m,
                &Constant::Bytes {
                    data: data.clone(),
                    utf8,
                },
                &Ty::Array(TyId::new(0), data.len() as u64),
            );
        }
    }
    run(&m, &c, &Ty::Array(TyId::new(999), 2));
}
#[test]
fn sequence_set_vector_tuple_children_keep_exact_stored_paths() {
    let m = fixture();
    for (c, t) in [
        (
            Constant::Sequence(vec![Constant::Bool(true), Constant::Int(300)]),
            Ty::Sequence(TyId::new(0)),
        ),
        (
            Constant::Set(vec![Constant::Int(3), Constant::Int(300)]),
            Ty::Set(TyId::new(0), SetRepr::Boxed),
        ),
        (
            Constant::Vector(vec![Constant::Int(3), Constant::Int(300)]),
            Ty::Vector(Box::new(Ty::U8), 2),
        ),
        (
            Constant::Aggregate(vec![Constant::Bool(true), Constant::Int(300)]),
            Ty::Tuple(vec![Ty::Bool, Ty::U8]),
        ),
    ] {
        let out = run(&m, &c, &t).0;
        assert!(out.iter().any(|e|matches!(e,ValidationError::ConstTypeMismatch{location,..}if location=="constant.root[1]")));
    }
}
#[test]
fn actual_offindex_nominal_definitions_and_positional_field_types_are_retained() {
    let mut m = fixture();
    m.structs[0].id = StructId::new(80);
    m.records[0].id = RecordId::new(81);
    let c = Constant::Aggregate(vec![Constant::Bool(false), Constant::Int(300)]);
    for t in [Ty::Struct(StructId::new(80)), Ty::Record(RecordId::new(81))] {
        assert_eq!(run(&m, &c, &t).0.len(), 1);
    }
    for t in [
        Ty::Struct(StructId::new(999)),
        Ty::Record(RecordId::new(999)),
    ] {
        assert!(matches!(
            &run(&m, &c, &t).0[..],
            [ValidationError::ConstTypeReferenceNotFound { .. }]
        ));
    }
}
#[test]
fn wrong_record_name_reports_expected_path_and_skips_that_whole_subtree() {
    let m = fixture();
    let c = Constant::Record(vec![
        (
            "wrong".into(),
            Constant::Closure {
                func: FuncId::new(12),
                captures: vec![Constant::Int(999)],
            },
        ),
        ("byte".into(), Constant::Int(300)),
    ]);
    let out = run(&m, &c, &Ty::Record(RecordId::new(0))).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::ConstTypeMismatch{location,expected,actual}if location=="constant.root.flag"&&expected=="field 'flag'"&&actual=="field 'wrong' at index 0")
    );
}
#[test]
fn enums_keep_assignment_head_discriminant_inhabitance_and_payload_precedence() {
    let mut m = fixture();
    let t = Ty::Enum(EnumId::new(0));
    for c in [
        Constant::Aggregate(vec![]),
        Constant::Aggregate(vec![Constant::Bool(false)]),
        Constant::Aggregate(vec![Constant::Int(999)]),
        Constant::Aggregate(vec![Constant::Int(2)]),
        Constant::Aggregate(vec![Constant::Int(0)]),
        Constant::Aggregate(vec![Constant::Int(0), Constant::Int(300)]),
        Constant::Aggregate(vec![Constant::Int(1)]),
    ] {
        run(&m, &c, &t);
    }
    let out = run(&m, &Constant::Aggregate(vec![Constant::Int(2)]), &t).0;
    assert!(matches!(
        &out[..],
        [ValidationError::UninhabitedVariantConstructed { variant: 2, .. }]
    ));
    m.enums[0].discriminants = vec![Some(0), Some(0)];
    assert_eq!(run(&m, &Constant::Aggregate(vec![]), &t).0.len(), 1);
}
#[test]
fn closure_capture_types_survive_outer_sequences_and_no_capture_indices_are_added() {
    let mut m = fixture();
    m.types.push(Ty::Closure(ClosureTyId::new(0)));
    let c = Constant::Sequence(vec![Constant::Closure {
        func: FuncId::new(9),
        captures: vec![Constant::Bool(true), Constant::Int(300)],
    }]);
    let out = run(&m, &c, &Ty::Sequence(TyId::new(4))).0;
    assert!(
        matches!(&out[..],[ValidationError::ConstTypeMismatch{location,..}]if location=="constant.root[0]")
    );
    run(
        &m,
        &Constant::Closure {
            func: FuncId::new(9),
            captures: vec![],
        },
        &Ty::Closure(ClosureTyId::new(0)),
    );
    run(&m, &c, &Ty::Sequence(TyId::new(999)));
}
#[test]
fn fndef_uniqueness_and_weak_spelling_diagnostics_precede_other_errors() {
    let mut m = fixture();
    for id in [9, 12, 999] {
        for sig in [0, 1] {
            run(
                &m,
                &Constant::FnDef(FuncId::new(id)),
                &Ty::Func(FuncTyId::new(sig)),
            );
        }
    }
    let duplicate = m.functions[0].clone();
    m.functions.push(duplicate);
    assert_eq!(
        run(
            &m,
            &Constant::FnDef(FuncId::new(9)),
            &Ty::Func(FuncTyId::new(0))
        )
        .0
        .len(),
        1
    );
    for addend in [0, -7, i64::MIN] {
        for t in [Ty::Ptr, Ty::Bool] {
            run(&m, &sym("weak", addend), &t);
        }
    }
}
#[test]
fn deep_nested_paths_and_long_unicode_type_and_field_diagnostics_are_exact() {
    let mut m = fixture();
    m.records[0].fields[0].name = "é🦀field".repeat(100);
    let (c, t) = nested();
    let out = run_at(&m, &c, &t, &"é🦀base".repeat(100)).0;
    assert_eq!(out.len(), 4);
    let mut c = Constant::Int(300);
    let mut t = Ty::U8;
    for _ in 0..80 {
        c = Constant::Aggregate(vec![c]);
        t = Ty::Tuple(vec![t]);
    }
    assert_eq!(run(&m, &c, &t).0.len(), 1);
}

#[test]
fn nominal_item_constants_preserve_exact_ids_and_actual_header_refusals() {
    let mut m = fixture();
    let id = FuncId::new(7001);
    m.functions
        .push(Function::new(id, "item", FuncTyId::new(0), BlockId::new(0)));
    let ty = Ty::FnItem(id);
    assert!(run(&m, &Constant::FnItem(id), &ty).0.is_empty());
    assert_eq!(
        run(&m, &Constant::FnItem(FuncId::new(7002)), &ty).0.len(),
        1
    );
    let row = m.functions.last().unwrap().clone();
    m.functions.push(row);
    assert_eq!(run(&m, &Constant::FnItem(id), &ty).0.len(), 1);
    m.functions.pop();
    m.functions.last_mut().unwrap().ty = FuncTyId::new(999);
    assert_eq!(run(&m, &Constant::FnItem(id), &ty).0.len(), 1);
}
