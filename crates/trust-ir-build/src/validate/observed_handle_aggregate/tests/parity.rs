// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn make_whole_struct_tuple_and_enum_checks_only_exact_handle_reaching_declared_lanes() {
    let (m, f) = fixture();
    for ty in [tuple(), Ty::Struct(StructId::new(0))] {
        assert_eq!(
            run(
                &m,
                &f,
                &make(ty.clone(), None, &[0, 5]),
                BlockId::new(17),
                true
            )
            .0,
            Ok(())
        );
        assert!(
            run(&m, &f, &make(ty, None, &[1, 5]), BlockId::new(17), true)
                .0
                .is_err()
        );
    }
    assert_eq!(
        run(
            &m,
            &f,
            &make(Ty::Enum(EnumId::new(0)), Some(0), &[0]),
            BlockId::new(17),
            true
        )
        .0,
        Ok(())
    );
    assert_eq!(
        run(
            &m,
            &f,
            &make(Ty::Enum(EnumId::new(0)), Some(1), &[1]),
            BlockId::new(17),
            true
        )
        .0,
        Ok(())
    );
}
#[test]
fn make_missing_variants_unknown_declarations_and_wrong_full_lane_count_refuse_exactly() {
    let (m, f) = fixture();
    for inst in [
        make(tuple(), None, &[]),
        make(tuple(), None, &[0, 1, 5]),
        make(Ty::Enum(EnumId::new(0)), None, &[0]),
        make(Ty::Enum(EnumId::new(0)), Some(u32::MAX), &[0]),
        make(Ty::Struct(StructId::new(99)), None, &[]),
        make(Ty::Enum(EnumId::new(99)), Some(0), &[]),
    ] {
        assert!(run(&m, &f, &inst, BlockId::new(17), true).0.is_err());
    }
}
#[test]
fn extract_struct_and_tuple_non_handle_lanes_still_require_exact_declared_type() {
    let (m, f) = fixture();
    for aggregate in [2, 3] {
        for (field, ty) in [(0, handle()), (1, Ty::Bool)] {
            assert_eq!(
                run(
                    &m,
                    &f,
                    &extract(ty, aggregate, field),
                    BlockId::new(17),
                    true
                )
                .0,
                Ok(())
            );
        }
        assert!(
            run(
                &m,
                &f,
                &extract(Ty::U64, aggregate, 0),
                BlockId::new(17),
                true
            )
            .0
            .is_err()
        );
        assert!(
            run(
                &m,
                &f,
                &extract(handle(), aggregate, u32::MAX),
                BlockId::new(17),
                true
            )
            .0
            .is_err()
        );
    }
    assert!(
        run(&m, &f, &extract(handle(), 99, 0), BlockId::new(17), true)
            .0
            .unwrap_err()
            .contains("unknown type")
    );
}
#[test]
fn enum_tag_exact_repr_and_payload_same_value_dominating_selected_variant_are_required() {
    let (m, f) = fixture();
    assert_eq!(
        run(&m, &f, &extract(Ty::U8, 4, 0), BlockId::new(17), true).0,
        Ok(())
    );
    assert!(
        run(&m, &f, &extract(Ty::U64, 4, 0), BlockId::new(17), true)
            .0
            .is_err()
    );
    assert_eq!(
        run(&m, &f, &extract(handle(), 4, 1), BlockId::new(17), true).0,
        Ok(())
    );
    assert_eq!(
        run(&m, &f, &extract(Ty::U64, 4, 1), BlockId::new(18), true).0,
        Ok(())
    );
    for (block, ty) in [
        (17, Ty::U64),
        (18, handle()),
        (33, handle()),
        (888, handle()),
    ] {
        assert!(
            run(&m, &f, &extract(ty, 4, 1), BlockId::new(block), true)
                .0
                .is_err()
        );
    }
    assert!(
        run(&m, &f, &extract(handle(), 4, 1), BlockId::new(17), false)
            .0
            .unwrap_err()
            .contains("no guard analysis")
    );
}
#[test]
fn enum_reads_of_every_payload_lane_require_guard_even_when_that_lane_is_ordinary() {
    let (mut m, f) = fixture();
    m.enums[0].variants[0].fields.push(Ty::Bool);
    m.enums[0].variants[1].fields.push(Ty::U64);
    assert_eq!(
        run(&m, &f, &extract(Ty::Bool, 4, 2), BlockId::new(17), true).0,
        Ok(())
    );
    assert!(
        run(&m, &f, &extract(Ty::Bool, 4, 2), BlockId::new(33), true)
            .0
            .is_err()
    );
    assert!(
        run(&m, &f, &extract(Ty::Bool, 4, 2), BlockId::new(17), false)
            .0
            .is_err()
    );
}
#[test]
fn malformed_discriminants_narrow_repr_and_empty_enum_refuse_before_guard_payload_use() {
    let (m, f) = fixture();
    let mut cases = vec![];
    let mut a = m.clone();
    a.enums[0].discriminants = vec![Some(0), Some(0)];
    cases.push(a);
    let mut a = m.clone();
    a.enums[0].discriminants = vec![Some(i128::MAX), None];
    cases.push(a);
    let mut a = m.clone();
    a.enums[0].discriminants = vec![Some(0), Some(256)];
    a.enums[0].repr = Some(trust_ir::ty::EnumTagRepr::U8);
    cases.push(a);
    let mut a = m.clone();
    a.enums[0].variants.clear();
    cases.push(a);
    for a in cases {
        assert!(
            run(&a, &f, &extract(handle(), 4, 1), BlockId::new(17), true)
                .0
                .unwrap_err()
                .contains("no canonical tag repr")
        );
    }
}
#[test]
fn insert_requires_exact_base_and_value_and_never_mutates_an_enum_lane() {
    let (m, f) = fixture();
    for (ty, aggregate) in [(tuple(), 2), (Ty::Struct(StructId::new(0)), 3)] {
        assert_eq!(
            run(
                &m,
                &f,
                &insert(ty.clone(), aggregate, 0, 0),
                BlockId::new(17),
                true
            )
            .0,
            Ok(())
        );
        assert!(
            run(
                &m,
                &f,
                &insert(ty.clone(), aggregate, 0, 1),
                BlockId::new(17),
                true
            )
            .0
            .is_err()
        );
        assert!(
            run(&m, &f, &insert(ty.clone(), 0, 0, 0), BlockId::new(17), true)
                .0
                .is_err()
        );
        assert!(
            run(
                &m,
                &f,
                &insert(ty, aggregate, u32::MAX, 0),
                BlockId::new(17),
                true
            )
            .0
            .is_err()
        );
    }
    for (ty, aggregate) in [(Ty::Enum(EnumId::new(0)), 2), (tuple(), 4)] {
        assert!(
            run(&m, &f, &insert(ty, aggregate, 0, 0), BlockId::new(17), true)
                .0
                .unwrap_err()
                .contains("cannot rewrite")
        );
    }
}
#[test]
fn every_other_aggregate_carrier_is_refused_and_wrong_operations_have_payload_free_original_names()
{
    let (m, f) = fixture();
    for ty in [
        Ty::Bool,
        Ty::Handle(Box::new(HandleTy::new("raw λ\0", "R"))),
        Ty::Ref(Box::new(handle())),
        Ty::Sequence(trust_ir::value::TyId::new(0)),
    ] {
        assert!(
            run(&m, &f, &make(ty, None, &[]), BlockId::new(17), true)
                .0
                .unwrap_err()
                .contains("not a handle carrier")
        );
    }
    for inst in [
        Inst::NullPtr,
        Inst::Const {
            ty: handle(),
            value: Constant::Bytes {
                data: vec![1; 100_000],
                utf8: true,
            },
        },
    ] {
        assert!(
            run(&m, &f, &inst, BlockId::new(17), true)
                .0
                .unwrap_err()
                .ends_with("is not an aggregate lane operation")
        );
    }
}
#[test]
fn declaration_fast_path_and_paid_first_off_index_fallback_keep_duplicates_and_unknown_ids() {
    let (mut m, f) = fixture();
    let first = m.structs[0].clone();
    let mut different = first.clone();
    different.fields[0].ty = Ty::U64;
    m.structs = vec![first.clone(), different.clone()];
    assert_eq!(
        run(
            &m,
            &f,
            &make(Ty::Struct(StructId::new(0)), None, &[0, 1]),
            BlockId::new(17),
            true
        )
        .0,
        Ok(())
    );
    m.structs[0].id = StructId::new(99);
    m.structs[1].id = StructId::new(77);
    let mut fallback = first;
    fallback.id = StructId::new(0);
    m.structs.push(fallback);
    assert_eq!(
        run(
            &m,
            &f,
            &make(Ty::Struct(StructId::new(0)), None, &[0, 1]),
            BlockId::new(17),
            true
        )
        .0,
        Ok(())
    );
    let mut e = m.enums[0].clone();
    e.id = EnumId::new(99);
    m.enums.insert(0, e);
    assert_eq!(
        run(&m, &f, &extract(handle(), 4, 1), BlockId::new(17), true).0,
        Ok(())
    );
    assert!(
        run(
            &m,
            &f,
            &make(Ty::Struct(StructId::new(u32::MAX)), None, &[]),
            BlockId::new(17),
            true
        )
        .0
        .is_err()
    );
}
#[test]
fn duplicate_value_rows_keep_last_definition_exact_identity() {
    let (m, mut f) = fixture();
    f.blocks[3].params.push((v(0), Ty::U64));
    assert!(
        run(
            &m,
            &f,
            &make(tuple(), None, &[0, 1]),
            BlockId::new(17),
            true
        )
        .0
        .is_err()
    );
}
#[test]
fn raw_diagnostic_names_and_deep_types_are_not_truncated_and_unrelated_field_names_stay_unread() {
    let (mut m, f) = fixture();
    m.structs[0].fields[0].name = "unread".repeat(10000);
    m.enums[0].variants[0].name = "unread".repeat(10000);
    let mut deep = handle();
    for _ in 0..128 {
        deep = Ty::Ref(Box::new(deep));
    }
    let inst = extract(deep, 2, 0);
    assert!(
        run(&m, &f, &inst, BlockId::new(17), true)
            .0
            .unwrap_err()
            .len()
            > 200
    );
}
#[test]
fn full_unsigned_decimal_keeps_native_maximum_and_u128_maximum_without_truncation() {
    for n in [0, u32::MAX as u128, usize::MAX as u128, u128::MAX] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut out = String::new();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        work.unsigned(n, &mut out).unwrap();
        assert_eq!(out, n.to_string());
        work.flat(out);
    }
}
