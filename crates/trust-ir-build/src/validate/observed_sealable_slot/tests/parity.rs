// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn direct_handle_nested_struct_and_tuple_carriers_match_actual_ordinary_predicate() {
    let m = fixture();
    for ty in [
        handle(),
        Ty::Struct(StructId::new(0)),
        Ty::Struct(StructId::new(1)),
        Ty::Tuple(vec![handle(), Ty::Struct(StructId::new(1)), Ty::Bool]),
    ] {
        assert!(run(&m, &ty).0);
    }
}
#[test]
fn all_other_root_shapes_refuse_without_opening_nested_handle_payloads() {
    let m = fixture();
    for ty in [
        Ty::Bool,
        Ty::Ref(Box::new(handle())),
        Ty::RefMut(Box::new(handle())),
        Ty::Array(TyId::new(0), 0),
        Ty::Sequence(TyId::new(0)),
        Ty::Enum(EnumId::new(0)),
        Ty::Vector(Box::new(handle()), 8),
    ] {
        assert!(!run(&m, &ty).0);
    }
}
#[test]
fn non_handle_lanes_are_skipped_even_when_their_root_shape_is_not_sealable() {
    let mut m = fixture();
    m.structs[0].fields.push(FieldDef {
        name: "opaque".into(),
        ty: Ty::Dialect(Box::new(trust_ir::DialectTy::new("ns", "opaque", 1))),
        offset: None,
    });
    assert!(run(&m, &Ty::Struct(StructId::new(0))).0);
    assert!(run(&m, &Ty::Tuple(vec![Ty::Bool, Ty::Ptr])).0);
    // This predicate alone does NOT validate a by-value module cycle. Such a
    // lane with no reachable handle is skipped, exactly like the ordinary rule.
    m.structs = vec![structure(0, vec![Ty::Struct(StructId::new(0))])];
    assert!(run(&m, &Ty::Struct(StructId::new(0))).0);
}
#[test]
fn handle_reaching_direct_mutual_and_tuple_mediated_struct_cycles_refuse() {
    let mut m = fixture();
    m.structs = vec![structure(0, vec![Ty::Struct(StructId::new(0)), handle()])];
    assert!(!run(&m, &Ty::Struct(StructId::new(0))).0);
    m.structs = vec![
        structure(0, vec![Ty::Struct(StructId::new(1)), handle()]),
        structure(1, vec![Ty::Tuple(vec![Ty::Struct(StructId::new(0))])]),
    ];
    assert!(!run(&m, &Ty::Struct(StructId::new(0))).0);
}
#[test]
fn active_path_guard_does_not_globally_deduplicate_sibling_definitions() {
    let m = fixture();
    assert!(
        run(
            &m,
            &Ty::Tuple(vec![
                Ty::Struct(StructId::new(1)),
                Ty::Struct(StructId::new(1))
            ])
        )
        .0
    );
}
#[test]
fn original_fast_id_filter_first_off_index_match_and_missing_definition_are_preserved() {
    let mut m = fixture();
    let valid = structure(0, vec![handle()]);
    let wrong = structure(0, vec![Ty::Ref(Box::new(handle()))]);
    m.structs = vec![valid.clone(), wrong.clone()];
    assert!(run(&m, &Ty::Struct(StructId::new(0))).0);
    m.structs = vec![structure(9, vec![]), valid, wrong];
    assert!(run(&m, &Ty::Struct(StructId::new(0))).0);
    assert!(!run(&m, &Ty::Struct(StructId::new(u32::MAX))).0);
}
#[test]
fn deep_heap_frames_and_wide_lanes_have_no_fixed_visit_or_depth_cap() {
    let m = fixture();
    let mut ty = handle();
    for _ in 0..256 {
        ty = Ty::Tuple(vec![ty]);
    }
    assert!(run(&m, &ty).0);
    assert!(run(&m, &Ty::Tuple(vec![handle(); 512])).0);
}
#[test]
fn raw_handle_names_and_unrelated_layout_or_field_metadata_remain_unread() {
    let m = fixture();
    let (_, a, ab, ae) = run(&m, &handle());
    let (_, b, bb, be) = run(&m, &Ty::handle("x".repeat(100_000), "y".repeat(100_000)));
    assert_eq!(&a.events[ab..ae], &b.events[bb..be]);
    let mut n = m.clone();
    n.structs[0].name = "x".repeat(100000);
    n.structs[0].fields[0].name = "x".repeat(100000);
    n.structs[0].fields[0].offset = Some(u64::MAX);
    n.structs[0].size = Some(u64::MAX);
    let (_, a, ab, ae) = run(&m, &Ty::Struct(StructId::new(0)));
    let (_, b, bb, be) = run(&n, &Ty::Struct(StructId::new(0)));
    assert_eq!(&a.events[ab..ae], &b.events[bb..be]);
}
