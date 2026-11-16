// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn uninhabited_direct_live_pair_and_full_reserved_storage_match() {
    let ty = Ty::Enum(EnumId::new(0));
    for (live, size, align) in [(Ty::U32, 4, 4), (Ty::U128, 16, 16)] {
        let m = direct_storage_fixture(live, size, align);
        assert_eq!(run(&m, &ty).0, Some(2));
    }
    let mut narrow = direct_storage_fixture(Ty::U64, 8, 8);
    let target = narrow.target_info.as_mut().unwrap();
    target.triple = "wasm32-unknown-unknown".into();
    target.pointer_size = 4;
    assert_eq!(
        run(&narrow, &ty).0,
        Some(2),
        "not a fixed two-pointer-word ceiling"
    );
    narrow.target_info.as_mut().unwrap().triple = "i686-unknown-linux-gnu".into();
    assert_eq!(
        run(&narrow, &ty).0,
        None,
        "missing scalar-layout authority still refuses"
    );

    for change in 0..6 {
        let mut m = direct_storage_fixture(Ty::U32, 4, 4);
        match change {
            0 => m.enums[0].variants[0].fields = vec![Ty::U8],
            1 => m.enums[0].variants[0].fields = vec![Ty::Tuple(vec![Ty::Never, s(999)])],
            _ => {
                let desc = m.enums[0].layout.as_mut().unwrap();
                let EnumTagEncoding::DirectWithUninhabited { variants, .. } = &mut desc.encoding
                else {
                    unreachable!()
                };
                match change {
                    2 => variants.clear(),
                    3 => {
                        desc.size = 65552;
                        desc.align = 16;
                        variants[0].size = 65552;
                        variants[0].align = 16;
                    }
                    4 => {
                        desc.size = 16;
                        variants[0].size = 16;
                        desc.variant_field_offsets[1][0] = 12;
                    }
                    5 => {
                        desc.size = 16;
                        desc.align = 16;
                        variants[0].size = 16;
                        variants[0].align = 16;
                    }
                    _ => unreachable!(),
                }
            }
        }
        if change >= 3 {
            assert!(m.layout_table().enum_layout(EnumId::new(0)).is_ok());
        }
        assert_eq!(run(&m, &ty).0, None, "case {change}");
    }
}

#[test]
fn uninhabited_direct_ignores_zero_extent_ranges_but_keeps_their_alignment() {
    let mut m = direct_storage_fixture(Ty::U32, 4, 4);
    let mut zst = strukt(0, vec![]);
    zst.size = Some(0);
    zst.align = Some(16);
    zst.repr = StructRepr::Rust;
    m.structs.push(zst);
    m.enums[0].variants[1].fields.push(s(0));
    let desc = m.enums[0].layout.as_mut().unwrap();
    desc.size = 16;
    desc.align = 16;
    desc.variant_field_offsets[1].push(16);
    let EnumTagEncoding::DirectWithUninhabited { variants, .. } = &mut desc.encoding else {
        unreachable!()
    };
    variants[0].size = 16;
    variants[0].align = 16;
    assert!(m.layout_table().enum_layout(EnumId::new(0)).is_ok());
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(0))).0, Some(2));
}

#[test]
fn uninhabited_direct_nested_dead_source_keeps_memory_passing() {
    let mut m = direct_storage_fixture(Ty::U32, 4, 4);
    m.types.push(Ty::U128);
    m.enums
        .push(EnumDef::new(EnumId::new(9), "Infallible", vec![]));
    m.enums[0].variants[0].fields = vec![Ty::Tuple(vec![
        Ty::Enum(EnumId::new(9)),
        Ty::Array(TyId::new(0), 4096),
    ])];
    let desc = m.enums[0].layout.as_mut().unwrap();
    desc.size = 65552;
    desc.align = 16;
    desc.variant_field_offsets[0][0] = 16;
    let EnumTagEncoding::DirectWithUninhabited { variants, .. } = &mut desc.encoding else {
        unreachable!()
    };
    variants[0].size = 65552;
    variants[0].align = 16;
    variants[0].fields[0] = trust_ir::ty::FieldStorageLayout {
        size: 65536,
        align: 16,
    };
    assert!(m.layout_table().enum_layout(EnumId::new(0)).is_ok());
    assert!(
        m.layout_table()
            .ty_layout(&Ty::Enum(EnumId::new(9)))
            .is_err()
    );
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(0))).0, None);
}

#[test]
fn uninhabited_direct_all_dead_physical_image_has_no_abi_value() {
    let mut m = direct_storage_fixture(Ty::U32, 4, 4);
    m.enums[0].variants[1].fields = vec![Ty::Never];
    let desc = m.enums[0].layout.as_mut().unwrap();
    let EnumTagEncoding::DirectWithUninhabited { variants, .. } = &mut desc.encoding else {
        unreachable!()
    };
    let mut second = variants[0].clone();
    second.variant = 1;
    variants.push(second);
    assert!(m.layout_table().enum_layout(EnumId::new(0)).is_ok());
    assert_eq!(
        run(&m, &Ty::Enum(EnumId::new(0))).0,
        None,
        "a valid physical tag image does not create an inhabited source value"
    );
    m.enums
        .push(EnumDef::new(EnumId::new(9), "Infallible", vec![]));
    assert!(
        m.layout_table()
            .ty_layout(&Ty::Enum(EnumId::new(9)))
            .is_err()
    );
}

#[test]
fn every_closed_scalar_unit_and_thin_or_fat_pointer_family_matches_original_raw_count() {
    let m = module();
    for ty in [
        Ty::Bool,
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Char,
        Ty::Ptr,
        Ty::Unit,
        Ty::Ref(Box::new(Ty::Never)),
        Ty::RefMut(Box::new(Ty::Never)),
        Ty::PtrConst(Box::new(Ty::Never)),
        Ty::PtrMut(Box::new(Ty::Never)),
        Ty::Rc(Box::new(Ty::Never)),
        Ty::FatPtr(FatPtrKind::Str),
    ] {
        run(&m, &ty);
    }
    assert_eq!(run(&m, &Ty::Unit).0, Some(0));
    assert_eq!(run(&m, &Ty::FatPtr(FatPtrKind::Str)).0, Some(2));
}
#[test]
fn arrays_vectors_refinements_nominals_without_rules_and_functions_are_not_broadened() {
    let m = module();
    for ty in [
        Ty::Never,
        Ty::Array(TyId::new(0), 1),
        Ty::Vector(Box::new(Ty::U8), 2),
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Closure(ClosureTyId::new(0)),
        Ty::Sequence(TyId::new(0)),
        Ty::Func(FuncTyId::new(0)),
        Ty::handle("H", "rt::H"),
        Ty::Dialect(Box::new(trust_ir::DialectTy::new("ns", "D", 1))),
        Ty::Error,
    ] {
        assert_eq!(run(&m, &ty).0, None);
    }
}
#[test]
fn nested_tuple_and_struct_sums_ignore_zero_lanes_and_preserve_exact_counts() {
    let mut m = module();
    m.structs
        .push(strukt(0, vec![Ty::U64, Ty::Tuple(vec![Ty::Unit, Ty::Ptr])]));
    assert_eq!(run(&m, &s(0)).0, Some(2));
    assert_eq!(run(&m, &Ty::Tuple(vec![s(0), Ty::U8])).0, Some(3));
    assert_eq!(run(&m, &Ty::Tuple(vec![])).0, Some(0));
}
#[test]
fn actual_first_physical_definition_wins_over_a_later_matching_index_or_duplicate() {
    let mut m = module();
    m.structs.push(strukt(7, vec![Ty::U64, Ty::Ptr]));
    for i in 1..7 {
        m.structs.push(strukt(i, vec![]));
    }
    m.structs.push(strukt(7, vec![Ty::U8]));
    assert_eq!(run(&m, &s(7)).0, Some(2));
    m.enums.push(enum_def(7, vec![vec![Ty::U8]], None));
    for i in 1..7 {
        m.enums.push(enum_def(i, vec![], None));
    }
    m.enums.push(enum_def(7, vec![vec![]], None));
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(7))).0, Some(2));
}
#[test]
fn direct_enums_add_one_tag_to_at_most_one_payload_lane_but_empty_has_no_abi() {
    let mut m = module();
    for (id, variants) in [
        (0, vec![vec![], vec![Ty::U64]]),
        (1, vec![vec![Ty::U64, Ty::Ptr]]),
        (2, vec![]),
    ] {
        m.enums.push(enum_def(id, variants, None));
    }
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(0))).0, Some(2));
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(1))).0, None);
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(2))).0, None);
}

#[test]
fn single_inhabited_abi_uses_selected_payload_and_refuses_inactive_or_unknown_proof() {
    for selected in [0, 1] {
        let mut m = module();
        m.enums.push(enum_def(0, vec![], None));
        let empty = Ty::Enum(EnumId::new(0));
        let fields = if selected == 0 {
            vec![vec![Ty::U64, Ty::Ptr], vec![empty.clone()]]
        } else {
            vec![vec![empty.clone()], vec![Ty::U64, Ty::Ptr]]
        };
        m.enums.push(enum_def(
            1,
            fields,
            Some(EnumTagEncoding::SingleInhabited { variant: selected }),
        ));
        let ty = Ty::Enum(EnumId::new(1));
        assert_eq!(run(&m, &ty).0, Some(2));
        let (_, _, begin, end) = run(&m, &ty);
        assert!(end > begin);
        for invalid in [2, 1 - selected] {
            let mut bad = m.clone();
            bad.enums[1].layout.as_mut().unwrap().encoding =
                EnumTagEncoding::SingleInhabited { variant: invalid };
            assert_eq!(run(&bad, &ty).0, None);
        }
        m.enums[1].variants[(1 - selected) as usize].fields = vec![Ty::Enum(EnumId::new(999))];
        assert_eq!(run(&m, &ty).0, None);
    }
}
#[test]
fn untagged_enums_require_exactly_one_variant_then_keep_its_whole_sum() {
    let mut m = module();
    for (id, variants) in [
        (0, vec![]),
        (1, vec![vec![Ty::U64, Ty::Ptr]]),
        (2, vec![vec![], vec![]]),
    ] {
        m.enums
            .push(enum_def(id, variants, Some(EnumTagEncoding::Untagged)));
    }
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(0))).0, None);
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(1))).0, Some(2));
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(2))).0, None);
}
#[test]
fn niche_enums_visit_all_other_variants_before_dataful_and_refuse_nonzero_others() {
    let mut m = module();
    m.enums.push(enum_def(
        0,
        vec![vec![], vec![Ty::U64, Ty::Ptr], vec![Ty::Unit]],
        Some(niche(1)),
    ));
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(0))).0, Some(2));
    m.enums[0].variants[2].fields = vec![Ty::U8];
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(0))).0, None);
}
#[test]
fn invalid_niche_dataful_index_waits_for_others_then_remains_semantic_none() {
    let mut m = module();
    m.enums
        .push(enum_def(0, vec![vec![], vec![Ty::Unit]], Some(niche(99))));
    assert_eq!(run(&m, &Ty::Enum(EnumId::new(0))).0, None);
}
#[test]
fn self_and_mutual_struct_enum_cycles_have_no_finite_count_without_recursion() {
    let mut m = module();
    m.structs.push(strukt(0, vec![s(1), Ty::U64]));
    m.structs.push(strukt(1, vec![Ty::Enum(EnumId::new(0))]));
    m.enums.push(enum_def(
        0,
        vec![vec![s(0)]],
        Some(EnumTagEncoding::Untagged),
    ));
    for ty in [s(0), s(1), Ty::Enum(EnumId::new(0)), s(99)] {
        assert_eq!(run(&m, &ty).0, None);
    }
}
#[test]
fn shared_doubling_graph_preserves_checked_usize_overflow_and_cached_counts() {
    let m = doubling(usize::BITS + 2);
    for depth in [0, 1, 12, usize::BITS - 1, usize::BITS, usize::BITS + 1] {
        let got = run(&m, &s(depth)).0;
        assert_eq!(
            got,
            if depth < usize::BITS {
                Some(1usize << depth)
            } else {
                None
            }
        );
    }
}
#[test]
fn many_empty_enum_variants_run_on_one_fixed_host_call_stack() {
    // The ordinary raw rule gives one tag plus zero payload; do not recurse
    // through its mutually recursive empty-variant helper on this wide input.
    let mut m = module();
    m.enums.push(enum_def(0, vec![vec![]; 8192], None));
    let mut o = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, mut lanes) = setup(&m, &mut session);
    assert_eq!(
        lanes
            .lanes_observed(&table, &Ty::Enum(EnumId::new(0)), &mut session, site())
            .unwrap(),
        Some(1)
    );
    dispose(table, lanes, &mut session);
}
#[test]
fn actual_bounded_mixed_cyclic_graphs_match_complete_original_solver_for_every_root() {
    for seed in 0..16 {
        let m = random_graph(seed);
        for id in 0..8 {
            run(&m, &s(id));
            run(&m, &Ty::Enum(EnumId::new(id)));
        }
    }
}
