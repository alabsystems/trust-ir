// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn direct_dead_storage_native_profiles_bind_exact_field_extents_and_rows() {
    let module = crate::layout_table::direct_storage::tests::fixture();
    let fact = crate::layout_table::direct_storage::tests::native_fact(&module);
    assert!(ordinary_adt(&module, &fact).is_empty());
    assert_eq!(adt(&module, &fact), ordinary_adt(&module, &fact));
    for change in 0..7 {
        let mut changed = fact.clone();
        let layout = changed.enum_layout.as_mut().unwrap();
        match change {
            0 => layout.tag_encoding = NativeEnumTagEncoding::Direct,
            1 => {
                let NativeEnumTagEncoding::DirectWithUninhabited { variants } =
                    &mut layout.tag_encoding
                else {
                    unreachable!()
                };
                variants[0].fields[0].size -= 16;
            }
            2 => layout.variants[0].size_bits -= 128,
            3 => layout.variants[0].align_bits = None,
            4 => layout.variants[0].fields[0].offset_bits = Some(0),
            5 => layout.tag_bits = Some(8),
            6 => layout.discriminant_offset_bits = Some(8),
            _ => unreachable!(),
        }
        let expected = ordinary_adt(&module, &changed);
        assert!(!expected.is_empty(), "case {change}");
        assert_eq!(adt(&module, &changed), expected, "case {change}");
    }
    let mut invalid_source = module.clone();
    let crate::EnumTagEncoding::DirectWithUninhabited { variants, .. } =
        &mut invalid_source.enums[0].layout.as_mut().unwrap().encoding
    else {
        unreachable!()
    };
    variants[0].fields[0].align = 3;
    let fact = crate::layout_table::direct_storage::tests::native_fact(&invalid_source);
    assert!(
        !ordinary_adt(&invalid_source, &fact).is_empty(),
        "matching claims cannot establish source layout"
    );
    assert_eq!(
        adt(&invalid_source, &fact),
        ordinary_adt(&invalid_source, &fact)
    );
}

#[test]
fn struct_actual_layout_names_offsets_shapes_and_size_match_original_helper() {
    let module = module();
    let base = structure(&module);
    assert!(adt(&module, &base).is_empty());
    for change in 0..7 {
        let mut fact = base.clone();
        match change {
            0 => fact.layout.size_bits += 8,
            1 => fact.layout.align_bits = None,
            _ => {
                if let TyLayoutKind::Struct { fields, .. } = &mut fact.layout.kind {
                    match change {
                        2 => {
                            let end = fields[0].name.len();
                            fields[0].name.replace_range(end - 2.., "μ");
                        }
                        3 => fields[0].offset_bits = Some(8),
                        4 => fields[0].ty_shape = TyShape::Bool,
                        5 => fields[0].field = 1,
                        _ => {
                            fields.pop();
                        }
                    }
                }
            }
        }
        assert_eq!(adt(&module, &fact), ordinary_adt(&module, &fact));
    }
}

#[test]
fn missing_struct_kind_mismatch_and_non_adt_guards_keep_original_order() {
    let module = module();
    for change in 0..4 {
        let mut fact = structure(&module);
        match change {
            0 => {
                fact.ty = Ty::Struct(StructId::new(99));
                if let TyLayoutKind::Struct { id, .. } = &mut fact.layout.kind {
                    *id = StructId::new(99);
                }
            }
            1 => fact.layout.kind = TyLayoutKind::Unit,
            2 => fact.ty = Ty::U32,
            _ => fact.enum_layout = enumeration(&module).enum_layout,
        }
        assert_eq!(adt(&module, &fact), ordinary_adt(&module, &fact));
    }
}

#[test]
fn original_first_definition_and_semantic_layout_error_behavior_is_preserved() {
    let base = module();
    let fact = structure(&base);
    for change in 0..6 {
        let mut module = base.clone();
        match change {
            0 => module.structs[0].size = None,
            1 => module.structs[0].align = Some(0),
            2 => module.structs[0].fields[0].offset = None,
            3 => module.target_info.as_mut().unwrap().triple = "i686-unknown-linux-gnu".into(),
            4 => {
                let mut duplicate = module.structs[0].clone();
                duplicate.size = None;
                module.structs.push(duplicate);
            }
            _ => module.structs[0].fields[0].ty = Ty::Struct(StructId::new(9)),
        }
        assert_eq!(adt(&module, &fact), ordinary_adt(&module, &fact));
    }
}

#[test]
fn enum_variant_index_name_field_and_alignment_tampering_match_both_helpers() {
    let module = module();
    let base = enumeration(&module);
    for change in 0..11 {
        let mut fact = base.clone();
        let layout = fact.enum_layout.as_mut().unwrap();
        match change {
            0 => layout.variants[1].variant_index = 0,
            1 => layout.variants[0].variant_index = 99,
            2 => layout.variants[0].name.push('!'),
            3 => {
                layout.variants[0].fields.pop();
            }
            4 => layout.variants[0].fields[0].field = 1,
            5 => layout.variants[0].fields[0].ty_shape = TyShape::Bool,
            6 => layout.variants[0].size_bits = 999,
            7 => layout.variants[0].align_bits = Some(0),
            8 => layout.variants[0].align_bits = Some(64),
            9 => fact.layout.align_bits = Some(48),
            _ => layout.variants.push(layout.variants[0].clone()),
        }
        assert_eq!(adt(&module, &fact), ordinary_adt(&module, &fact));
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            fact.enum_layout
                .as_ref()
                .unwrap()
                .validation_errors_observed(&fact, &module.enums[0], &mut session, site())
                .unwrap(),
            ordinary_enum(&module, &fact)
        );
    }
}

#[test]
fn enum_outer_missing_id_missing_rows_and_variant_count_guards_match() {
    let module = module();
    for change in 0..6 {
        let mut fact = enumeration(&module);
        match change {
            0 => {
                fact.ty = Ty::Enum(EnumId::new(99));
                fact.layout.kind = TyLayoutKind::Enum {
                    id: EnumId::new(99),
                    variants: 2,
                };
            }
            1 => fact.enum_layout = None,
            2 => fact.enum_layout.as_mut().unwrap().enum_id = EnumId::new(99),
            3 => {
                fact.layout.kind = TyLayoutKind::Enum {
                    id: EnumId::new(7),
                    variants: 1,
                }
            }
            4 => {
                fact.enum_layout.as_mut().unwrap().variants.pop();
            }
            _ => fact.layout.kind = TyLayoutKind::Unit,
        }
        assert_eq!(adt(&module, &fact), ordinary_adt(&module, &fact));
    }
}

#[test]
fn direct_tag_zero_early_return_overflow_and_duplicate_discriminants_match() {
    let module = module();
    for change in 0..7 {
        let mut fact = enumeration(&module);
        let layout = fact.enum_layout.as_mut().unwrap();
        match change {
            0 => {
                layout.tag_bits = Some(0);
                layout.variants[0].discriminant = None;
            }
            1 => layout.tag_bits = None,
            2 => layout.discriminant_offset_bits = None,
            3 => layout.discriminant_offset_bits = Some(u64::MAX),
            4 => layout.variants[1].discriminant = Some(0),
            5 => layout.variants[0].discriminant = None,
            _ => {
                layout.niche = Some(NativeEnumNicheFact {
                    variant_index: 0,
                    field: None,
                    valid_range: NativeIntegerRange { start: 0, end: 1 },
                })
            }
        }
        assert_eq!(adt(&module, &fact), ordinary_adt(&module, &fact));
    }
}

#[test]
fn niche_and_untagged_guard_order_and_early_returns_match() {
    let module = module();
    for strategy in [
        NativeEnumTagEncoding::Niche,
        NativeEnumTagEncoding::Untagged,
    ] {
        for change in 0..6 {
            let mut fact = enumeration(&module);
            let layout = fact.enum_layout.as_mut().unwrap();
            layout.tag_encoding = strategy.clone();
            layout.niche = Some(NativeEnumNicheFact {
                variant_index: 0,
                field: Some(0),
                valid_range: NativeIntegerRange { start: 0, end: 1 },
            });
            match change {
                0 => layout.niche = None,
                1 => layout.niche.as_mut().unwrap().valid_range.start = 2,
                2 => {
                    let niche = layout.niche.as_mut().unwrap();
                    niche.variant_index = 99;
                    niche.field = Some(99);
                }
                3 => layout.niche.as_mut().unwrap().field = Some(99),
                4 => {
                    layout.tag_bits = None;
                    layout.discriminant_offset_bits = None;
                }
                _ => {
                    for variant in &mut layout.variants {
                        variant.discriminant = None;
                    }
                }
            }
            assert_eq!(adt(&module, &fact), ordinary_adt(&module, &fact));
        }
    }
}

#[test]
fn enum_helper_does_not_add_derived_layout_or_ignored_field_payload_checks() {
    let mut module = module();
    let mut fact = enumeration(&module);
    module.enums[0].discriminants = vec![Some(0), Some(0)];
    fact.enum_layout.as_mut().unwrap().variants[0].fields[0].name = "ignored\0name".repeat(2000);
    fact.enum_layout.as_mut().unwrap().variants[0].fields[0].offset_bits = Some(u64::MAX);
    assert!(ordinary_adt(&module, &fact).is_empty());
    assert!(adt(&module, &fact).is_empty());
}

#[test]
fn every_fat_pointer_metadata_identity_thin_and_nonpointer_case_matches() {
    let module = module();
    for ty in [
        Ty::FatPtr(FatPtrKind::Str),
        Ty::FatPtr(FatPtrKind::Slice(TyId::new(8))),
        Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 7 }),
        Ty::FatPtr(FatPtrKind::ContainerLen),
        Ty::FatPtr(FatPtrKind::ContainerVtable),
        Ty::Ptr,
        Ty::Ref(Box::new(Ty::Tuple(vec![Ty::U32]))),
        Ty::U32,
    ] {
        for change in 0..3 {
            let mut fact = fat();
            fact.ty = ty.clone();
            fact.layout = fact.ty.pointer_layout_shape(64).unwrap_or(fact.layout);
            if change == 1 {
                fact.layout.data_bits = 32;
            }
            if change == 2 {
                fact.layout.metadata = Some(PointerMetadataShape::StrLen);
            }
            let mut observer = Observer::default();
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                fact.validation_errors_observed(&module, &mut session, site())
                    .unwrap(),
                ordinary_fat(&module, &fact)
            );
        }
    }
}

#[test]
fn pointer_width_zero_and_checked_overflow_fallback_preserve_original_helper() {
    for width in [0, 4, 8, u32::MAX] {
        let mut module = module();
        module.target_info.as_mut().unwrap().pointer_size = width;
        let mut fact = fat();
        fact.layout = fact.ty.pointer_layout_shape(module.pointer_bits()).unwrap();
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            fact.validation_errors_observed(&module, &mut session, site())
                .unwrap(),
            ordinary_fat(&module, &fact)
        );
    }
}

// Standalone enum metadata and authoritative ADT storage have different scopes.
fn empty_native_fixture() -> (Module, NativeAdtLayoutFact) {
    let mut module = module();
    let mut fact = enumeration(&module);
    module.enums[0].variants.clear();
    fact.layout.kind = TyLayoutKind::Enum {
        id: EnumId::new(7),
        variants: 0,
    };
    let layout = fact.enum_layout.as_mut().unwrap();
    layout.tag_encoding = NativeEnumTagEncoding::Untagged;
    layout.tag_bits = None;
    layout.discriminant_offset_bits = None;
    layout.variants.clear();
    (module, fact)
}
fn assert_empty_storage_refused(size_bits: u64, include_enum_metadata: bool) {
    let (module, mut fact) = empty_native_fixture();
    assert!(module.ty_is_uninhabited(&fact.ty));
    assert!(module.ty_layout_shape(&fact.ty).is_err());
    fact.layout.size_bits = size_bits;
    if !include_enum_metadata {
        fact.enum_layout = None;
    }
    let expected = vec![E::InvalidCompilerFact {
        fact: NativeCompilerFactRef::AdtLayout(fact.id),
        field: "layout",
    }];
    assert_eq!(ordinary_adt(&module, &fact), expected);
    assert_eq!(adt(&module, &fact), expected);
    if include_enum_metadata {
        assert!(ordinary_enum(&module, &fact).is_empty());
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(
            fact.enum_layout
                .as_ref()
                .unwrap()
                .validation_errors_observed(&fact, &module.enums[0], &mut session, site(),)
                .unwrap()
                .is_empty()
        );
    }
}
#[test]
fn empty_storage_zero_is_refused_but_shape_helper_stays_shape_only() {
    assert_empty_storage_refused(0, true);
}
#[test]
fn empty_storage_nonzero_is_refused_but_shape_helper_stays_shape_only() {
    assert_empty_storage_refused(8, true);
}
#[test]
fn empty_storage_max_is_refused_but_shape_helper_stays_shape_only() {
    assert_empty_storage_refused(u64::MAX, true);
}
#[test]
fn empty_storage_missing_rows_cannot_bypass_full_adt() {
    assert_empty_storage_refused(0, false);
}

fn bound_single_native_fixture() -> (Module, NativeAdtLayoutFact) {
    let mut module = module();
    module.types.push(Ty::U128);
    module.enums[0].variants[0].fields = vec![Ty::Never, Ty::Array(TyId::new(0), u64::MAX)];
    module.enums[0].variants[1].fields = vec![Ty::U32];
    module.enums[0].layout = Some(crate::EnumLayoutDescriptor {
        encoding: crate::EnumTagEncoding::SingleInhabited { variant: 1 },
        size: 4,
        align: 4,
        variant_field_offsets: vec![vec![], vec![0]],
    });
    let mut fact = enumeration(&module);
    fact.layout.size_bits = 32;
    fact.layout.align_bits = Some(32);
    let layout = fact.enum_layout.as_mut().unwrap();
    layout.tag_encoding = NativeEnumTagEncoding::Untagged;
    layout.tag_bits = None;
    layout.discriminant_offset_bits = None;
    layout.variants[0].fields.clear();
    layout.variants[0].size_bits = 0;
    layout.variants[0].align_bits = None;
    layout.variants[0].discriminant = None;
    layout.variants[1].fields = vec![FieldOffsetShape {
        field: 0,
        name: "value".into(),
        ty_shape: Ty::U32.shape(),
        offset_bits: Some(0),
    }];
    layout.variants[1].size_bits = 32;
    layout.variants[1].align_bits = Some(32);
    layout.variants[1].discriminant = None;
    (module, fact)
}
fn assert_bound_single_field(module: &Module, fact: &NativeAdtLayoutFact, field: &'static str) {
    let ordinary = ordinary_adt(module, fact);
    let observed = adt(module, fact);
    assert_eq!(ordinary, observed);
    let wanted = E::InvalidCompilerFact {
        fact: NativeCompilerFactRef::AdtLayout(fact.id),
        field,
    };
    assert!(
        ordinary.contains(&wanted),
        "missing exact {wanted:?}, got {ordinary:?}"
    );
}
#[test]
fn single_native_empty_dead_rows_bind_valid_logical_storage() {
    let (module, fact) = bound_single_native_fixture();
    assert!(ordinary_adt(&module, &fact).is_empty());
    assert!(adt(&module, &fact).is_empty());
}
#[test]
fn single_native_inactive_nonzero_size_is_refused() {
    let (module, mut fact) = bound_single_native_fixture();
    fact.enum_layout.as_mut().unwrap().variants[0].size_bits = 8;
    assert_bound_single_field(&module, &fact, "layout.size_bits");
}
#[test]
fn single_native_inactive_physical_fields_are_refused() {
    let (module, mut fact) = bound_single_native_fixture();
    fact.enum_layout.as_mut().unwrap().variants[0].fields = vec![
        FieldOffsetShape {
            field: 0,
            name: "never".into(),
            ty_shape: Ty::Never.shape(),
            offset_bits: Some(0),
        },
        FieldOffsetShape {
            field: 1,
            name: "dead".into(),
            ty_shape: module.enums[0].variants[0].fields[1].shape(),
            offset_bits: Some(0),
        },
    ];
    assert_bound_single_field(&module, &fact, "enum_layout.variant.fields");
}
#[test]
fn single_native_outer_geometry_is_bound_to_logical_layout() {
    let (module, mut fact) = bound_single_native_fixture();
    fact.layout.size_bits = 64;
    assert_bound_single_field(&module, &fact, "layout");
}
#[test]
fn single_native_empty_row_cannot_supply_source_deadness() {
    let (mut module, fact) = bound_single_native_fixture();
    module.enums[0].variants[0].fields = vec![Ty::U64];
    assert_bound_single_field(&module, &fact, "layout");
}
#[test]
fn single_native_requires_untagged_protocol() {
    let (module, mut fact) = bound_single_native_fixture();
    let layout = fact.enum_layout.as_mut().unwrap();
    layout.tag_encoding = NativeEnumTagEncoding::Direct;
    layout.tag_bits = Some(8);
    layout.discriminant_offset_bits = Some(0);
    for (index, variant) in layout.variants.iter_mut().enumerate() {
        variant.discriminant = Some(index as i128);
    }
    assert_bound_single_field(&module, &fact, "enum_layout.tag_encoding");
}
