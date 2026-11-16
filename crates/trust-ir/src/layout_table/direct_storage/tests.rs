// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::ty::{FieldStorageLayout, UninhabitedVariantLayout};

pub(crate) fn fixture() -> Module {
    let mut module = Module::new("Direct source/storage separation");
    module.types.push(Ty::U128);
    module.add_enum(EnumDef::new(EnumId::new(9), "Infallible", vec![]));
    let mut definition = EnumDef::new(
        EnumId::new(7),
        "Nested",
        vec![
            EnumVariant {
                name: "Dead".into(),
                fields: vec![Ty::Tuple(vec![
                    Ty::Enum(EnumId::new(9)),
                    Ty::Array(TyId::new(0), 4096),
                ])],
                field_names: vec![],
            },
            EnumVariant {
                name: "Live".into(),
                fields: vec![Ty::U32],
                field_names: vec![],
            },
        ],
    )
    .with_discriminants(vec![Some(-7), Some(37)])
    .with_repr(EnumTagRepr::I32);
    definition.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::DirectWithUninhabited {
            tag_offset: 0,
            variants: vec![UninhabitedVariantLayout {
                variant: 0,
                size: 65552,
                align: 16,
                fields: vec![FieldStorageLayout {
                    size: 65536,
                    align: 16,
                }],
            }],
        },
        size: 65552,
        align: 16,
        variant_field_offsets: vec![vec![16], vec![4]],
    });
    module.enums.insert(0, definition);
    module
}

pub(crate) fn native_fact(module: &Module) -> crate::request::NativeAdtLayoutFact {
    use crate::request::{
        NativeAdtLayoutFact, NativeCompilerFactId, NativeEnumLayoutFact, NativeEnumTagEncoding,
        NativeEnumVariantLayoutFact,
    };
    let definition = &module.enums[0];
    let desc = definition.layout.as_ref().unwrap();
    let EnumTagEncoding::DirectWithUninhabited {
        tag_offset,
        variants,
    } = &desc.encoding
    else {
        unreachable!()
    };
    NativeAdtLayoutFact {
        id: NativeCompilerFactId::new(20),
        ty: Ty::Enum(definition.id),
        layout: TyLayoutShape {
            size_bits: desc.size * 8,
            align_bits: Some(desc.align * 8),
            kind: TyLayoutKind::Enum {
                id: definition.id,
                variants: definition.variants.len(),
            },
        },
        enum_layout: Some(NativeEnumLayoutFact {
            enum_id: definition.id,
            tag_encoding: NativeEnumTagEncoding::DirectWithUninhabited {
                variants: variants.clone(),
            },
            tag_bits: Some(32),
            discriminant_offset_bits: Some(tag_offset * 8),
            niche: None,
            variants: definition
                .variants
                .iter()
                .enumerate()
                .map(|(index, row)| NativeEnumVariantLayoutFact {
                    variant_index: index as u32,
                    name: row.name.clone(),
                    discriminant: Some(if index == 0 { -7 } else { 37 }),
                    fields: row
                        .fields
                        .iter()
                        .enumerate()
                        .map(|(field, ty)| FieldOffsetShape {
                            field: field as u32,
                            name: field.to_string(),
                            ty_shape: ty.shape(),
                            offset_bits: Some(desc.variant_field_offsets[index][field] * 8),
                        })
                        .collect(),
                    size_bits: if index == 0 { 65552 * 8 } else { 8 * 8 },
                    align_bits: Some(if index == 0 { 16 * 8 } else { 4 * 8 }),
                })
                .collect(),
        }),
    }
}

#[test]
fn direct_profile_preserves_large_physical_image_and_nominal_dead_source() {
    let module = fixture();
    let table = LayoutTable::new(&module);
    let shape = table.enum_layout(EnumId::new(7)).unwrap();
    assert_eq!((shape.size_bits, shape.align_bits), (65552 * 8, 16 * 8));
    assert_eq!(shape.payload_size_bits, 65536 * 8);
    assert_eq!(shape.payload_offset_bits, 16 * 8);
    assert!(table.variant_is_uninhabited(&module.enums[0].variants[0]));
    assert!(!table.variant_is_uninhabited(&module.enums[0].variants[1]));
    assert!(table.ty_layout(&Ty::Enum(EnumId::new(9))).is_err());
    assert_eq!(
        module.enums[0].variants[0].fields,
        vec![Ty::Tuple(vec![
            Ty::Enum(EnumId::new(9)),
            Ty::Array(TyId::new(0), 4096),
        ])]
    );
}

pub(crate) fn invalid_cases() -> Vec<Module> {
    let mut cases = Vec::new();
    for change in 0..18 {
        let mut module = fixture();
        let definition = &mut module.enums[0];
        let desc = definition.layout.as_mut().unwrap();
        let EnumTagEncoding::DirectWithUninhabited {
            tag_offset,
            variants,
        } = &mut desc.encoding
        else {
            unreachable!()
        };
        match change {
            0 => variants.clear(),
            1 => variants.push(variants[0].clone()),
            2 => variants[0].variant = 1,
            3 => variants[0].variant = u32::MAX,
            4 => variants[0].fields.clear(),
            5 => desc.variant_field_offsets[0].clear(),
            6 => variants[0].align = 3,
            7 => variants[0].size -= 1,
            8 => variants[0].size += 16,
            9 => variants[0].fields[0].align = 0,
            10 => variants[0].fields[0].align = 32,
            11 => variants[0].fields[0] = FieldStorageLayout { size: 3, align: 2 },
            12 => desc.variant_field_offsets[0][0] = 17,
            13 => desc.variant_field_offsets[0][0] = 32,
            14 => {
                variants[0].fields[0] = FieldStorageLayout { size: 4, align: 4 };
                desc.variant_field_offsets[0][0] = 0;
            }
            15 => *tag_offset = 1,
            16 => definition.variants[0].fields = vec![Ty::U32],
            17 => definition.variants[0].fields = vec![Ty::Never, Ty::Enum(EnumId::new(999))],
            _ => unreachable!(),
        }
        cases.push(module);
    }
    let mut overlap = fixture();
    overlap.enums[0].variants[0].fields.push(Ty::U32);
    let desc = overlap.enums[0].layout.as_mut().unwrap();
    desc.variant_field_offsets[0].push(16);
    let EnumTagEncoding::DirectWithUninhabited { variants, .. } = &mut desc.encoding else {
        unreachable!()
    };
    variants[0]
        .fields
        .push(FieldStorageLayout { size: 4, align: 4 });
    cases.push(overlap);
    cases
}

#[test]
fn direct_profile_refuses_forged_storage_and_unproved_source_rows() {
    for (index, module) in invalid_cases().iter().enumerate() {
        assert!(
            LayoutTable::new(module)
                .enum_layout(EnumId::new(7))
                .is_err(),
            "case {index}"
        );
    }
    let mut module = fixture();
    module.enums[0].variants[0].fields = vec![Ty::Enum(EnumId::new(7))];
    assert!(
        LayoutTable::new(&module)
            .enum_layout(EnumId::new(7))
            .is_err(),
        "a cycle is not a dead proof"
    );
}
