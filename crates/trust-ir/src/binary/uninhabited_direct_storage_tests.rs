// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

fn fixture() -> Module {
    let row = |name: &str, fields| EnumVariant {
        name: name.into(),
        fields,
        field_names: vec![],
    };
    let mut module = Module::new("uninhabited_direct_codec");
    module.add_enum(EnumDef::new(EnumId::new(0), "Infallible", vec![]));
    let mut definition = EnumDef::new(
        EnumId::new(1),
        "Physical",
        vec![
            row("Dead", vec![Ty::Enum(EnumId::new(0))]),
            row("Live", vec![Ty::U32]),
        ],
    )
    .with_discriminants(vec![Some(-7), Some(19)])
    .with_repr(EnumTagRepr::I32);
    definition.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::DirectWithUninhabited {
            tag_offset: 0,
            variants: vec![UninhabitedVariantLayout {
                variant: 0,
                size: 4,
                align: 4,
                fields: vec![FieldStorageLayout { size: 0, align: 1 }],
            }],
        },
        size: 8,
        align: 4,
        variant_field_offsets: vec![vec![4], vec![4]],
    });
    module.add_enum(definition);
    module
}

#[test]
fn uninhabited_direct_storage_roundtrips_and_selects_its_minimum_wire_version() {
    let module = fixture();
    let encoded = serialize_module(&module).unwrap();
    assert_eq!(
        &encoded[8..12],
        &UNINHABITED_DIRECT_STORAGE_FORMAT_VERSION.to_le_bytes()
    );
    assert_eq!(deserialize_module(&encoded).unwrap(), module);
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        assert!(matches!(
            ProjectedModuleBinaryPlan::try_new(
                &module,
                ModuleBinaryOptions {
                    body,
                    ..ModuleBinaryOptions::default()
                }
            ),
            Err(BinaryProjectionError::UninhabitedDirectStorageRequiresV72)
        ));
    }
    for prior in [
        SINGLE_INHABITED_ENUM_FORMAT_VERSION,
        CLOSURE_ORIGIN_FORMAT_VERSION,
    ] {
        let mut old_header = encoded.clone();
        old_header[8..12].copy_from_slice(&prior.to_le_bytes());
        assert_eq!(
            deserialize_module(&old_header),
            Err(BinaryError::InvalidTag(4)),
            "encoding tag 4 must refuse under version {prior}"
        );
    }
    let mut legacy = module;
    legacy.enums[1].layout.as_mut().unwrap().encoding = EnumTagEncoding::Direct { tag_offset: 0 };
    let encoded = serialize_module(&legacy).unwrap();
    // Removing the storage-profile encoding leaves the existing v65 empty
    // nominal declaration. Its established version floor is preserved.
    assert_eq!(
        &encoded[8..12],
        &SINGLE_INHABITED_ENUM_FORMAT_VERSION.to_le_bytes()
    );
    assert_eq!(deserialize_module(&encoded).unwrap(), legacy);
}

#[test]
fn ordinary_direct_without_newer_features_keeps_the_legacy_wire_floor() {
    let mut module = Module::new("ordinary_direct_legacy_floor");
    let mut definition = EnumDef::new(
        EnumId::new(0),
        "Legacy",
        vec![
            EnumVariant {
                name: "Empty".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Word".into(),
                fields: vec![Ty::U32],
                field_names: vec![],
            },
        ],
    );
    definition.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
        size: 8,
        align: 4,
        variant_field_offsets: vec![vec![], vec![4]],
    });
    module.add_enum(definition);
    let encoded = serialize_module(&module).unwrap();
    assert_eq!(&encoded[8..12], &BASE_FORMAT_VERSION.to_le_bytes());
    assert_eq!(deserialize_module(&encoded).unwrap(), module);
}

#[test]
fn uninhabited_direct_storage_identity_binds_every_extent_and_observed_paths_agree() {
    use crate::interpret::{
        ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, ObservedSession,
    };
    struct Allow;
    impl ExecutionObserver for Allow {
        type Refusal = ();
        fn admit(&mut self, _: ExecutionProgress) -> Result<(), ()> {
            Ok(())
        }
    }
    let module = fixture();
    for scheme in [IdentityScheme::V2, IdentityScheme::V3] {
        let mut observer = Allow;
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let expected = module.stable_digest_under(scheme);
        assert_eq!(
            observed::observed_module_identity(
                &module,
                scheme,
                &mut session,
                ExecutionSite::Entry(FuncId::new(0)),
            )
            .unwrap(),
            expected
        );
        for dimension in 0..6 {
            let mut changed = module.clone();
            let EnumTagEncoding::DirectWithUninhabited {
                tag_offset,
                variants,
            } = &mut changed.enums[1].layout.as_mut().unwrap().encoding
            else {
                unreachable!()
            };
            match dimension {
                0 => *tag_offset = 1,
                1 => variants[0].variant = 1,
                2 => variants[0].size += 4,
                3 => variants[0].align = 2,
                4 => variants[0].fields[0].size = 1,
                5 => variants[0].fields[0].align = 2,
                _ => unreachable!(),
            }
            assert_ne!(
                changed.stable_digest_under(scheme),
                expected,
                "dimension {dimension}"
            );
        }
    }
}

#[cfg(all(feature = "parser", feature = "fmt"))]
#[test]
fn uninhabited_direct_storage_text_keeps_source_identity_and_storage_separate() {
    let module = fixture();
    let text = format!("{module}");
    assert!(text.contains("direct_uninhabited tag@0 profiles=[{variant=0 size=4 align=4 fields=[{size=0 align=1}]}]"), "{text}");
    assert!(crate::text_loss::text_losses(&module).is_empty());
    assert_eq!(crate::parser::parse_module(&text).unwrap(), module);
    for malformed in [
        text.replace("variant=0 size=4", "variant=2 size=4"),
        text.replace("size=0 align=1", "size=0 align=0"),
        text.replace("size=0 align=1", "size=3 align=2"),
    ] {
        assert!(crate::parser::parse_module(&malformed).is_err());
    }
}

#[cfg(feature = "serde")]
#[test]
fn uninhabited_direct_storage_serde_preserves_all_source_and_physical_fields() {
    let module = fixture();
    let json = serde_json::to_vec(&module).unwrap();
    assert_eq!(serde_json::from_slice::<Module>(&json).unwrap(), module);
    let bytes = rmp_serde::to_vec_named(&module).unwrap();
    assert_eq!(rmp_serde::from_slice::<Module>(&bytes).unwrap(), module);
}

fn single_inhabited_fixture() -> Module {
    let variant = |name: &str, fields| EnumVariant {
        name: name.into(),
        fields,
        field_names: Vec::new(),
    };
    let mut module = Module::new("single_inhabited_codec");
    let mut definition = EnumDef::new(
        EnumId::new(0),
        "Selected",
        vec![
            variant("DeadBefore", vec![Ty::Never]),
            variant("Live", vec![Ty::U32]),
            variant("DeadAfter", vec![Ty::Never]),
        ],
    )
    .with_discriminants(vec![Some(-9), Some(37), Some(80)]);
    definition.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::SingleInhabited { variant: 1 },
        size: 4,
        align: 4,
        variant_field_offsets: vec![vec![], vec![0], vec![]],
    });
    module.add_enum(definition);
    module
}

fn assert_version_and_projection_refusal(
    module: &Module,
    version: u32,
    refusal: BinaryProjectionError,
) {
    let encoded = serialize_module(module).unwrap();
    assert_eq!(&encoded[8..12], &version.to_le_bytes());
    assert_eq!(&deserialize_module(&encoded).unwrap(), module);
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        assert_eq!(
            ProjectedModuleBinaryPlan::try_new(
                module,
                ModuleBinaryOptions {
                    body,
                    ..ModuleBinaryOptions::default()
                }
            )
            .err(),
            Some(refusal.clone())
        );
    }
}

#[test]
fn single_inhabited_projection_refusal_reports_the_highest_wire_requirement() {
    let mut empty = Module::new("empty_nominal_enum");
    empty.add_enum(EnumDef::new(EnumId::new(0), "Infallible", vec![]));

    let storage = Ty::Storage(crate::StorageLayout::new(8, 8));
    let mut storage_only = Module::new("storage_only_floor");
    storage_only.types.push(storage.clone());
    let mut storage_and_single = single_inhabited_fixture();
    storage_and_single.types.push(storage);

    let mut closure_and_single = single_inhabited_fixture();
    closure_and_single.target_info = Some(crate::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: crate::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let signature = closure_and_single
        .add_func_type(FuncTy::unrecorded(vec![], vec![], false))
        .unwrap();
    closure_and_single.closure_types.push(ClosureTy {
        func: signature,
        captures: vec![],
    });
    closure_and_single
        .closure_layouts
        .push(crate::ClosureLayoutDescriptor {
            closure: ClosureTyId::new(0),
            size: 0,
            align: 1,
            capture_offsets: vec![],
            origin: Some(TypeOrigin::Clean {
                decl: "Original.Closure".into(),
                env_digest: ProofDigest::sha256([7; 32]),
            }),
        });

    for (module, version, refusal) in [
        (
            empty,
            SINGLE_INHABITED_ENUM_FORMAT_VERSION,
            BinaryProjectionError::SingleInhabitedRequiresV65,
        ),
        (
            storage_only,
            STORAGE_LAYOUT_FORMAT_VERSION,
            BinaryProjectionError::StorageRequiresV64,
        ),
        (
            storage_and_single,
            SINGLE_INHABITED_ENUM_FORMAT_VERSION,
            BinaryProjectionError::SingleInhabitedRequiresV65,
        ),
        (
            closure_and_single,
            CLOSURE_ORIGIN_FORMAT_VERSION,
            BinaryProjectionError::ClosureOriginRequiresV66,
        ),
    ] {
        assert_version_and_projection_refusal(&module, version, refusal);
    }
    assert_eq!(
        BinaryProjectionError::SingleInhabitedRequiresV65.to_string(),
        "single-inhabited or empty nominal enum requires wire v65"
    );
}

#[test]
fn single_inhabited_three_row_identity_retains_v2_v3_observed_parity() {
    use crate::interpret::{
        ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, ObservedSession,
    };
    struct Allow;
    impl ExecutionObserver for Allow {
        type Refusal = ();
        fn admit(&mut self, _: ExecutionProgress) -> Result<(), ()> {
            Ok(())
        }
    }
    let module = single_inhabited_fixture();
    assert_version_and_projection_refusal(
        &module,
        SINGLE_INHABITED_ENUM_FORMAT_VERSION,
        BinaryProjectionError::SingleInhabitedRequiresV65,
    );
    for scheme in [IdentityScheme::V2, IdentityScheme::V3] {
        let mut observer = Allow;
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            observed::observed_module_identity(
                &module,
                scheme,
                &mut session,
                ExecutionSite::Entry(FuncId::new(0))
            )
            .unwrap(),
            module.stable_digest_under(scheme)
        );
        let mut changed = module.clone();
        changed.enums[0].layout.as_mut().unwrap().encoding =
            EnumTagEncoding::SingleInhabited { variant: 2 };
        assert_ne!(
            module.stable_digest_under(scheme),
            changed.stable_digest_under(scheme)
        );
    }
}

// Retain the original three-row codec controls under the current native syntax.
#[cfg(all(feature = "parser", feature = "fmt"))]
#[test]
fn single_three_row_text_keeps_selected_index_and_empty_inactive_offsets() {
    let module = single_inhabited_fixture();
    let text = format!("{module}");
    assert!(
        text.contains("layout(single inhabited=1 size=4 align=4 offsets=[[], [0], []])"),
        "{text}"
    );
    assert!(crate::text_loss::text_losses(&module).is_empty());
    assert_eq!(crate::parser::parse_module(&text).unwrap(), module);
    let wrong_selected = text.replace("inhabited=1", "inhabited=3");
    assert_ne!(
        wrong_selected, text,
        "the selected-index mutant must change the input"
    );
    assert!(crate::parser::parse_module(&wrong_selected).is_err());
    let wrong_inactive = text.replace("offsets=[[], [0], []]", "offsets=[[0], [0], []]");
    assert_ne!(
        wrong_inactive, text,
        "the inactive-row mutant must change the input"
    );
    assert!(crate::parser::parse_module(&wrong_inactive).is_err());
}

#[cfg(feature = "serde")]
#[test]
fn single_three_row_named_messagepack_and_json_keep_selected_index() {
    let module = single_inhabited_fixture();
    let json = serde_json::to_vec(&module).unwrap();
    assert_eq!(serde_json::from_slice::<Module>(&json).unwrap(), module);
    let named = rmp_serde::to_vec_named(&module).unwrap();
    assert_eq!(rmp_serde::from_slice::<Module>(&named).unwrap(), module);
}
