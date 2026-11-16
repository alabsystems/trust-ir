// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Nominal empty declarations, payload-only storage and observed refusals.
use trust_ir::interpret::{
    ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, InterpretValueKind,
    Interpreter, ObservedSession,
};
use trust_ir::{
    Constant, EnumDef, EnumId, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant,
    FuncId, LayoutTable, Module, Ty,
};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

fn fixture(active: usize) -> Module {
    let mut module = Module::new("Result_with_nominal_Infallible");
    module.add_enum(EnumDef::new(
        EnumId::new(0),
        "core::convert::Infallible",
        vec![],
    ));
    let a = EnumVariant {
        name: "Value".into(),
        fields: vec![Ty::U32],
        field_names: vec!["value".into()],
    };
    let b = EnumVariant {
        name: "Impossible".into(),
        fields: vec![Ty::Enum(EnumId::new(0))],
        field_names: vec!["nominal_void".into()],
    };
    let mut definition = EnumDef::new(
        EnumId::new(1),
        "Result",
        if active == 0 { vec![a, b] } else { vec![b, a] },
    );
    definition.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::SingleInhabited {
            variant: active as u32,
        },
        size: 4,
        align: 4,
        variant_field_offsets: if active == 0 {
            vec![vec![0], vec![]]
        } else {
            vec![vec![], vec![0]]
        },
    });
    module.add_enum(definition);
    module
}

#[test]
fn nominal_infallible_is_retained_without_a_physical_layout() {
    for active in [0, 1] {
        let module = fixture(active);
        assert!(
            validate_module(&module).is_empty(),
            "{:?}",
            validate_module(&module)
        );
        assert_eq!(module.enums.len(), 2);
        assert_eq!(module.enums[0].name, "core::convert::Infallible");
        assert!(module.enums[0].variants.is_empty());
        assert!(module.ty_is_uninhabited(&Ty::Enum(EnumId::new(0))));
        assert!(module.ty_layout_shape(&Ty::Enum(EnumId::new(0))).is_err());
        let image = module.enum_layout_shape(EnumId::new(1)).unwrap();
        assert_eq!((image.size_bits, image.align_bits), (32, 32));
    }
}

#[test]
fn actual_typed_store_load_recovers_both_active_indices() {
    for active in [0, 1] {
        let mut builder = ModuleBuilder::new("single_inhabited_storage");
        for definition in fixture(active).enums {
            builder.add_enum(definition);
        }
        let ty = Ty::Enum(EnumId::new(1));
        let signature = builder.add_func_type(vec![], vec![ty.clone()]);
        let mut body = builder.function("roundtrip", signature);
        let entry = body.create_block();
        body.switch_to_block(entry);
        let value = body.const_value(
            ty.clone(),
            Constant::Aggregate(vec![
                Constant::Int(active as i128),
                Constant::Int(0x1234_5678),
            ]),
        );
        let pointer = body.alloca(ty.clone());
        body.store(ty.clone(), pointer, value);
        let loaded = body.load(ty, pointer);
        body.ret(vec![loaded]);
        let function = body.build();
        let module = builder.build().unwrap();
        assert!(
            validate_module(&module).is_empty(),
            "{:?}",
            validate_module(&module)
        );
        let outcome = Interpreter::with_module(&module)
            .execute_func(function, [])
            .unwrap();
        assert_eq!(outcome.host_calls, 0);
        let InterpretValueKind::Aggregate(fields) = &outcome.returns[0].kind else {
            panic!("enum aggregate")
        };
        assert_eq!(fields.len(), 2);
        assert_eq!(
            fields[0],
            trust_ir::interpret::InterpretValue::int(Ty::U8, active as i128).unwrap()
        );
        assert_eq!(
            fields[1],
            trust_ir::interpret::InterpretValue::int(Ty::U32, 0x1234_5678).unwrap()
        );
    }
}

#[test]
fn descriptor_mutations_and_legacy_untagged_fail_closed() {
    for case in 0..7 {
        let mut module = fixture(1);
        match case {
            0 => {
                module.enums[1].layout.as_mut().unwrap().encoding =
                    EnumTagEncoding::SingleInhabited { variant: 2 }
            }
            1 => {
                module.enums[1].layout.as_mut().unwrap().encoding =
                    EnumTagEncoding::SingleInhabited { variant: 0 }
            }
            2 => module.enums[1].variants[0].fields = vec![Ty::U32],
            3 => {
                module.enums[1]
                    .layout
                    .as_mut()
                    .unwrap()
                    .variant_field_offsets[0] = vec![0]
            }
            4 => {
                module.enums[1]
                    .layout
                    .as_mut()
                    .unwrap()
                    .variant_field_offsets[1] = vec![1]
            }
            5 => module.enums[1].layout.as_mut().unwrap().encoding = EnumTagEncoding::Untagged,
            _ => module.enums[1]
                .layout
                .as_mut()
                .unwrap()
                .variant_field_offsets[1]
                .clear(),
        }
        let expected = validate_module(&module);
        assert!(!expected.is_empty(), "case {case}");
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let observed = trust_ir_build::validate::validate_module_enums_observed(
            &module,
            &mut session,
            ExecutionSite::Entry(FuncId::new(0)),
        )
        .unwrap();
        assert_eq!(
            observed, expected,
            "same complete ordered enum diagnostics, case {case}"
        );
        assert!(session.first_refusal().is_none());
        assert!(
            module.enum_layout_shape(EnumId::new(1)).is_err(),
            "case {case}"
        );
    }
}

#[test]
fn inactive_types_still_receive_global_nominal_validation() {
    let mut module = fixture(1);
    module.enums[1].variants[0].fields = vec![Ty::Never, Ty::Enum(EnumId::new(999))];
    module.enums[1].variants[0].field_names.clear();
    assert!(module.variant_is_uninhabited(&module.enums[1].variants[0]));
    assert!(validate_module(&module).iter().any(|error| matches!(
        error,
        ValidationError::DanglingTypeReference {
            kind: "enum",
            id: 999,
            ..
        }
    )));
    let mut cycle = fixture(1);
    cycle.enums.push(EnumDef::new(
        EnumId::new(2),
        "UnseededCycle",
        vec![EnumVariant {
            name: "Again".into(),
            fields: vec![Ty::Enum(EnumId::new(2))],
            field_names: vec![],
        }],
    ));
    cycle.enums[1].variants[0].fields = vec![Ty::Enum(EnumId::new(2))];
    assert!(!cycle.variant_is_uninhabited(&cycle.enums[1].variants[0]));
    assert!(!validate_module(&cycle).is_empty());
    assert!(cycle.enum_layout_shape(EnumId::new(1)).is_err());
}

#[test]
fn empty_declaration_cannot_claim_repr_discriminants_or_storage() {
    for case in 0..3 {
        let mut module = fixture(1);
        match case {
            0 => module.enums[0].repr = Some(EnumTagRepr::U8),
            1 => module.enums[0].discriminants = vec![Some(0)],
            _ => {
                module.enums[0].layout = Some(EnumLayoutDescriptor {
                    encoding: EnumTagEncoding::Direct { tag_offset: 0 },
                    size: 0,
                    align: 1,
                    variant_field_offsets: vec![],
                })
            }
        }
        assert!(!validate_module(&module).is_empty());
    }
    for construct in [false, true] {
        let mut builder = ModuleBuilder::new("empty_has_no_value_or_storage");
        builder.add_enum(EnumDef::new(EnumId::new(0), "NominalVoid", vec![]));
        let signature = builder.add_func_type(vec![], vec![Ty::U32]);
        let mut body = builder.function("refuse", signature);
        let entry = body.create_block();
        body.switch_to_block(entry);
        if construct {
            let _ = body.make_enum_variant(Ty::Enum(EnumId::new(0)), 0, vec![]);
        } else {
            let _ = body.alloca(Ty::Enum(EnumId::new(0)));
        }
        let value = body.const_value(Ty::U32, Constant::Int(0));
        body.ret(vec![value]);
        let function = body.build();
        let module = builder.build().unwrap();
        assert!(
            Interpreter::with_module(&module)
                .execute_func(function, [])
                .is_err()
        );
    }
}

#[derive(Default)]
struct Observer {
    events: usize,
    stop: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, _: ExecutionProgress) -> Result<(), Self::Refusal> {
        if self.stop == Some(self.events) {
            return Err("single-inhabited observed stop");
        }
        self.events += 1;
        Ok(())
    }
}

#[test]
fn observed_wire_identity_traverses_the_new_selector_and_empty_declaration() {
    for selected in [0, 1] {
        let module = fixture(selected);
        let site = ExecutionSite::Entry(FuncId::new(0));
        let mut observer = Observer::default();
        {
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                module
                    .checked_stable_digest_observed(&mut session, site)
                    .unwrap(),
                module.stable_digest()
            );
            assert!(session.first_refusal().is_none());
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        }
        let events = observer.events;
        assert!(events > 10);
        for stop in [0, events / 2, events - 1] {
            let mut observer = Observer {
                events: 0,
                stop: Some(stop),
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert!(
                module
                    .checked_stable_digest_observed(&mut session, site)
                    .is_err()
            );
            assert!(session.first_refusal().is_some());
        }
    }
}

#[test]
fn observed_layout_and_enum_diagnostics_match_without_unpaid_shortcuts() {
    let module = fixture(1);
    let before = module.clone();
    let ty = Ty::Enum(EnumId::new(1));
    let site = ExecutionSite::Entry(FuncId::new(0));
    let mut observer = Observer::default();
    {
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let table = LayoutTable::new_observed(&module, &mut session, site).unwrap();
        let actual = table
            .ty_layout_observed(&ty, &mut session, site)
            .unwrap()
            .unwrap();
        assert_eq!(*actual, *LayoutTable::new(&module).ty_layout(&ty).unwrap());
        assert!(session.first_refusal().is_none());
    }
    let events = observer.events;
    assert!(events > 10);
    {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(
            trust_ir_build::validate::validate_module_enums_observed(&module, &mut session, site)
                .unwrap()
                .is_empty()
        );
    }
    for stop in [0, 1, events / 2, events - 1] {
        let mut observer = Observer {
            events: 0,
            stop: Some(stop),
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let result = LayoutTable::new_observed(&module, &mut session, site)
            .and_then(|table| table.ty_layout_observed(&ty, &mut session, site));
        assert!(
            result.is_err(),
            "actual reached layout event {stop}/{events}"
        );
        assert!(session.first_refusal().is_some());
    }
    assert_eq!(module, before);
}

#[test]
fn single_inhabited_accepts_transitive_dead_payloads_without_sizing_them() {
    let mut module = fixture(1);
    let huge = module.add_type(Ty::U128).unwrap();
    module.structs.push(trust_ir::StructDef {
        id: trust_ir::value::StructId::new(10),
        name: "DeadWrapper".into(),
        fields: vec![trust_ir::FieldDef {
            name: "never".into(),
            ty: Ty::Never,
            offset: None,
        }],
        size: None,
        align: None,
        repr: trust_ir::StructRepr::Rust,
        origin: None,
    });
    module.enums[1].discriminants = vec![Some(-4), Some(19)];
    module.enums[1].variants[0].fields = vec![Ty::Tuple(vec![
        Ty::Struct(trust_ir::value::StructId::new(10)),
        Ty::Array(huge, u64::MAX),
    ])];
    assert!(
        validate_module(&module).is_empty(),
        "{:?}",
        validate_module(&module)
    );
    assert_eq!(
        module.enum_layout_shape(EnumId::new(1)).unwrap().size_bits,
        32
    );
}

// These operations have no value/storage interpretation for a nominal empty enum.
// Keep a valid U32 function header so refusal must arise from the body operation.
fn empty_declaration_operation_module(load: Option<Ty>) -> (Module, FuncId) {
    let mut builder = ModuleBuilder::new("empty_declaration_operation");
    builder.add_enum(EnumDef::new(EnumId::new(0), "NominalVoid", vec![]));
    let signature = builder.add_func_type(vec![], vec![Ty::U32]);
    let mut body = builder.function("empty_operation", signature);
    let entry = body.create_block();
    body.switch_to_block(entry);
    match load {
        None => {
            let _ = body.const_value(
                Ty::Enum(EnumId::new(0)),
                Constant::Aggregate(vec![Constant::Int(0)]),
            );
        }
        Some(ty) => {
            let pointer = body.alloca(Ty::U8);
            let byte = body.const_value(Ty::U8, Constant::Int(0));
            body.store(Ty::U8, pointer, byte);
            let _ = body.load(ty, pointer);
        }
    }
    let result = body.const_value(Ty::U32, Constant::Int(0));
    body.ret(vec![result]);
    let function = body.build();
    (builder.build().unwrap(), function)
}

#[test]
fn empty_declaration_aggregate_constant_is_a_type_error() {
    let (module, function) = empty_declaration_operation_module(None);
    assert!(!validate_module(&module).is_empty());
    let error = Interpreter::with_module(&module)
        .execute_func(function, [])
        .unwrap_err();
    assert_eq!(
        error.code,
        trust_ir::interpret::InterpretErrorCode::TypeError
    );
}

#[test]
fn empty_declaration_typed_load_is_a_type_error_after_initialized_byte_setup() {
    let (control, function) = empty_declaration_operation_module(Some(Ty::U8));
    assert!(validate_module(&control).is_empty());
    Interpreter::with_module(&control)
        .execute_func(function, [])
        .expect("the same initialized U8 allocation/store/load prefix executes");

    let (module, function) = empty_declaration_operation_module(Some(Ty::Enum(EnumId::new(0))));
    let error = Interpreter::with_module(&module)
        .execute_func(function, [])
        .unwrap_err();
    assert_eq!(
        error.code,
        trust_ir::interpret::InterpretErrorCode::TypeError
    );
}

fn three_row_single_control_module() -> Module {
    let variant = |name: &str, fields| EnumVariant {
        name: name.into(),
        fields,
        field_names: vec![],
    };
    let mut module = Module::new("three_row_single_retained_controls");
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

#[test]
fn three_row_single_refuses_both_v38_projections_at_its_actual_v65_floor() {
    use trust_ir::binary::{
        BinaryProjectionError, ModuleBinaryBody, ModuleBinaryOptions, ProjectedModuleBinaryPlan,
        SINGLE_INHABITED_ENUM_FORMAT_VERSION,
    };
    let module = three_row_single_control_module();
    assert!(validate_module(&module).is_empty());
    let bytes = trust_ir::binary::serialize_module(&module).unwrap();
    assert_eq!(
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
        SINGLE_INHABITED_ENUM_FORMAT_VERSION,
    );
    assert_eq!(SINGLE_INHABITED_ENUM_FORMAT_VERSION, 65);
    assert_eq!(
        trust_ir::binary::deserialize_module(&bytes).unwrap(),
        module
    );
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        // The refusal names the actual wire floor for this selected layout.
        assert!(matches!(
            ProjectedModuleBinaryPlan::try_new(
                &module,
                ModuleBinaryOptions {
                    body,
                    ..ModuleBinaryOptions::default()
                },
            ),
            Err(BinaryProjectionError::SingleInhabitedRequiresV65),
        ));
    }
}

#[test]
fn three_row_single_current_text_refuses_bad_selector_and_inactive_offsets() {
    let module = three_row_single_control_module();
    assert!(validate_module(&module).is_empty());
    assert_eq!(module.enums[0].variants.len(), 3);
    let text = trust_ir::format::canonical(&module);
    assert_eq!(trust_ir::parser::parse_module(&text).unwrap(), module);
    let mutate_once = |input: &str, original: &str, replacement: &str, label: &str| {
        assert_eq!(
            input.matches(original).count(),
            1,
            "{label}: actual grammar"
        );
        let mutated = input.replacen(original, replacement, 1);
        assert_ne!(mutated, input, "{label}: mutation must change the input");
        mutated
    };

    let bad_selector = mutate_once(
        &text,
        "single inhabited=1",
        "single inhabited=3",
        "selector outside three declarations",
    );
    // The parser checks inactive rows before selector bounds. With selector3,
    // every existing row is inactive: clear the former active row so neither
    // the inactive-offset guard nor the selected-field-count guard masks bounds.
    let bad_selector = mutate_once(
        &bad_selector,
        "offsets=[[], [0], []]",
        "offsets=[[], [], []]",
        "clear the former active row for selector bounds",
    );
    let error = trust_ir::parser::parse_module(&bad_selector).unwrap_err();
    assert_eq!(
        error.message,
        "a single-inhabited enum selector must name a declared variant (enum @Selected)",
    );

    let inactive_offsets = mutate_once(
        &text,
        "offsets=[[], [0], []]",
        "offsets=[[0], [0], []]",
        "nonempty inactive row",
    );
    let error = trust_ir::parser::parse_module(&inactive_offsets).unwrap_err();
    assert_eq!(
        error.message,
        "an inactive single-inhabited variant has no physical offset row (enum @Selected)",
    );
}

fn assert_current_enum_refusal_matches_observed(
    module: &Module,
    label: &str,
) -> Vec<ValidationError> {
    let before = module.clone();
    let expected = validate_module(module);
    assert!(!expected.is_empty(), "{label}");
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let observed = trust_ir_build::validate::validate_module_enums_observed(
        module,
        &mut session,
        ExecutionSite::Entry(FuncId::new(0)),
    )
    .unwrap();
    assert_eq!(
        observed, expected,
        "complete ordered enum diagnostics: {label}"
    );
    assert!(session.first_refusal().is_none());
    assert_eq!(module, &before, "{label}: source metadata stays intact");
    expected
}

#[test]
fn single_descriptor_refuses_exact_outer_align_two_and_active_offset_four() {
    let baseline = fixture(1);
    assert!(validate_module(&baseline).is_empty());
    let layout = baseline.enum_layout_shape(EnumId::new(1)).unwrap();
    assert_eq!((layout.size_bits, layout.align_bits), (32, 32));
    for (label, align, offset) in [
        ("outer align2 below U32 child alignment", 2, 0),
        ("active offset4 outside four-byte image", 4, 4),
    ] {
        let mut invalid = baseline.clone();
        let descriptor = invalid.enums[1].layout.as_mut().unwrap();
        descriptor.align = align;
        descriptor.variant_field_offsets[1] = vec![offset];
        assert_eq!(descriptor.size, 4);
        assert!(descriptor.variant_field_offsets[0].is_empty());
        assert_current_enum_refusal_matches_observed(&invalid, label);
        assert!(
            invalid.enum_layout_shape(EnumId::new(1)).is_err(),
            "{label}"
        );
    }
}

#[test]
fn duplicate_empty_declaration_keeps_exact_nominal_duplicate_refusal() {
    let mut module = Module::new("duplicate_empty_nominal_identity");
    module.add_enum(EnumDef::new(EnumId::new(0), "NominalVoid", vec![]));
    assert!(validate_module(&module).is_empty());
    let duplicate = module.enums[0].clone();
    module.add_enum(duplicate);
    assert_eq!(module.enums.len(), 2);
    assert!(module.enums.iter().all(|row| row.variants.is_empty()));
    let errors = assert_current_enum_refusal_matches_observed(&module, "duplicate empty ID0");
    assert_eq!(errors, vec![ValidationError::DuplicateEnumId(0)]);
}

#[test]
fn empty_declaration_refuses_original_four_encoding_metadata_claims() {
    let mut baseline = Module::new("empty_nominal_encoding_metadata");
    baseline.add_enum(EnumDef::new(EnumId::new(0), "NominalVoid", vec![]));
    assert!(validate_module(&baseline).is_empty());
    // This is the exact original four-encoding roster. DirectWithUninhabited
    // has separate current storage-profile controls; no encoding grants a value
    // or byte image to this empty nominal declaration.
    for (label, encoding) in [
        ("Direct", EnumTagEncoding::Direct { tag_offset: 0 }),
        ("Untagged", EnumTagEncoding::Untagged),
        (
            "SingleInhabited",
            EnumTagEncoding::SingleInhabited { variant: 0 },
        ),
        (
            "Niche",
            EnumTagEncoding::Niche {
                untagged_variant: 0,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: 0,
                niche_offset: 0,
                niche_ty: EnumTagRepr::U8,
            },
        ),
    ] {
        let mut invalid = baseline.clone();
        invalid.enums[0].layout = Some(EnumLayoutDescriptor {
            encoding,
            size: 0,
            align: 1,
            variant_field_offsets: vec![],
        });
        let errors = assert_current_enum_refusal_matches_observed(&invalid, label);
        assert!(
            errors
                .iter()
                .any(|error| matches!(error, ValidationError::ConstTypeMismatch { .. },)),
            "{label}: metadata refusal"
        );
        assert!(
            invalid.ty_layout_shape(&Ty::Enum(EnumId::new(0))).is_err(),
            "{label}"
        );
    }
    // The original declaration control also rejects a padded implicit
    // discriminant row; the preexisting target covers the explicit Some(0) row.
    let mut padded = baseline;
    padded.enums[0].discriminants = vec![None];
    assert_current_enum_refusal_matches_observed(&padded, "padded implicit discriminant");
}
