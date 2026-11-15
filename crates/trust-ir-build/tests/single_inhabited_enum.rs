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
