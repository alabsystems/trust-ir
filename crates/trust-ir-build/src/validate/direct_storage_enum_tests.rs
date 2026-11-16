// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, ObservedSession,
};
use trust_ir::{
    EnumDef, EnumId, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant,
    FieldStorageLayout, UninhabitedVariantLayout,
};

fn fixture() -> Module {
    let mut module = Module::new("nominal Direct source fields");
    module
        .enums
        .push(EnumDef::new(EnumId::new(9), "Infallible", vec![]));
    let mut definition = EnumDef::new(
        EnumId::new(7),
        "Direct",
        vec![
            EnumVariant {
                name: "Dead".into(),
                fields: vec![Ty::Enum(EnumId::new(9))],
                field_names: vec![],
            },
            EnumVariant {
                name: "Live".into(),
                fields: vec![Ty::U32],
                field_names: vec![],
            },
        ],
    )
    .with_repr(EnumTagRepr::U32);
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
    module.enums.insert(0, definition);
    module
}

#[derive(Default)]
struct Observer {
    count: usize,
    stop: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = ();
    fn admit(&mut self, _: ExecutionProgress) -> Result<(), ()> {
        self.count += 1;
        if self.stop == Some(self.count) {
            Err(())
        } else {
            Ok(())
        }
    }
}

fn observed(module: &Module, observer: &mut Observer) -> Vec<ValidationError> {
    let mut session = ObservedSession::new(InterpretOptions::default(), observer);
    super::observed_module_enums::validate_module_enums_observed(
        module,
        &mut session,
        ExecutionSite::Entry(FuncId::new(0)),
    )
    .unwrap()
}

#[test]
fn direct_dead_profiles_keep_nominal_declarations_and_match_observed_validation() {
    let module = fixture();
    assert!(validate_module(&module).is_empty());
    assert!(observed(&module, &mut Observer::default()).is_empty());
    assert!(module.ty_is_uninhabited(&module.enums[0].variants[0].fields[0]));
    assert!(module.ty_layout_shape(&Ty::Enum(EnumId::new(9))).is_err());
    for change in 0..5 {
        let mut module = module.clone();
        let desc = module.enums[0].layout.as_mut().unwrap();
        let EnumTagEncoding::DirectWithUninhabited { variants, .. } = &mut desc.encoding else {
            unreachable!()
        };
        match change {
            0 => variants.clear(),
            1 => variants.push(variants[0].clone()),
            2 => variants[0].fields[0].align = 0,
            3 => variants[0].fields[0].size = 1,
            4 => variants[0].variant = 1,
            _ => unreachable!(),
        }
        let expected = validate_module(&module);
        assert!(!expected.is_empty(), "case {change}");
        assert_eq!(
            observed(&module, &mut Observer::default()),
            expected,
            "case {change}"
        );
    }
    // A second declaration under the same ID must not borrow the first
    // row's valid layout to bypass checks on its own physical profile.
    let mut duplicate = module.clone();
    let mut second = duplicate.enums[0].clone();
    second.layout.as_mut().unwrap().size = 0;
    duplicate.enums.push(second);
    let expected = validate_module(&duplicate);
    assert!(!expected.is_empty());
    assert_eq!(observed(&duplicate, &mut Observer::default()), expected);

    // The indexed fast path in Module::enum_def must not change which row
    // the layout table binds: the second duplicate occupies its own ID slot.
    let mut indexed = module;
    indexed.enums[0].id = EnumId::new(1);
    indexed.enums[0].name = "First".into();
    let mut second = indexed.enums[0].clone();
    second.name = "Second".into();
    second.layout.as_mut().unwrap().size = 0;
    indexed.enums.insert(1, second);
    let expected = validate_module(&indexed);
    assert!(expected.iter().any(|error| matches!(error,
        ValidationError::ConstTypeMismatch { location, .. } if location == "enum.1 (Second) layout")));
    assert!(!expected.iter().any(|error| matches!(error,
        ValidationError::ConstTypeMismatch { location, .. } if location == "enum.1 (First) layout")));
    assert_eq!(observed(&indexed, &mut Observer::default()), expected);
}

#[test]
fn direct_dead_profile_validation_callback_refusals_remain_terminal() {
    let module = fixture();
    let mut measured = Observer::default();
    observed(&module, &mut measured);
    for stop in 1..=measured.count {
        let mut observer = Observer {
            count: 0,
            stop: Some(stop),
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let result = super::observed_module_enums::validate_module_enums_observed(
            &module,
            &mut session,
            ExecutionSite::Entry(FuncId::new(0)),
        );
        assert!(result.is_err(), "event {stop}");
        assert!(session.first_refusal().is_some());
    }
}
