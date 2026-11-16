// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Full-width content controls for the optional native-transport-json profile.
//! Synthetic changed facts exercise codecs only; semantic admission and proof
//! authority remain separate from successful typed content roundtrips.

use super::*;
use crate::request::transport::{
    native_bundle_transport_payload, rehydrate_native_bundle_transport_payload,
};
use crate::{AttrValue, Constant, EnumDef, EnumTagRepr, EnumVariant, ProofAnnotation};
use serde::Serialize;
use serde::de::DeserializeOwned;
use serde_json::Value;
use std::fmt::Debug;

const INTEGER_BOUNDARIES: [i128; 9] = [
    i128::MIN,
    i64::MIN as i128 - 1,
    i64::MIN as i128,
    -1,
    0,
    1,
    u64::MAX as i128,
    u64::MAX as i128 + 1,
    i128::MAX,
];

fn named_bundle_roundtrip(bundle: &NativeVerificationBundle) {
    // Native bundle sidecars use the maintained named-struct MessagePack profile.
    // Scalar compact MessagePack below remains a separate wire profile.
    let bytes = rmp_serde::to_vec_named(bundle).expect("named bundle MessagePack writer");
    let restored: NativeVerificationBundle =
        rmp_serde::from_slice(&bytes).expect("named bundle MessagePack reader");
    assert_eq!(&restored, bundle);
    assert_eq!(rmp_serde::to_vec_named(&restored).unwrap(), bytes);
}

fn admitted_seed() -> NativeVerificationBundle {
    // This is the maintained, separately admitted fixture. It removes the
    // existing deliberately unreplayable TrustVc request by its existing owner;
    // it does not manufacture a certificate, status or source-generation grade.
    let bundle = source_generation_authority_bundle();
    bundle
        .validate()
        .expect("maintained native admission control");
    let payload = native_bundle_transport_payload(&bundle)
        .expect("ordinary admitted fixture must be transportable");
    check_public_payload(&bundle, &payload);
    bundle
}

fn check_public_payload(bundle: &NativeVerificationBundle, payload: &Value) -> Value {
    named_bundle_roundtrip(bundle);
    let restored = rehydrate_native_bundle_transport_payload(payload)
        .expect("public reader must restore the exact typed content");
    assert_eq!(&restored, bundle);
    assert_eq!(
        native_bundle_transport_payload(&restored).unwrap(),
        *payload,
        "public re-encoding must retain the exact transport payload",
    );
    payload["bundle"].clone()
}

fn assert_number(value: &Value, expected: i128) {
    assert!(
        value.is_number(),
        "the raw field's numeric spelling changed"
    );
    assert_eq!(value.to_string(), expected.to_string());
}

fn raw_i128_case(
    label: &str,
    bundle: &NativeVerificationBundle,
    number: i128,
    field: impl Fn(&Value) -> &Value,
) {
    // The direct typed JSON writer and parser are a separate route from Value.
    let direct = serde_json::to_vec(bundle).expect("typed JSON writer");
    assert_eq!(
        serde_json::from_slice::<NativeVerificationBundle>(&direct).unwrap(),
        *bundle,
    );
    let payload = native_bundle_transport_payload(bundle)
        .unwrap_or_else(|error| panic!("wide_json {label} {number}: {error}"));
    let typed_json = check_public_payload(bundle, &payload);
    assert_number(field(&typed_json), number);
    eprintln!("wide_json {label} {number}: exact public roundtrip");
}

fn json_roundtrip<T: Serialize + DeserializeOwned + PartialEq + Debug>(original: &T) -> Value {
    let direct = serde_json::to_vec(original).unwrap();
    let value = serde_json::to_value(original).unwrap();
    assert_eq!(
        serde_json::from_value::<T>(value.clone()).unwrap(),
        *original
    );
    assert_eq!(serde_json::from_slice::<T>(&direct).unwrap(), *original);
    assert_eq!(
        serde_json::from_slice::<T>(&serde_json::to_vec(&value).unwrap()).unwrap(),
        *original,
    );
    value
}

fn scalar_roundtrip<T: Serialize + DeserializeOwned + PartialEq + Debug>(original: &T) -> Value {
    let value = json_roundtrip(original);
    let bytes = rmp_serde::to_vec(original).unwrap();
    let restored: T = rmp_serde::from_slice(&bytes).unwrap();
    assert_eq!(restored, *original);
    assert_eq!(rmp_serde::to_vec(&restored).unwrap(), bytes);
    value
}

fn constant_content(ty: Ty, value: Constant) -> NativeVerificationBundle {
    let mut bundle = admitted_seed();
    let result = ValueId::new(100);
    assert!(bundle.module.functions[0].blocks.iter().all(|block| {
        block.params.iter().all(|(id, _)| *id != result)
            && block
                .body
                .iter()
                .all(|node| !node.results.contains(&result))
    }));
    bundle.module.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Const { ty, value }).with_result(result));
    refresh_native_bundle_module_identity(&mut bundle);
    // The mutated content is synthetic transport data. A successful decode
    // does not imply separate semantic module admission or proof authority.
    bundle
}

#[test]
fn native_bundle_wide_enum_discriminants_roundtrip_exactly() {
    for number in INTEGER_BOUNDARIES {
        let mut bundle = admitted_seed();
        let enum_index = bundle.module.enums.len();
        let enum_id = EnumId::new(enum_index as u32);
        bundle.module.add_enum(
            EnumDef::new(
                enum_id,
                "WideJson",
                vec![EnumVariant {
                    name: "Value".into(),
                    fields: vec![],
                    field_names: vec![],
                }],
            )
            .with_discriminants(vec![Some(number)])
            .with_repr(EnumTagRepr::I128),
        );
        refresh_native_bundle_module_identity(&mut bundle);
        raw_i128_case("enum_discriminant", &bundle, number, |json| {
            &json["module"]["enums"][enum_index]["discriminants"][0]
        });
    }
    // Retain the explicit implicit-discriminant/null representation as well.
    let mut bundle = admitted_seed();
    let index = bundle.module.enums.len();
    bundle.module.add_enum(
        EnumDef::new(
            EnumId::new(index as u32),
            "ImplicitJson",
            ["Explicit", "Implicit"]
                .into_iter()
                .map(|name| EnumVariant {
                    name: name.into(),
                    fields: vec![],
                    field_names: vec![],
                })
                .collect(),
        )
        .with_discriminants(vec![Some(0), None])
        .with_repr(EnumTagRepr::I128),
    );
    refresh_native_bundle_module_identity(&mut bundle);
    let payload = native_bundle_transport_payload(&bundle).unwrap();
    let json = check_public_payload(&bundle, &payload);
    assert!(json["module"]["enums"][index]["discriminants"][1].is_null());

    // Retain the earlier single-vector case: wide values occur on both sides
    // of an interior null. Each numeric boundary above remains independent.
    let mut bundle = admitted_seed();
    let index = bundle.module.enums.len();
    let discriminants = vec![
        Some(i128::MIN),
        None,
        Some(i128::MAX),
        Some(1i128 << 64),
        Some(i64::MIN as i128),
        Some(0),
        Some(u64::MAX as i128),
    ];
    let variants = [
        "Minimum",
        "Implicit",
        "Maximum",
        "BeyondU64",
        "I64Min",
        "Zero",
        "U64Max",
    ]
    .into_iter()
    .map(|name| EnumVariant {
        name: name.into(),
        fields: vec![],
        field_names: vec![],
    })
    .collect();
    bundle.module.add_enum(
        EnumDef::new(EnumId::new(index as u32), "MixedWideJson", variants)
            .with_discriminants(discriminants)
            .with_repr(EnumTagRepr::I128),
    );
    refresh_native_bundle_module_identity(&mut bundle);
    // admitted_seed validates the seed bundle before this synthetic change.
    // Codec success does not admit the changed module or compiler facts.
    let direct = serde_json::to_vec(&bundle).expect("mixed enum typed JSON writer");
    assert_eq!(
        serde_json::from_slice::<NativeVerificationBundle>(&direct)
            .expect("mixed enum typed JSON reader"),
        bundle,
    );
    let payload =
        native_bundle_transport_payload(&bundle).expect("mixed enum public native JSON writer");
    let json = check_public_payload(&bundle, &payload);
    let actual = json["module"]["enums"][index]["discriminants"]
        .as_array()
        .expect("mixed enum discriminant vector");
    assert_eq!(actual.len(), 7);
    assert_number(&actual[0], i128::MIN);
    assert!(actual[1].is_null());
    assert_number(&actual[2], i128::MAX);
    assert_number(&actual[3], 1i128 << 64);
    assert_number(&actual[4], i64::MIN as i128);
    assert_number(&actual[5], 0);
    assert_number(&actual[6], u64::MAX as i128);
    eprintln!(
        "wide_json mixed_enum_with_interior_null: exact public and named MessagePack roundtrip"
    );
}

#[test]
fn native_bundle_wide_variant_facts_roundtrip_exactly() {
    let mut seed = admitted_seed();
    add_native_direct_enum_fact(&mut seed);
    refresh_native_bundle_module_identity(&mut seed);
    seed.validate()
        .expect("unchanged direct enum fact admission control");
    let payload = native_bundle_transport_payload(&seed).unwrap();
    check_public_payload(&seed, &payload);
    for number in INTEGER_BOUNDARIES {
        let mut bundle = seed.clone();
        bundle.compiler_facts.adt_layouts[0]
            .enum_layout
            .as_mut()
            .unwrap()
            .variants[0]
            .discriminant = Some(number);
        // These deliberately changed facts are synthetic. No admission claim
        // is made for a fact that may disagree with its source declaration.
        raw_i128_case("variant_fact", &bundle, number, |json| {
            &json["compiler_facts"]["adt_layouts"][0]["enum_layout"]["variants"][0]["discriminant"]
        });
    }
}

#[test]
fn native_bundle_wide_pointer_facts_roundtrip_exactly() {
    let mut seed = native_bundle();
    add_pointer_offset_ir(&mut seed);
    let fact = pointer_offset_fact(&seed);
    seed.compiler_facts.pointer_offsets.push(fact);
    seed.compiler_facts.obligation_sources[1].cause = NativeObligationCause::PointerOffset;
    seed.compiler_facts.obligation_sources[1]
        .facts
        .push(NativeCompilerFactRef::PointerOffset(
            NativeCompilerFactId::new(40),
        ));
    remove_unreplayed_trust_vc_fixture(&mut seed);
    refresh_native_bundle_module_identity(&mut seed);
    seed.validate()
        .expect("unchanged bound pointer fact admission control");
    let payload = native_bundle_transport_payload(&seed).unwrap();
    check_public_payload(&seed, &payload);
    for number in INTEGER_BOUNDARIES {
        let mut bundle = seed.clone();
        bundle.compiler_facts.pointer_offsets[0].signed_offset_const = Some(number);
        // In particular, outside-I64 values do not become valid I64 offset
        // facts merely because this content codec might represent them.
        raw_i128_case("pointer_fact", &bundle, number, |json| {
            &json["compiler_facts"]["pointer_offsets"][0]["signed_offset_const"]
        });
    }
}

#[test]
fn existing_wide_adapters_keep_their_json_spellings_and_binary_roundtrips() {
    for (number, expected) in [
        (0, "{\"Int\":0}".to_owned()),
        (-1, "{\"Int\":-1}".to_owned()),
        (i64::MIN as i128, format!("{{\"Int\":{}}}", i64::MIN)),
        (u64::MAX as i128, format!("{{\"Int\":{}}}", u64::MAX)),
        (i128::MIN, format!("{{\"Int\":\"{}\"}}", i128::MIN)),
        (i128::MAX, format!("{{\"Int\":\"{}\"}}", i128::MAX)),
    ] {
        let constant = Constant::Int(number);
        assert_eq!(serde_json::to_string(&constant).unwrap(), expected);
        scalar_roundtrip(&constant);
        let bundle = constant_content(Ty::I128, constant);
        let payload = native_bundle_transport_payload(&bundle).unwrap();
        check_public_payload(&bundle, &payload);
    }
    let constant = Constant::U128(u128::MAX);
    assert_eq!(
        serde_json::to_string(&constant).unwrap(),
        format!("{{\"U128\":\"{}\"}}", u128::MAX),
    );
    scalar_roundtrip(&constant);
    let bundle = constant_content(Ty::U128, constant);
    check_public_payload(&bundle, &native_bundle_transport_payload(&bundle).unwrap());
    for (ones, expected) in [
        (
            u64::MAX as u128,
            format!("{{\"KnownBits\":{{\"zeros\":0,\"ones\":{}}}}}", u64::MAX),
        ),
        (
            u128::MAX,
            format!(
                "{{\"KnownBits\":{{\"zeros\":0,\"ones\":\"{}\"}}}}",
                u128::MAX
            ),
        ),
    ] {
        let annotation = ProofAnnotation::KnownBits { zeros: 0, ones };
        assert_eq!(serde_json::to_string(&annotation).unwrap(), expected);
        scalar_roundtrip(&annotation);
    }
    scalar_roundtrip(&NativeIntegerRange {
        start: i128::MIN,
        end: i128::MAX,
    });
    assert_eq!(
        serde_json::to_string(&NativeIntegerRange {
            start: i128::MIN,
            end: i128::MAX,
        })
        .unwrap(),
        r#"{"start":"-170141183460469231731687303715884105728","end":"170141183460469231731687303715884105727"}"#,
    );
}

#[test]
fn float_bits_survive_value_writer_and_messagepack_routes() {
    for bits in [
        0,
        1u64 << 63,
        1,
        1.5f64.to_bits(),
        f64::MAX.to_bits(),
        f64::INFINITY.to_bits(),
        f64::NEG_INFINITY.to_bits(),
        0x7ff8_0000_1234_5678,
        0xfff0_0000_0000_0001,
    ] {
        let constant = Constant::Float(f64::from_bits(bits));
        assert_eq!(
            serde_json::to_string(&constant).unwrap(),
            format!("{{\"Float\":{{\"bits\":{bits}}}}}"),
        );
        let value = scalar_roundtrip(&constant);
        assert_eq!(value["Float"]["bits"].as_u64(), Some(bits));
        let bundle = constant_content(Ty::F64, constant);
        check_public_payload(&bundle, &native_bundle_transport_payload(&bundle).unwrap());
        // AttrValue derives float equality: inspect bits instead of NaN == NaN.
        let attribute = AttrValue::F64(f64::from_bits(bits));
        let writer = serde_json::to_vec(&attribute).unwrap();
        assert_eq!(
            writer.as_slice(),
            format!("{{\"F64\":{{\"bits\":{bits}}}}}").as_bytes()
        );
        let value = serde_json::to_value(&attribute).unwrap();
        let compact = rmp_serde::to_vec(&attribute).unwrap();
        for actual in [
            serde_json::from_value::<AttrValue>(value).unwrap(),
            serde_json::from_slice::<AttrValue>(&writer).unwrap(),
            rmp_serde::from_slice::<AttrValue>(&compact).unwrap(),
        ] {
            let AttrValue::F64(number) = actual else {
                panic!("float attribute tag changed")
            };
            assert_eq!(number.to_bits(), bits);
        }
    }
}
