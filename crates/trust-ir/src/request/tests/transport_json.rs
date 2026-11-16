// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native JSON transport preserves content; it does not establish admission.

use super::*;
use crate::request::transport::{
    NATIVE_BUNDLE_REPLAY_FORMULA_REF_ENCODING, native_bundle_transport_payload,
    rehydrate_native_bundle_transport_payload,
};
use crate::{EnumDef, EnumTagRepr, EnumVariant};
use serde_json::{Value, json};

fn transport_bundle() -> NativeVerificationBundle {
    let mut bundle = native_bundle();
    for request in &mut bundle.requests {
        let (obligation, provenance) = match request {
            NativeVerificationRequest::TrustVc(request) => {
                (request.obligations[0], &mut request.provenance)
            }
            NativeVerificationRequest::TrustMc(request) => {
                (request.obligations[0], &mut request.provenance)
            }
            NativeVerificationRequest::TrustWp(request) => {
                (request.obligations[0], &mut request.provenance)
            }
        };
        let formula = bundle
            .module
            .proof_obligations
            .iter()
            .find(|entry| entry.id == obligation)
            .unwrap()
            .formula
            .clone()
            .unwrap();
        provenance.replay_context = NativeReplayContext::default()
            .with_atom(
                NativeReplayAtom::assertion(NativeReplayAtomId::new(0), formula)
                    .with_obligation(obligation),
            )
            .with_atom(
                NativeReplayAtom::assertion(
                    NativeReplayAtomId::new(1),
                    ProofFormula::smtlib2("different replay formula", "Bool"),
                )
                .with_obligation(obligation),
            )
            .with_atom(NativeReplayAtom::assumption(
                NativeReplayAtomId::new(2),
                ProofFormula::smtlib2("unbound assumption", "Bool"),
            ));
    }
    bundle
}

fn atoms(payload: &Value) -> Vec<&Value> {
    payload["bundle"]["requests"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|request| request.as_object().unwrap().values())
        .flat_map(|request| {
            request["provenance"]["replay_context"]["atoms"]
                .as_array()
                .unwrap()
        })
        .collect()
}

fn referenced_atom_mut(payload: &mut Value) -> &mut Value {
    payload["bundle"]["requests"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .flat_map(|request| request.as_object_mut().unwrap().values_mut())
        .flat_map(|request| {
            request["provenance"]["replay_context"]["atoms"]
                .as_array_mut()
                .unwrap()
        })
        .find(|atom| atom.get("formula_ref").is_some())
        .unwrap()
}

fn assert_refused(payload: &Value, expected: &str) {
    let error = rehydrate_native_bundle_transport_payload(payload).unwrap_err();
    assert!(error.contains(expected), "{expected:?} not in {error:?}");
}

#[test]
fn native_transport_roundtrip_references_only_equal_bound_formulas_in_every_suite() {
    let bundle = transport_bundle();
    let before = bundle.clone();
    let payload = native_bundle_transport_payload(&bundle).unwrap();
    assert_eq!(
        payload["encoding"],
        NATIVE_BUNDLE_REPLAY_FORMULA_REF_ENCODING
    );
    assert_eq!(payload.as_object().unwrap().len(), 2);
    let atoms = atoms(&payload);
    assert_eq!(atoms.len(), 9, "all three request suites are exercised");
    for request_atoms in atoms.as_chunks::<3>().0 {
        assert_eq!(
            request_atoms[0]["formula_ref"]["obligation"],
            request_atoms[0]["obligation"],
        );
        assert!(request_atoms[0].get("formula").is_none());
        assert!(request_atoms[1].get("formula").is_some());
        assert!(request_atoms[1].get("formula_ref").is_none());
        assert!(request_atoms[2].get("formula").is_some());
        assert!(request_atoms[2].get("formula_ref").is_none());
    }
    let wire = serde_json::to_vec(&payload).unwrap();
    let payload = serde_json::from_slice(&wire).unwrap();
    let restored = rehydrate_native_bundle_transport_payload(&payload).unwrap();
    assert_eq!(restored, bundle);
    assert_eq!(restored.stable_digest(), bundle.stable_digest());
    assert_eq!(bundle, before, "encoding leaves the input unchanged");
}

#[test]
fn native_transport_rejects_malformed_and_extended_envelopes() {
    let payload = native_bundle_transport_payload(&transport_bundle()).unwrap();
    for malformed in [Value::Null, json!([]), json!("bundle")] {
        assert_refused(&malformed, "not an object");
    }
    assert_refused(&payload["bundle"], "encoding");
    let mut wrong_encoding = payload.clone();
    wrong_encoding["encoding"] = json!("trust.native-bundle.replay-formula-ref.v0");
    assert_refused(&wrong_encoding, "encoding");
    let mut extra = payload.clone();
    extra["extra"] = json!(true);
    assert_refused(&extra, "encoding");
    let mut missing = payload.clone();
    missing.as_object_mut().unwrap().remove("bundle");
    assert_refused(&missing, "encoding");
    let mut wrong_bundle = payload;
    wrong_bundle["bundle"] = json!([]);
    assert_refused(&wrong_bundle, "does not decode");
}

#[test]
fn native_transport_rejects_malformed_mismatched_and_dangling_references() {
    let payload = native_bundle_transport_payload(&transport_bundle()).unwrap();
    for reference in [
        Value::Null,
        json!(0),
        json!({}),
        json!({"obligation": "0"}),
        json!({"obligation": -1}),
        json!({"obligation": 0, "extra": true}),
    ] {
        let mut malformed = payload.clone();
        referenced_atom_mut(&mut malformed)["formula_ref"] = reference;
        assert_refused(&malformed, "is not `{\"obligation\": <id>}`");
    }
    let mut mismatched = payload.clone();
    referenced_atom_mut(&mut mismatched)["formula_ref"]["obligation"] = json!(1);
    assert_refused(&mismatched, "not the atom's own obligation");
    let mut dangling = payload.clone();
    let atom = referenced_atom_mut(&mut dangling);
    atom["obligation"] = json!(99);
    atom["formula_ref"]["obligation"] = json!(99);
    assert_refused(&dangling, "absent obligation 99");
    let mut both = payload;
    referenced_atom_mut(&mut both)["formula"] = json!({"schema": "x", "payload": "y"});
    assert_refused(&both, "both an inline formula and a formula reference");
}

#[test]
fn native_transport_rejects_ambiguous_obligation_formulas() {
    for (first_has_formula, second_has_formula) in [(true, true), (true, false), (false, true)] {
        let mut bundle = transport_bundle();
        let mut repeated = bundle.module.proof_obligations[0].clone();
        if !first_has_formula {
            bundle.module.proof_obligations[0].formula = None;
        }
        if !second_has_formula {
            repeated.formula = None;
        }
        bundle.module.proof_obligations.push(repeated);
        let payload = native_bundle_transport_payload(&bundle).unwrap();
        assert!(
            atoms(&payload)
                .iter()
                .all(|atom| atom.get("formula_ref").is_none())
        );
        assert_refused(&payload, "obligation id 0 is repeated");
    }
}

#[test]
fn native_transport_checks_restored_formula_and_payload_digest() {
    let payload = native_bundle_transport_payload(&transport_bundle()).unwrap();
    let mut changed_formula = payload.clone();
    changed_formula["bundle"]["module"]["proof_obligations"][0]["formula"]["smtlib"] =
        json!("tampered formula");
    assert_refused(
        &changed_formula,
        "does not reproduce its recorded payload digest",
    );
    let mut changed_digest = payload;
    referenced_atom_mut(&mut changed_digest)["payload_digest"] =
        serde_json::to_value(digest(0xEE)).unwrap();
    assert_refused(
        &changed_digest,
        "does not reproduce its recorded payload digest",
    );
}

#[test]
fn native_transport_rejects_unknown_fields_and_default_erasure() {
    let payload = native_bundle_transport_payload(&transport_bundle()).unwrap();
    let mut extra_bundle = payload.clone();
    extra_bundle["bundle"]["unknown_identity"] = json!(true);
    assert_refused(&extra_bundle, "loses fields during typed decoding");
    let mut extra_atom = payload.clone();
    referenced_atom_mut(&mut extra_atom)["unknown_identity"] = json!(true);
    assert_refused(&extra_atom, "loses fields during typed decoding");
    let mut omitted_default = payload;
    omitted_default["bundle"]
        .as_object_mut()
        .unwrap()
        .remove("diagnostics");
    assert_refused(&omitted_default, "loses fields during typed decoding");
}

#[test]
fn native_transport_wide_numeric_fields_remain_numbers_and_roundtrip_exactly() {
    for number in [
        i128::MIN,
        i64::MIN as i128 - 1,
        i64::MIN as i128,
        0,
        u64::MAX as i128,
        u64::MAX as i128 + 1,
        i128::MAX,
    ] {
        let mut bundle = transport_bundle();
        bundle.module.add_enum(
            EnumDef::new(
                EnumId::new(0),
                "WideTransport",
                vec![EnumVariant {
                    name: "Value".into(),
                    fields: vec![],
                    field_names: vec![],
                }],
            )
            .with_discriminants(vec![Some(number)])
            .with_repr(EnumTagRepr::I128),
        );
        add_native_direct_enum_fact(&mut bundle);
        bundle.compiler_facts.adt_layouts[0]
            .enum_layout
            .as_mut()
            .unwrap()
            .variants[0]
            .discriminant = Some(number);
        add_pointer_offset_ir(&mut bundle);
        let mut fact = pointer_offset_fact(&bundle);
        fact.signed_offset_const = Some(number);
        bundle.compiler_facts.pointer_offsets.push(fact);
        refresh_native_bundle_module_identity(&mut bundle);
        let payload = native_bundle_transport_payload(&bundle).unwrap();
        for value in [
            &payload["bundle"]["module"]["enums"][0]["discriminants"][0],
            &payload["bundle"]["compiler_facts"]["adt_layouts"][0]["enum_layout"]["variants"][0]["discriminant"],
            &payload["bundle"]["compiler_facts"]["pointer_offsets"][0]["signed_offset_const"],
        ] {
            assert!(value.is_number());
            assert_eq!(value.to_string(), number.to_string());
        }
        let wire = serde_json::to_vec(&payload).unwrap();
        let payload = serde_json::from_slice(&wire).unwrap();
        let restored = rehydrate_native_bundle_transport_payload(&payload).unwrap();
        assert_eq!(restored, bundle);
        assert_eq!(restored.stable_digest(), bundle.stable_digest());
    }
}

#[test]
fn native_transport_preserves_existing_wide_constant_adapter_spelling() {
    let mut bundle = transport_bundle();
    bundle.module.functions[0].blocks[0].body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U128,
            value: Constant::U128(u128::MAX),
        })
        .with_result(ValueId::new(21)),
    );
    refresh_native_bundle_module_identity(&mut bundle);
    let payload = native_bundle_transport_payload(&bundle).unwrap();
    assert_eq!(
        payload["bundle"]["module"]["functions"][0]["blocks"][0]["body"][0]["inst"]["Const"]["value"]
            ["U128"],
        json!(u128::MAX.to_string()),
    );
    let wire = serde_json::to_vec(&payload).unwrap();
    let payload = serde_json::from_slice(&wire).unwrap();
    let restored = rehydrate_native_bundle_transport_payload(&payload).unwrap();
    assert_eq!(restored, bundle);
    assert_eq!(restored.stable_digest(), bundle.stable_digest());
}

#[test]
fn native_transport_deduplication_reduces_bytes_without_changing_content() {
    let mut bundle = transport_bundle();
    let formula = ProofFormula::smtlib2("x".repeat(32 * 1024), "Bool");
    bundle.module.proof_obligations[0].formula = Some(formula.clone());
    for request in &mut bundle.requests {
        let provenance = match request {
            NativeVerificationRequest::TrustVc(request) => &mut request.provenance,
            NativeVerificationRequest::TrustMc(request) => &mut request.provenance,
            NativeVerificationRequest::TrustWp(request) => &mut request.provenance,
        };
        for atom in &mut provenance.replay_context.atoms {
            if atom.id == NativeReplayAtomId::new(0) && atom.obligation == Some(ProofId::new(0)) {
                atom.formula = formula.clone();
                atom.payload_digest = atom.expected_payload_digest();
            }
        }
    }
    refresh_native_bundle_module_identity(&mut bundle);
    let plain = serde_json::to_vec(&bundle).unwrap();
    let payload = native_bundle_transport_payload(&bundle).unwrap();
    assert!(serde_json::to_vec(&payload).unwrap().len() < plain.len());
    assert_eq!(
        rehydrate_native_bundle_transport_payload(&payload).unwrap(),
        bundle
    );
}

#[test]
fn native_transport_does_not_validate_or_restore_live_source_authority() {
    let mut bundle = source_generation_authority_bundle();
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    assert!(authority.authorizes_bundle(&bundle));
    let payload = native_bundle_transport_payload(&bundle).unwrap();
    let decoded = rehydrate_native_bundle_transport_payload(&payload).unwrap();
    assert_eq!(decoded, bundle);
    decoded.validate().unwrap();
    assert!(!authority.authorizes_bundle(&decoded));

    bundle.schema_version = 0;
    let payload = native_bundle_transport_payload(&bundle).unwrap();
    let decoded = rehydrate_native_bundle_transport_payload(&payload).unwrap();
    assert_eq!(
        decoded, bundle,
        "content decoding is separate from admission"
    );
    assert!(decoded.validate().is_err());
}
