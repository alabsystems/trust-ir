// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Diagnose the actual historical environment input; never accept a proof in
//! the diagnostic clone or change the production anchor/axiom policy.

use clean_kernel::{Declaration, Name};
use trust_ir::Module;
use trust_ir::proof::{CertificateBinding, ProofDigest, ProofEvidence, kernel_environment_digest};

fn binding(module: &Module) -> &CertificateBinding {
    let [certificate] = module.proof_certificates.as_slice() else {
        panic!("one complete producer certificate");
    };
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(recheck),
        ..
    } = &certificate.evidence
    else {
        panic!("complete CleanCic directive");
    };
    recheck
        .binding
        .as_deref()
        .expect("complete producer binding")
}

#[test]
fn actual_prelude_marker_is_the_entire_preserved_environment_binding_difference() {
    macro_rules! data {
        ($file:literal) => {
            include_bytes!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/source_value_equations/boundActualEquation/",
                $file
            ))
        };
    }
    let fresh = trust_ir::binary::deserialize_module(data!("module.bin")).unwrap();
    let stale =
        trust_ir::binary::deserialize_module(data!("module.stale-environment.bin")).unwrap();
    let preserved_clean550 = trust_ir::binary::deserialize_module(include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/source_value_equations/stale-clean550/boundActualEquation/module.bin"
    )))
    .unwrap();
    let config = super::ValidationConfig::pinned().with_bound_certificates(true);
    let checked = super::validate_module_with_config(&fresh, &config);
    assert!(checked.errors.is_empty(), "{:?}", checked.errors);
    let rejected = super::validate_module_with_config(&stale, &config);
    assert!(
        matches!(rejected.errors.as_slice(),
        [super::ValidationError::CertificateBindingMismatch { obligation: 0, field, .. }]
            if field == "environment_digest"),
        "{:?}",
        rejected.errors
    );
    let historical_rejected = super::validate_module_with_config(&preserved_clean550, &config);
    assert!(
        matches!(historical_rejected.errors.as_slice(),
        [super::ValidationError::CertificateBindingMismatch { obligation: 0, field, .. }]
            if field == "environment_digest"),
        "{:?}",
        historical_rejected.errors
    );

    let fresh_binding = binding(&fresh);
    let stale_binding = binding(&stale);
    assert!(fresh_binding.environment.is_none());
    assert!(stale_binding.environment.is_none());
    let historical_binding = binding(&preserved_clean550);
    assert!(historical_binding.environment.is_none());
    assert_ne!(
        historical_binding.environment_digest,
        fresh_binding.environment_digest
    );
    let current = super::clean_backend_tv::anchor_environment().unwrap();
    let current_digest = kernel_environment_digest(&current).unwrap();
    assert_eq!(current_digest, fresh_binding.environment_digest);
    let name = Name::from_string("semiOutParam");
    let marker = current
        .get_const(&name)
        .expect("actual new checked prelude declaration")
        .clone();
    assert!(marker.is_reducible);
    assert!(marker.value.is_some());

    // Keep the historical test identity and every preserved producer byte.
    // The old single-marker explanation was qualified with Clean550; the
    // current Clean7722 fixture has later environment changes as well. Bind
    // the actually measured current marker-removal identity explicitly, not
    // an invented equivalence with either historical environment. This clone
    // is never passed to a proof checker, validator or certificate producer.
    let mut diagnostic = current.clone();
    assert!(diagnostic.forget_decl(&name));
    let without_marker = kernel_environment_digest(&diagnostic).unwrap();
    assert_eq!(
        without_marker,
        ProofDigest::sha256([
            1, 176, 84, 201, 38, 35, 246, 21, 15, 167, 204, 221, 22, 60, 169, 95, 224, 198, 159,
            149, 1, 22, 103, 237, 2, 114, 173, 204, 8, 1, 59, 118,
        ]),
        "exact Clean7722 current environment with only semiOutParam removed"
    );
    assert_ne!(without_marker, current_digest);
    assert_ne!(without_marker, stale_binding.environment_digest);
    diagnostic
        .add_decl(Declaration::Definition {
            name: marker.name.clone(),
            level_params: marker.level_params.clone(),
            type_: marker.type_.clone(),
            value: marker.value.clone().unwrap(),
            is_reducible: marker.is_reducible,
        })
        .expect("restore the exact declaration through checked kernel admission");
    assert_eq!(diagnostic.get_const(&name), Some(&marker));
    assert_eq!(
        kernel_environment_digest(&diagnostic).unwrap(),
        current_digest
    );
    assert_eq!(current.get_const(&name), Some(&marker));
    assert_eq!(kernel_environment_digest(&current).unwrap(), current_digest);
    let checked_again = super::validate_module_with_config(&fresh, &config);
    assert!(
        checked_again.errors.is_empty(),
        "{:?}",
        checked_again.errors
    );
}
