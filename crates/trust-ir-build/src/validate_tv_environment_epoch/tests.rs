// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Diagnose the actual historical environment input; never accept a proof in
//! the diagnostic clone or change the production anchor/axiom policy.

use clean_kernel::{Declaration, Name};
use trust_ir::Module;
use trust_ir::proof::{CertificateBinding, ProofEvidence, kernel_environment_digest};

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

    let fresh_binding = binding(&fresh);
    let stale_binding = binding(&stale);
    assert!(fresh_binding.environment.is_none());
    assert!(stale_binding.environment.is_none());
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

    // Historical hash-only control. This clone is never passed to a proof
    // checker, module validator or certificate producer.
    let mut diagnostic = current.clone();
    assert!(diagnostic.forget_decl(&name));
    assert_eq!(
        kernel_environment_digest(&diagnostic).unwrap(),
        stale_binding.environment_digest
    );
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
