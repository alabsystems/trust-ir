// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Kernel-backed lineage authority tests: exact semantic endpoint binding,
//! transform binding, and fail-closed rejection of unrelated proofs.

use trust_ir::Module;
use trust_ir::proof::{
    ObligationKind, ProofDigest, ProofFormula, ProofLineageId, ProofLineageManifest,
    ProofLineageNode, ProofObligation, ProofStatus, ProofTransform, ProofTransformStage,
    clean_cic_lineage_digest,
};
use trust_ir::ty::Ty;
use trust_ir::value::ProofId;
use trust_ir_build::{
    ModuleBuilder, certify_identity_lineage_rung, lineage_closed_with_validated_authority,
    validate_module,
};

fn identity_module() -> Module {
    let mut builder = ModuleBuilder::new("lineage_identity");
    let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut function = builder.function("identity", signature);
    let entry = function.create_block();
    let value = function.add_block_param(entry, Ty::U64);
    function.switch_to_block(entry);
    function.ret(vec![value]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

fn kernel_identity_fixture() -> (Module, ProofLineageManifest) {
    let mut module = identity_module();
    let (node, obligation, certificate) = certify_identity_lineage_rung(
        &module,
        ProofLineageId::new(0),
        ProofId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "identity",
            "trust-ir-build-test",
            "1.0.0",
        ),
        module.functions[0].id,
    )
    .expect("identity function is in the backend-TV fragment");
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    let manifest = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        roots: vec![node.id],
        nodes: vec![node],
    };
    (module, manifest)
}

#[test]
fn kernel_replayed_identity_lineage_closes() {
    let (module, manifest) = kernel_identity_fixture();
    assert!(validate_module(&module).is_empty());
    assert_eq!(
        lineage_closed_with_validated_authority(&module, &manifest),
        Ok(())
    );
}

#[test]
fn forged_endpoint_fails_after_rebinding_public_identity_fields() {
    let (mut module, mut manifest) = kernel_identity_fixture();

    // An attacker can recompute the public obligation-lineage hash after
    // editing a node. Exercise that strongest forgery, not merely a stale-ref
    // typo: update the formula, certificate lineage, and node cert reference.
    // The independent semantic rederivation must still catch the forged edge.
    manifest.nodes[0].source_module =
        ProofDigest::sha256_domain("trust-ir.test.forged-lineage-source", b"forged");
    let rebound_formula = manifest.nodes[0].transform_binding_formula();
    module.proof_obligations[0].formula = Some(rebound_formula);
    let rebound_lineage = clean_cic_lineage_digest(&module.proof_obligations[0]);
    let trust_ir::ProofEvidence::CleanCic { lineage, .. } =
        &mut module.proof_certificates[0].evidence
    else {
        panic!("identity fixture carries CleanCic evidence");
    };
    *lineage = rebound_lineage;
    manifest.nodes[0].certificates[0] = module.proof_certificates[0].lineage_ref();

    // The certificate still proves the function equation and is correctly
    // rebound as table data; only node-aware semantic endpoint checking can
    // distinguish the forged source digest.
    assert!(validate_module(&module).is_empty());
    let error = lineage_closed_with_validated_authority(&module, &manifest)
        .expect_err("forged semantic endpoint must fail closed");
    assert!(
        error
            .to_string()
            .contains("source semantics digest mismatch"),
        "unexpected error: {error}"
    );
}

#[test]
fn unrelated_certified_contract_cannot_authorize_lineage() {
    let mut module = identity_module();
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "a true but unrelated contract",
    )
    .with_formula(ProofFormula::smtlib2("(= 1 1)", "Bool"));
    let certificate = trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate(
        &obligation,
        "contract-prover",
    )
    .expect("the unrelated contract itself is genuinely kernel-provable");
    let mut node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "forged-from-contract",
            "attacker",
            "1",
        ),
        ProofDigest::sha256_domain("trust-ir.test.contract-source", b"source"),
        ProofDigest::sha256_domain("trust-ir.test.contract-target", b"target"),
    );
    node.obligations.push(obligation.id);
    node.certificates.push(certificate.lineage_ref());
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    let manifest = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        roots: vec![node.id],
        nodes: vec![node],
    };

    let error = lineage_closed_with_validated_authority(&module, &manifest)
        .expect_err("a contract proof is not translation authority");
    assert!(
        error.to_string().contains("not TranslationValidation"),
        "unexpected error: {error}"
    );
}
