// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A required proof transport codec grants no optional TV anchor authority.
#![cfg(not(feature = "clean-tv-anchor"))]

use trust_ir::Ty;
use trust_ir::proof::{ProofLineageId, ProofTransform, ProofTransformStage};
use trust_ir::value::ProofId;
use trust_ir_build::ModuleBuilder;

#[test]
fn scoped_codec_does_not_enable_the_disabled_tv_anchor() {
    let mut builder = ModuleBuilder::new("codec-without-tv-anchor");
    let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut function = builder.function("identity", signature);
    let entry = function.create_block();
    let value = function.add_block_param(entry, Ty::U64);
    function.switch_to_block(entry);
    function.ret(vec![value]);
    function.build();
    let module = builder.build().expect("honest identity module");
    let identity = module.functions[0].id;
    let error = trust_ir_build::validate::certify_identity_lineage_rung(
        &module,
        ProofLineageId::new(0),
        ProofId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "identity",
            "feature-test",
            "1",
        ),
        identity,
    )
    .expect_err("a codec must not enable translation-validation certification");
    assert_eq!(
        error,
        "identity lineage certification requires the clean-tv-anchor feature"
    );
}

#[test]
fn source_call_family_does_not_enable_disabled_tv_anchor() {
    use trust_ir::FuncId;
    use trust_ir::proof::{IslandEnvironment, ProofDigest, SourceDefinitionRef};
    let module = ModuleBuilder::new("source-calls-without-feature")
        .build()
        .unwrap();
    let error = trust_ir_build::certify_source_bound_call_family(
        &module,
        ProofLineageId::new(0),
        ProofId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "source-calls",
            "feature-test",
            "1",
        ),
        &IslandEnvironment::new(vec![]),
        &[(
            FuncId::new(0),
            SourceDefinitionRef {
                decl: "missing".into(),
                closure_digest: ProofDigest::zero(),
            },
        )],
    )
    .expect_err("no disabled-feature producer authority");
    assert!(error.contains("requires the clean-tv-anchor feature"));
}
