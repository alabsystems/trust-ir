// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// KIND 1 — the v41 producer conformance rule, made checkable.
//
// `BodyGate`'s doc used to say the rule ("a v41 producer MUST emit `Ungated`
// or `Gated`; wire tag 0 is legitimate only as re-emission of pre-v41
// content") was "not format-enforceable — a decoded Module does not retain
// the wire version it came from". That was an implementation fact, not a
// law: `deserialize_module_with_wire_version` keeps the header version beside
// the module as a `WireVersion` only the decoder can mint, and
// `validate_module_as_decoded` reads the rule against it. These tests pin
// exactly the prose, negative first:
//
//   * a v41 blob whose bodied function makes no `body_gate` claim is REFUSED,
//     by name (`ProducerOmittedBodyGate`), naming the declared version;
//   * the same content in a pre-v41 blob — v38, and v40, the last version
//     before the tag existed — is ACCEPTED: `None` is the grandfather state;
//   * a bodyless declaration with no claim at v41 is ACCEPTED;
//   * plain `validate_module` accepts every one of them — a module in hand
//     has no wire version, so the rule has nothing to read there. That
//     residual is the one the types state, and the codegen pass's refusal of
//     the same body is a DIFFERENT variant under every provenance;
//   * a faithful re-emission of pre-v41 content KEEPS its pre-v41 header
//     (the writer selects the minimum lossless version), so the exception
//     the rule used to state in prose — "tag 0 is legitimate as re-emission
//     of pre-v41 content" — is a property of the writer, not a case the
//     check has to (or could) recognise; the same content reaches v41+ only
//     by gaining a v41+ feature, and is then refused.
//
// "Same bytes relabelled v40" cannot be spelled at the byte level: the v41
// function record carries bytes a v40 reader never consumes, so a relabelled
// blob does not decode (`a_v41_blob_relabelled_v40_does_not_decode`). The
// grandfather case is therefore the same CONTENT written with a genuine v40
// header.
//
// FEATURES. `binary`-gated whole: without the codec nothing mints a
// `WireVersion`. Runs under `--workspace --all-features` (feature
// unification, `scripts/ci-self-verify.sh`) and wherever
// `trust-ir-build/binary` is on — which NO standing `scripts/ci_gates.sh`
// gate is: the gate-9 registry lane is featureless and would compile this
// file to an empty target. The standing-gate coverage of every case here is
// the CLI twin (`trust-ir-cli/tests/cli_decoded_provenance.rs`, gate 3),
// which pins the v38, v40 and v41 boundaries, the declaration cut, the
// re-emission property and the non-binary UNCHECKED line.

#![cfg(feature = "binary")]

use trust_ir::binary::{
    BASE_FORMAT_VERSION, CONTAINER_VTABLE_FORMAT_VERSION, CONTRACT_SURFACE_FORMAT_VERSION,
    WireVersion, deserialize_module_with_wire_version, serialize_module,
};
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::{FatPtrKind, FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId};
use trust_ir::{Block, BodyGate, CallingConv, Function, Linkage, Module};
use trust_ir_build::validate::{
    ValidationError, decoded_provenance_errors, validate_module, validate_module_as_decoded,
    validate_module_for_codegen,
};

fn ret_block() -> Block {
    let mut block = Block::new(BlockId::new(0));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    block
}

/// One nullary function `f` with NO `body_gate` claim: bodied unless
/// `declaration`. `at_v41` adds a `display_path` — a genuine v41 feature, so
/// the writer selects exactly v41 — without touching the license.
fn module(name: &str, declaration: bool, at_v41: bool) -> Module {
    let mut module = Module::new(name);
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", signature, BlockId::new(0));
    f.linkage = Linkage::External;
    f.calling_conv = CallingConv::Rust;
    f.body_gate = None;
    if !declaration {
        f.blocks.push(ret_block());
    }
    if at_v41 {
        f.display_path = Some("crate::f".into());
    }
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    module
}

fn decode(module: &Module) -> (Module, WireVersion) {
    deserialize_module_with_wire_version(
        &serialize_module(module).expect("serialize_module: test fixture"),
    )
    .expect("round-trip decodes")
}

#[test]
fn a_v41_blob_with_a_bodied_unlicensed_function_is_refused_by_name() {
    let (decoded, wire_version) = decode(&module("v41_bodied_none", false, true));
    assert_eq!(wire_version.get(), CONTRACT_SURFACE_FORMAT_VERSION);
    assert!(wire_version.claims_contract_surface());
    assert_eq!(decoded.functions[0].body_gate, None);
    assert!(!decoded.functions[0].is_declaration());

    let errors = validate_module_as_decoded(&decoded, wire_version);
    assert_eq!(
        errors,
        vec![ValidationError::ProducerOmittedBodyGate {
            function: 0,
            name: "f".into(),
            wire_version: CONTRACT_SURFACE_FORMAT_VERSION,
        }]
    );
    // The layer alone agrees, and the structural pass contributed nothing:
    // the refusal is the provenance rule's and nobody else's.
    assert_eq!(decoded_provenance_errors(&decoded, wire_version), errors);
    assert_eq!(validate_module(&decoded), Vec::new());
    let text = errors[0].to_string();
    assert!(
        text.contains("v41 blob") && text.contains("wire tag 0") && text.contains("\"f\""),
        "the refusal names the version, the tag and the function: {text}"
    );
}

#[test]
fn the_same_content_in_a_v38_blob_is_grandfathered() {
    let (decoded, wire_version) = decode(&module("v38_bodied_none", false, false));
    assert_eq!(wire_version.get(), BASE_FORMAT_VERSION);
    assert!(!wire_version.claims_contract_surface());
    assert_eq!(decoded.functions[0].body_gate, None);
    assert_eq!(
        validate_module_as_decoded(&decoded, wire_version),
        Vec::new()
    );
    assert_eq!(
        decoded_provenance_errors(&decoded, wire_version),
        Vec::new()
    );
}

#[test]
fn the_same_content_in_a_v40_blob_is_grandfathered() {
    // v40 is the last version before the tag existed. The same bodied
    // unlicensed function beside a `ContainerVtable` fat pointer, which is
    // what raises the header to exactly 40 and nothing higher.
    let mut with_v40_feature = module("v40_bodied_none", false, false);
    with_v40_feature
        .add_func_type(FuncTy {
            params: vec![Ty::FatPtr(FatPtrKind::ContainerVtable)],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let (decoded, wire_version) = decode(&with_v40_feature);
    assert_eq!(wire_version.get(), CONTAINER_VTABLE_FORMAT_VERSION);
    assert!(!wire_version.claims_contract_surface());
    assert_eq!(decoded.functions[0].body_gate, None);
    assert_eq!(
        validate_module_as_decoded(&decoded, wire_version),
        Vec::new()
    );
}

#[test]
fn a_v41_blob_relabelled_v40_does_not_decode() {
    // Why the grandfather tests above re-write the CONTENT at a lower version
    // instead of patching the header: a v41 function record carries the
    // `body_gate` tag and the `display_path` slot, which a v40 reader never
    // consumes, so the relabelled bytes are not a v40 blob at all.
    let mut bytes = serialize_module(&module("v41_bodied_none", false, true))
        .expect("serialize_module: test fixture");
    assert_eq!(
        &bytes[8..12],
        &CONTRACT_SURFACE_FORMAT_VERSION.to_le_bytes()
    );
    bytes[8..12].copy_from_slice(&CONTAINER_VTABLE_FORMAT_VERSION.to_le_bytes());
    assert!(deserialize_module_with_wire_version(&bytes).is_err());
}

#[test]
fn a_bodyless_declaration_needs_no_claim_at_v41() {
    let (decoded, wire_version) = decode(&module("v41_declaration_none", true, true));
    assert_eq!(wire_version.get(), CONTRACT_SURFACE_FORMAT_VERSION);
    assert!(decoded.functions[0].is_declaration());
    assert_eq!(decoded.functions[0].body_gate, None);
    assert_eq!(
        validate_module_as_decoded(&decoded, wire_version),
        Vec::new()
    );
}

#[test]
fn an_affirmative_claim_at_v41_satisfies_the_producer_rule() {
    // `Ungated` IS a claim: the producer rule is met. Whether codegen may
    // consume the body is `validate_module_for_codegen`'s separate refusal,
    // under a separate variant, and that one still fires.
    let mut ungated = module("v41_bodied_ungated", false, false);
    ungated.functions[0].body_gate = Some(BodyGate::Ungated);
    let (decoded, wire_version) = decode(&ungated);
    assert_eq!(wire_version.get(), CONTRACT_SURFACE_FORMAT_VERSION);
    assert_eq!(
        validate_module_as_decoded(&decoded, wire_version),
        Vec::new()
    );
    assert!(
        validate_module_for_codegen(&decoded)
            .iter()
            .any(|e| matches!(e, ValidationError::UngatedBodyForCodegen { .. }))
    );
}

#[test]
fn plain_validate_module_reads_no_provenance() {
    // The residual, stated: a module in hand carries no wire version, so the
    // plain pass accepts every shape above, before AND after a binary
    // round-trip — a caller that decoded through the plain entry point holds
    // exactly such a module.
    for (name, declaration, at_v41) in [
        ("v41_bodied_none", false, true),
        ("v38_bodied_none", false, false),
        ("v41_declaration_none", true, true),
    ] {
        let built = module(name, declaration, at_v41);
        assert_eq!(validate_module(&built), Vec::new(), "{name}");
        let (decoded, _wire_version) = decode(&built);
        assert_eq!(
            validate_module(&decoded),
            Vec::new(),
            "{name} after round-trip"
        );
    }
    // And the codegen pass refuses the bodied `None` under EVERY provenance
    // as the CONSUMER-side variant, never as the producer-side one.
    let codegen = validate_module_for_codegen(&module("v41_bodied_none", false, true));
    assert!(
        codegen
            .iter()
            .any(|e| matches!(e, ValidationError::UnlicensedBodyForCodegen { .. }))
    );
    assert!(
        !codegen
            .iter()
            .any(|e| matches!(e, ValidationError::ProducerOmittedBodyGate { .. }))
    );
}

#[test]
fn a_faithful_re_emission_of_pre_v41_content_keeps_its_header() {
    // The retired prose exception, as a property of the writer: a decoded
    // pre-v41 module re-serializes at the SAME pre-v41 version (minimum
    // lossless selection), byte-identically, so the re-emission is
    // grandfathered exactly as the original was — at both boundaries.
    for (name, raise_to_v40) in [("v38_bodied_none", false), ("v40_bodied_none", true)] {
        let mut built = module(name, false, false);
        if raise_to_v40 {
            built
                .add_func_type(FuncTy {
                    params: vec![Ty::FatPtr(FatPtrKind::ContainerVtable)],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
        }
        let original = serialize_module(&built).expect("serialize_module: test fixture");
        let (decoded, wire_version) =
            deserialize_module_with_wire_version(&original).expect("the original decodes");
        assert_eq!(
            wire_version.get(),
            if raise_to_v40 {
                CONTAINER_VTABLE_FORMAT_VERSION
            } else {
                BASE_FORMAT_VERSION
            },
            "{name}"
        );
        let re_emitted = serialize_module(&decoded).expect("serialize_module: test fixture");
        assert_eq!(
            re_emitted, original,
            "{name}: the re-emission is byte-identical, header included"
        );
        let (again, re_emitted_version) =
            deserialize_module_with_wire_version(&re_emitted).expect("the re-emission decodes");
        assert_eq!(re_emitted_version.get(), wire_version.get(), "{name}");
        assert!(!re_emitted_version.claims_contract_surface(), "{name}");
        assert_eq!(
            validate_module_as_decoded(&again, re_emitted_version),
            Vec::new(),
            "{name}: the re-emission is grandfathered like the original"
        );
    }

    // The ONLY way the same content reaches v41+ is a v41+ feature — and
    // whoever adds one is the v41+ producer of that module, held to the rule.
    let (mut with_feature, _) = deserialize_module_with_wire_version(
        &serialize_module(&module("v38_bodied_none", false, false))
            .expect("serialize_module: test fixture"),
    )
    .expect("decodes");
    with_feature.functions[0].display_path = Some("crate::f".into());
    let (decoded, wire_version) = deserialize_module_with_wire_version(
        &serialize_module(&with_feature).expect("serialize_module: test fixture"),
    )
    .expect("decodes");
    assert_eq!(wire_version.get(), CONTRACT_SURFACE_FORMAT_VERSION);
    assert!(matches!(
        validate_module_as_decoded(&decoded, wire_version).as_slice(),
        [ValidationError::ProducerOmittedBodyGate {
            function: 0,
            wire_version: 41,
            ..
        }]
    ));
}
