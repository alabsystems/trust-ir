// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir spec-link` — the spec↔source
//! cross-reference pass. These are the "teeth" tests: a passing fixture must
//! exit 0, and each negative fixture must exit 1 *and* name the exact
//! obligation it violates.

mod common;

use std::fs;

use tempfile::tempdir;

use common::{
    build_spec_fail_l1_module, build_spec_fail_l2_module, build_spec_fail_l3_module,
    build_spec_fail_ob1_module, build_spec_fail_ob3_module, build_spec_fail_ob4_module,
    build_spec_fail_typed_anchor_mismatched_symbol, build_spec_fail_typed_anchor_missing_function,
    build_spec_fail_typed_projection_signature, build_spec_pass_l1_module,
    build_spec_pass_l2_module, build_spec_pass_module, build_spec_pass_typed_anchor_module,
    build_valid_module, harness_manifest_with_proof, harness_manifest_without_proof, trust_ir_cmd,
};
use trust_ir::{
    Module, ProofKind, SpecAnchor, SpecModule, SpecOrigin, SpecProjectionTarget, SpecProof,
    SpecWaiver, TEMPORAL_FIELD_PATH_PROJECTION_V1,
};

/// Write `module` to `dir/name.tmbc` in the binary format and return the path.
/// (`.tmbc` is the binary codec extension per the CLI's format contract.)
fn write_bin(dir: &std::path::Path, name: &str, module: &Module) -> std::path::PathBuf {
    let path = dir.join(format!("{name}.tmbc"));
    fs::write(&path, trust_ir::binary::serialize_module(module)).expect("write bin");
    path
}

/// Write `module` to `dir/name.trust_ir` in the text format and return the path.
/// (`.trust_ir` is the canonical text extension per the CLI's format contract.)
fn write_text(dir: &std::path::Path, name: &str, module: &Module) -> std::path::PathBuf {
    let path = dir.join(format!("{name}.trust_ir"));
    fs::write(&path, format!("{module}")).expect("write text");
    path
}

#[test]
fn spec_link_passing_module_exits_zero() {
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "pass", &build_spec_pass_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert!(
        output.status.success(),
        "expected exit 0, got {:?}\nstdout: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("ok:"),
        "stdout should report ok, got: {stdout}"
    );
    assert!(
        stdout.contains("100.0%"),
        "passing fixture should report full coverage, got: {stdout}"
    );
}

#[test]
fn spec_link_passing_module_text_format_exits_zero() {
    // Same fixture, but routed through the text serializer+parser, proving the
    // SpecModule survives the text roundtrip the CLI uses.
    let dir = tempdir().expect("tempdir");
    let path = write_text(dir.path(), "pass", &build_spec_pass_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert!(
        output.status.success(),
        "expected exit 0 for text fixture, got {:?}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn spec_link_typed_anchor_to_exact_body_exits_zero() {
    let dir = tempdir().expect("tempdir");
    let path = write_bin(
        dir.path(),
        "typed-pass",
        &build_spec_pass_typed_anchor_module(),
    );

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert!(
        output.status.success(),
        "exact typed anchor must pass\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn spec_link_typed_anchor_to_missing_function_exits_one() {
    let dir = tempdir().expect("tempdir");
    let path = write_bin(
        dir.path(),
        "typed-missing",
        &build_spec_fail_typed_anchor_missing_function(),
    );

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("S2 typed-resolution"), "got: {stderr}");
    assert!(
        stderr.contains("function #99"),
        "must name the missing FuncId: {stderr}"
    );
    assert!(
        stderr.contains("not present in module"),
        "must explain the missing target: {stderr}"
    );
}

#[test]
fn spec_link_typed_anchor_with_mismatched_symbol_exits_one() {
    let dir = tempdir().expect("tempdir");
    let path = write_bin(
        dir.path(),
        "typed-mismatch",
        &build_spec_fail_typed_anchor_mismatched_symbol(),
    );

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("S2 typed-resolution"), "got: {stderr}");
    assert!(
        stderr.contains("rust_symbol \"other::add\""),
        "must name the stale label: {stderr}"
    );
    assert!(
        stderr.contains("does not match typed target \"add\""),
        "must name the typed target: {stderr}"
    );
}

#[test]
fn spec_link_typed_projection_with_non_reference_input_exits_one() {
    let dir = tempdir().expect("tempdir");
    let path = write_bin(
        dir.path(),
        "typed-projection-signature",
        &build_spec_fail_typed_projection_signature(),
    );

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("S2 typed-resolution"), "got: {stderr}");
    assert!(
        stderr.contains("invalid projection function #1"),
        "got: {stderr}"
    );
    assert!(stderr.contains("(&T) -> R"), "got: {stderr}");
}

#[test]
fn spec_link_ob1_bogus_action_exits_one() {
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "ob1", &build_spec_fail_ob1_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(
        output.status.code(),
        Some(1),
        "Ob.1 fixture must exit 1\nstderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("spec-link failed"), "got: {stderr}");
    assert!(
        stderr.contains("Ob.1"),
        "must name Ob.1 (action exists), got: {stderr}"
    );
    assert!(
        stderr.contains("SetOriginMode"),
        "must point at the bogus action, got: {stderr}"
    );
    // Teeth: ONLY Ob.1 fires for this fixture.
    assert!(!stderr.contains("Ob.3"), "Ob.3 must not fire: {stderr}");
    assert!(!stderr.contains("Ob.4"), "Ob.4 must not fire: {stderr}");
}

#[test]
fn spec_link_ob3_uncovered_action_exits_one() {
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "ob3", &build_spec_fail_ob3_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(
        output.status.code(),
        Some(1),
        "Ob.3 fixture must exit 1\nstderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Ob.3"),
        "must name Ob.3 (coverage), got: {stderr}"
    );
    assert!(
        stderr.contains("Pop"),
        "must point at the uncovered action, got: {stderr}"
    );
    assert!(!stderr.contains("Ob.1"), "Ob.1 must not fire: {stderr}");
    assert!(!stderr.contains("Ob.4"), "Ob.4 must not fire: {stderr}");
}

#[test]
fn spec_link_ob4_dangling_machine_exits_one() {
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "ob4", &build_spec_fail_ob4_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(
        output.status.code(),
        Some(1),
        "Ob.4 fixture must exit 1\nstderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Ob.4"),
        "must name Ob.4 (machine resolves), got: {stderr}"
    );
    assert!(
        stderr.contains("terminal_modes"),
        "must point at the dangling machine, got: {stderr}"
    );
    assert!(!stderr.contains("Ob.1"), "Ob.1 must not fire: {stderr}");
    assert!(!stderr.contains("Ob.3"), "Ob.3 must not fire: {stderr}");
}

/// Write a harness-manifest JSON `body` to `dir/name.json` and return the path.
fn write_manifest(dir: &std::path::Path, name: &str, body: &str) -> std::path::PathBuf {
    let path = dir.join(format!("{name}.json"));
    fs::write(&path, body).expect("write manifest");
    path
}

// ---------------------------------------------------------------------------
// L1 — proof_name must resolve to a real harness (§1.C / §3.1 item 6)
// ---------------------------------------------------------------------------

#[test]
fn spec_link_l1_unresolved_proof_exits_one() {
    // RED: a SpecProof proof_name "does_not_exist" + a manifest lacking it.
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "l1", &build_spec_fail_l1_module());
    let manifest = write_manifest(dir.path(), "m", &harness_manifest_without_proof());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .arg("--harness-manifest")
        .arg(&manifest)
        .output()
        .expect("run trust-ir");

    assert_eq!(
        output.status.code(),
        Some(1),
        "L1 red fixture must exit 1\nstderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("spec-link failed"), "got: {stderr}");
    assert!(
        stderr.contains("L1"),
        "must name L1 (proof resolves), got: {stderr}"
    );
    assert!(
        stderr.contains("does_not_exist"),
        "must point at the bogus proof_name, got: {stderr}"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("checked 1 proof binding"), "got: {stdout}");
    assert!(
        !stdout.contains("resolved 1 proof binding"),
        "an unresolved proof must not be reported as resolved: {stdout}"
    );
}

#[test]
fn spec_link_l1_resolved_proof_exits_zero() {
    // CONTROL: same shape, real proof_name + a manifest that contains it.
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "l1ok", &build_spec_pass_l1_module());
    let manifest = write_manifest(dir.path(), "m", &harness_manifest_with_proof());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .arg("--harness-manifest")
        .arg(&manifest)
        .output()
        .expect("run trust-ir");

    assert!(
        output.status.success(),
        "L1 control must exit 0, got {:?}\nstdout: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("proof binding") && stdout.contains("resolved (L1)"),
        "should report the resolved proof, got: {stdout}"
    );
}

#[test]
fn spec_link_linked_proofs_without_manifest_fail_by_default() {
    // Linked proofs require a manifest without an opt-in flag.
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "l1nomani", &build_spec_pass_l1_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("L1 proof-manifest-required"),
        "must reject the missing manifest, got: {stderr}"
    );
}

#[test]
fn spec_link_exploratory_unverified_proofs_remain_non_certifying_and_nonzero() {
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "l1explore", &build_spec_pass_l1_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .arg("--allow-unverified-proofs")
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("spec-link-status: non-certifying"),
        "got: {stderr}"
    );
    assert!(
        stderr.contains("code=proof-manifest-unverified"),
        "stable machine-readable reason missing: {stderr}"
    );
    assert!(
        !stderr.contains("L1 proof-manifest-required"),
        "override should analyze: {stderr}"
    );
}

#[test]
fn spec_link_design_only_mode_is_machine_readable_and_non_certifying() {
    let dir = tempdir().expect("tempdir");
    let mut spec = SpecModule::design_only("Design");
    spec.actions.push("Step".to_string());
    let mut module = Module::new("design-only");
    module.spec_modules.push(spec);
    let path = write_bin(dir.path(), "design-only", &module);

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("spec-link-status: non-certifying"),
        "got: {stderr}"
    );
    assert!(stderr.contains("code=design-only"), "got: {stderr}");
    assert!(
        !stderr.contains("Ob.3"),
        "design-only mode does not claim coverage: {stderr}"
    );
}

#[test]
fn spec_link_linked_zero_anchor_machine_still_enforces_total_coverage() {
    let dir = tempdir().expect("tempdir");
    let mut spec = SpecModule::linked("Linked");
    spec.actions.push("Step".to_string());
    let mut module = Module::new("linked-zero-anchor");
    module.spec_modules.push(spec);
    let path = write_bin(dir.path(), "linked-zero-anchor", &module);

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("spec-link-status: non-certifying"),
        "got: {stderr}"
    );
    assert!(
        stderr.contains("Ob.3 coverage") && stderr.contains("Step"),
        "got: {stderr}"
    );
}

#[test]
fn spec_link_linked_embedded_anchor_requires_typed_action_identity() {
    let dir = tempdir().expect("tempdir");
    let mut spec = SpecModule::linked("Embedded");
    spec.actions.push("Step".to_string());
    spec.anchors.push(SpecAnchor {
        machine: "Embedded".to_string(),
        action: "Step".to_string(),
        rust_symbol: "crate::step".to_string(),
        span: "fixture.rs:1:1".to_string(),
        project: Some(TEMPORAL_FIELD_PATH_PROJECTION_V1.to_string()),
        function: None,
        projection_target: Some(SpecProjectionTarget::TemporalFieldPathsV1),
    });
    let mut module = Module::new("embedded-untyped");
    module.spec_modules.push(spec);
    let path = write_bin(dir.path(), "embedded-untyped", &module);

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("S2 typed-resolution"), "got: {stderr}");
    assert!(
        stderr.contains("typed action function target"),
        "got: {stderr}"
    );
}

#[test]
fn spec_link_external_unresolved_projection_can_never_certify_linked_mode() {
    let dir = tempdir().expect("tempdir");
    let mut spec = SpecModule::linked("External");
    spec.origin = SpecOrigin::External("External.tla".to_string());
    spec.actions.push("Step".to_string());
    spec.anchors.push(SpecAnchor {
        machine: "External".to_string(),
        action: "Step".to_string(),
        rust_symbol: "add".to_string(),
        span: "fixture.rs:1:1".to_string(),
        project: Some("external::project".to_string()),
        function: Some(trust_ir::FuncId::new(0)),
        projection_target: Some(SpecProjectionTarget::ExternalUnresolved),
    });
    let mut module = build_valid_module();
    module.name = "external-unresolved".to_string();
    module.spec_modules.push(spec);
    let path = write_bin(dir.path(), "external-unresolved", &module);

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("spec-link-status: non-certifying"),
        "got: {stderr}"
    );
    assert!(
        stderr.contains("code=external-projection-unresolved"),
        "got: {stderr}"
    );
    assert!(
        !stderr.contains("spec-link failed:"),
        "no obligation need be violated: {stderr}"
    );
}

#[test]
fn spec_link_proofs_require_manifest_errors_when_absent() {
    // Proofs present, NO --harness-manifest, but --require-manifest → ERROR.
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "l1req", &build_spec_pass_l1_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .arg("--require-manifest")
        .output()
        .expect("run trust-ir");

    assert_eq!(
        output.status.code(),
        Some(1),
        "--require-manifest with no manifest must exit 1\nstderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("proof-manifest-required") && stderr.contains("no harness manifest"),
        "must explain the required-but-absent manifest, got: {stderr}"
    );
}

// ---------------------------------------------------------------------------
// L2 — mandatory non-empty project= (§1.C / §3.1 item 7)
// ---------------------------------------------------------------------------

#[test]
fn spec_link_l2_missing_projection_exits_one() {
    // RED: a present owned anchor with project: None.
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "l2", &build_spec_fail_l2_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(
        output.status.code(),
        Some(1),
        "L2 red fixture must exit 1\nstderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("L2"),
        "must name L2 (projection present), got: {stderr}"
    );
    assert!(
        stderr.contains("Pop"),
        "must point at the projection-less action, got: {stderr}"
    );
    // Teeth: only L2 fires (Pop is anchored + the machine is fully covered).
    assert!(!stderr.contains("Ob.1"), "Ob.1 must not fire: {stderr}");
    assert!(!stderr.contains("Ob.3"), "Ob.3 must not fire: {stderr}");
    assert!(!stderr.contains("Ob.4"), "Ob.4 must not fire: {stderr}");
}

#[test]
fn spec_link_l2_present_projection_exits_zero() {
    // CONTROL: same shape, but the Pop anchor carries a real project name.
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "l2ok", &build_spec_pass_l2_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert!(
        output.status.success(),
        "L2 control must exit 0, got {:?}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr),
    );
}

// ---------------------------------------------------------------------------
// L3 — external Ob.1 resolves against Next-only actions (§1.C / §3.1 item 8)
// ---------------------------------------------------------------------------

#[test]
fn spec_link_l3_external_typeok_anchor_is_ob1_reject() {
    // An external (Next-only `actions`) SpecModule + an anchor naming the
    // non-Next def `TypeOK` MUST be rejected by Ob.1. This locks the stricter
    // external behavior (the artifact carries only Next disjuncts as actions).
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "l3", &build_spec_fail_l3_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(
        output.status.code(),
        Some(1),
        "L3 external+TypeOK fixture must exit 1 (Ob.1)\nstderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Ob.1"),
        "external non-Next anchor must be an Ob.1 reject, got: {stderr}"
    );
    assert!(
        stderr.contains("TypeOK"),
        "must point at the non-Next def TypeOK, got: {stderr}"
    );
}

#[test]
fn spec_link_module_without_specs_is_user_error() {
    // A module with no SpecModule objects is a usage error (exit 1), not a
    // silent success.
    let dir = tempdir().expect("tempdir");
    let path = write_bin(dir.path(), "nospec", &build_valid_module());

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("no SpecModule"),
        "must explain the empty input, got: {stderr}"
    );
}

#[test]
fn spec_link_rejects_duplicate_machine_identity_once() {
    let dir = tempdir().expect("tempdir");
    let mut module = build_spec_pass_module();
    module.spec_modules.push(module.spec_modules[0].clone());
    let path = write_bin(dir.path(), "duplicate-machine", &module);

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("S0 unique-identity"), "got: {stderr}");
    assert_eq!(
        stderr.matches("duplicate SpecModule machine name").count(),
        1,
        "duplicate identity must be normalized: {stderr}"
    );
}

#[test]
fn spec_link_rejects_all_cross_container_binding_kinds() {
    let dir = tempdir().expect("tempdir");
    let mut a = SpecModule::new("A");
    a.actions.push("Step".to_string());
    a.anchors.push(SpecAnchor {
        machine: "B".to_string(),
        action: "Step".to_string(),
        function: None,
        rust_symbol: "crate::B::step".to_string(),
        span: "fixture.rs:1:1".to_string(),
        project: Some("crate::project".to_string()),
        projection_target: None,
    });
    a.waivers.push(SpecWaiver {
        machine: "B".to_string(),
        action: "Step".to_string(),
        reason: "not implemented".to_string(),
    });
    a.proofs.push(SpecProof {
        machine: "B".to_string(),
        action: "Step".to_string(),
        proof_name: "step_refines".to_string(),
        kind: ProofKind::Kani,
    });
    let mut b = SpecModule::new("B");
    b.actions.push("Step".to_string());
    let mut module = Module::new("foreign-bindings");
    module.spec_modules = vec![a, b];
    let path = write_bin(dir.path(), "foreign-bindings", &module);

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        stderr.matches("S1 container-owns-binding").count(),
        3,
        "got: {stderr}"
    );
    for binding in ["anchor", "waiver", "proof"] {
        assert!(
            stderr.contains(&format!("stored {binding}")),
            "got: {stderr}"
        );
    }
}

#[test]
fn spec_link_checks_proof_references_without_a_manifest() {
    let dir = tempdir().expect("tempdir");
    let mut module = build_spec_pass_module();
    module.spec_modules[0].proofs.extend([
        SpecProof {
            machine: "ring".to_string(),
            action: "Missing".to_string(),
            proof_name: "bad_action".to_string(),
            kind: ProofKind::Kani,
        },
        SpecProof {
            machine: "ghost".to_string(),
            action: "Push".to_string(),
            proof_name: "bad_machine".to_string(),
            kind: ProofKind::Kani,
        },
    ]);
    let path = write_bin(dir.path(), "proof-closure", &module);

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("Ob.1 action-exists"), "got: {stderr}");
    assert!(stderr.contains("Ob.4 machine-resolves"), "got: {stderr}");
    assert!(
        !stderr.contains("proof_name unverified"),
        "structural failure should not cascade: {stderr}"
    );
}

#[test]
fn spec_link_rejects_whitespace_only_projection() {
    let dir = tempdir().expect("tempdir");
    let mut module = build_spec_pass_module();
    module.spec_modules[0].anchors[0].project = Some(" \t ".to_string());
    let path = write_bin(dir.path(), "blank-project", &module);

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("L2 projection-present"), "got: {stderr}");
    assert!(stderr.contains("absent or blank"), "got: {stderr}");
}

#[test]
fn spec_link_rejects_blank_and_duplicate_manifest_identities() {
    let dir = tempdir().expect("tempdir");
    let path = write_bin(
        dir.path(),
        "manifest-identity",
        &build_spec_pass_l1_module(),
    );
    let cases = [
        (
            "blank",
            r#"{"harnesses":[{"name":" \t ","span":"fixture.rs:1:1"}]}"#,
            "blank name",
        ),
        (
            "duplicate",
            r#"{"harnesses":[{"name":"same","span":"a"},{"name":"same","span":"b"}]}"#,
            "duplicate harness name `same`",
        ),
    ];

    for (name, body, expected) in cases {
        let manifest = write_manifest(dir.path(), name, body);
        let output = trust_ir_cmd()
            .arg("spec-link")
            .arg(&path)
            .arg("--harness-manifest")
            .arg(&manifest)
            .output()
            .expect("run trust-ir");
        assert_eq!(output.status.code(), Some(1));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(expected), "case {name}: {stderr}");
    }
}

#[test]
fn require_manifest_accumulates_typed_anchor_and_coverage_failures() {
    let dir = tempdir().expect("tempdir");
    let mut module = build_spec_fail_typed_anchor_missing_function();
    let spec = &mut module.spec_modules[0];
    spec.actions.push("Uncovered".to_string());
    spec.proofs.push(SpecProof {
        machine: "ring".to_string(),
        action: "Push".to_string(),
        proof_name: "ring_push_refines".to_string(),
        kind: ProofKind::Kani,
    });
    let path = write_bin(dir.path(), "combined-errors", &module);

    let output = trust_ir_cmd()
        .arg("spec-link")
        .arg(&path)
        .arg("--require-manifest")
        .output()
        .expect("run trust-ir");

    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    let typed_anchor = stderr
        .find("S2 typed-resolution")
        .expect("typed-anchor error");
    let coverage = stderr.find("Ob.3 coverage").expect("coverage error");
    let missing_manifest = stderr
        .find("proof-manifest-required")
        .expect("missing-manifest error");
    assert!(
        typed_anchor < coverage && coverage < missing_manifest,
        "nondeterministic order: {stderr}"
    );
}
