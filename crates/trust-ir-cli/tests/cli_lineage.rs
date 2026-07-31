// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir validate --lineage` — the standing
//! lineage-closure CI gate (bootstrap-trust-model.md sketch item 2).

mod common;

use std::fs;
use std::path::{Path, PathBuf};

use tempfile::tempdir;

use common::{
    build_lineage_closed_fixture, build_lineage_misthreaded_fixture,
    build_lineage_opaque_smt_fixture, build_lineage_trusted_rung_fixture, trust_ir_cmd,
};
use trust_ir::proof::ProofLineageManifest;

/// Write the module as a `.tmbc` and the manifest as a `.tmpl` sidecar into
/// `dir`, returning both paths.
fn write_fixture(
    dir: &Path,
    module: &trust_ir::Module,
    manifest: &ProofLineageManifest,
) -> (PathBuf, PathBuf) {
    let module_path = dir.join("module.tmbc");
    fs::write(&module_path, trust_ir::binary::serialize_module(module)).expect("write module");
    let manifest_path = dir.join("lineage.tmpl");
    fs::write(
        &manifest_path,
        trust_ir::binary::serialize_proof_lineage_manifest(manifest),
    )
    .expect("write manifest");
    (module_path, manifest_path)
}

#[test]
fn closed_lineage_passes() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = build_lineage_closed_fixture();
    let (module_path, manifest_path) = write_fixture(dir.path(), &module, &manifest);

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(&manifest_path)
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "closed lineage must exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("lineage: closed"),
        "stdout should report the closed verdict, got: {stdout}"
    );
}

#[test]
fn opaque_smt_lineage_fails_without_replay_authority() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = build_lineage_opaque_smt_fixture();
    let (module_path, manifest_path) = write_fixture(dir.path(), &module, &manifest);

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(&manifest_path)
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(1),
        "opaque proof bytes must not close lineage\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("was not replayed by this validator") && stderr.contains("opaque evidence"),
        "stderr should identify the missing replay authority, got: {stderr}"
    );
}

#[test]
fn trusted_rung_open_lineage_fails() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = build_lineage_trusted_rung_fixture();
    let (module_path, manifest_path) = write_fixture(dir.path(), &module, &manifest);

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(&manifest_path)
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(1),
        "a faith-stamped rung must exit 1\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("lineage check failed"),
        "stderr should announce the lineage failure, got: {stderr}"
    );
    assert!(
        stderr.contains("faith-stamped (Trusted)") && stderr.contains("hand-checked by reviewer"),
        "stderr should name the Trusted rung and its justification, got: {stderr}"
    );
}

#[test]
fn misthreaded_lineage_fails() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = build_lineage_misthreaded_fixture();
    let (module_path, manifest_path) = write_fixture(dir.path(), &module, &manifest);

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(&manifest_path)
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(1),
        "a mis-threaded chain must exit 1\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    // The digest mismatch is caught by `validate_against` (structural
    // validation), not by the closure walk — the flag must run both.
    assert!(
        stderr.contains("does not match dependency"),
        "stderr should report the dependency digest mismatch, got: {stderr}"
    );
}

#[test]
fn json_manifest_sidecar_accepted() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = build_lineage_closed_fixture();
    let module_path = dir.path().join("module.tmbc");
    fs::write(&module_path, trust_ir::binary::serialize_module(&module)).expect("write module");
    let manifest_path = dir.path().join("lineage.json");
    fs::write(
        &manifest_path,
        serde_json::to_vec_pretty(&manifest).expect("json"),
    )
    .expect("write manifest");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(&manifest_path)
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "closed lineage via .json sidecar must exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("lineage: closed"),
        "stdout should report the closed verdict, got: {stdout}"
    );
}

#[test]
fn missing_manifest_file_exits_io_error() {
    let dir = tempdir().expect("tempdir");
    let (module, _) = build_lineage_closed_fixture();
    let module_path = dir.path().join("module.tmbc");
    fs::write(&module_path, trust_ir::binary::serialize_module(&module)).expect("write module");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(dir.path().join("nonexistent.tmpl"))
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(2),
        "unreadable manifest is an I/O error\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("error:"),
        "expected error message, got: {stderr}"
    );
}

#[test]
fn without_lineage_flag_behavior_unchanged() {
    // The same open-lineage module validates cleanly when --lineage is not
    // passed: the gate is opt-in and the default verdict is untouched.
    let dir = tempdir().expect("tempdir");
    let (module, _) = build_lineage_trusted_rung_fixture();
    let module_path = dir.path().join("module.tmbc");
    fs::write(&module_path, trust_ir::binary::serialize_module(&module)).expect("write module");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "without --lineage the verdict must be unchanged\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
