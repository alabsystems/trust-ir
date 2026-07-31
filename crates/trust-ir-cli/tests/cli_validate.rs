// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir validate`.

mod common;

use std::fs;

use tempfile::tempdir;

use common::{build_diagnostics_module, build_invalid_module, build_valid_module, trust_ir_cmd};

#[test]
fn validate_valid_module_exits_zero() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("ok.tmbc");
    let bytes = trust_ir::binary::serialize_module(&build_valid_module());
    fs::write(&path, bytes).expect("write");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "expected exit 0, got {:?}\nstdout: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("ok:"),
        "stdout should report ok, got: {stdout}"
    );
}

#[test]
fn validate_invalid_module_exits_nonzero_with_stderr() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("bad.tmbc");
    let bytes = trust_ir::binary::serialize_module(&build_invalid_module());
    fs::write(&path, bytes).expect("write");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        !output.status.success(),
        "expected nonzero exit, got success\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("validation failed"),
        "stderr should explain validation failure, got: {stderr}"
    );
    assert!(
        stderr.contains("BlockMissingTerminator") || stderr.contains("EmptyFunction"),
        "stderr should mention the specific validation error, got: {stderr}"
    );
}

#[test]
fn validate_reports_rendered_obligation_diagnostics_without_failing() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("diag.tmbc");
    let bytes = trust_ir::binary::serialize_module(&build_diagnostics_module());
    fs::write(&path, bytes).expect("write");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    // Diagnostics are module data being reported, not a validation verdict.
    assert!(
        output.status.success(),
        "diagnostics must not change the exit code\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("obligation diagnostics (2):"),
        "stderr should announce the diagnostics report, got: {stderr}"
    );
    assert!(
        stderr.contains(
            "src/main.rs:12:5: error: could not prove a + b stays in range \
             [counterexample: a=i64::MAX, b=1]"
        ),
        "stderr should render path:line:col: severity: message [detail], got: {stderr}"
    );
    assert!(
        stderr.contains("note: see verifier transcript"),
        "a location-less diagnostic renders without a path prefix, got: {stderr}"
    );
}

#[test]
fn validate_missing_file_exits_nonzero() {
    let output = trust_ir_cmd()
        .arg("validate")
        .arg("/nonexistent/path/to/module.trust_ir")
        .output()
        .expect("run trust-ir");
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("error:"),
        "expected error message, got: {stderr}"
    );
}

#[test]
fn validate_explicit_json_format() {
    let dir = tempdir().expect("tempdir");
    // Intentionally use a non-standard extension so format detection would fail
    // without the --format override.
    let path = dir.path().join("module.weird");
    let bytes = serde_json::to_vec(&build_valid_module()).expect("json");
    fs::write(&path, bytes).expect("write");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--format")
        .arg("json")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "expected exit 0, got {:?}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}
