// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir validate --forbid-failed` — the
//! violated-contract build-abort gate (CK1 WS3-M1: a refuted ensures must be
//! able to fail the build, negative-test-first).

mod common;

use std::fs;
use std::path::{Path, PathBuf};

use tempfile::tempdir;

use common::{build_failed_status_module, build_valid_module, trust_ir_cmd};

fn write_module(dir: &Path, module: &trust_ir::Module) -> PathBuf {
    let path = dir.join("module.tmbc");
    fs::write(
        &path,
        trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
    )
    .expect("write module");
    path
}

#[test]
fn zero_failed_module_passes_census() {
    // A valid module with no Failed statuses must have an empty census and
    // leave the gate green.
    let dir = tempdir().expect("tempdir");
    let module = build_valid_module();
    let path = write_module(dir.path(), &module);

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--forbid-failed")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "zero-Failed module must exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("failed-obligation census:")
            && stdout.contains("no Failed obligation status"),
        "stdout should report the empty census, got: {stdout}"
    );
}

#[test]
fn failed_obligation_status_aborts_build() {
    let dir = tempdir().expect("tempdir");
    let path = write_module(dir.path(), &build_failed_status_module());

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--forbid-failed")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(1),
        "a Failed obligation status must exit 1\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("failed-obligation census failed"),
        "stderr should announce the census failure, got: {stderr}"
    );
    // Each occurrence is listed with id, kind, function scope, and the clause
    // (description) — the item is NAMED, not just counted.
    assert!(
        stderr.contains("status Failed")
            && stderr.contains("Postcondition")
            && stderr.contains("function add")
            && stderr.contains("ensures clause 0 of 'add'"),
        "stderr should name the Failed obligation (kind, scope, clause), got: {stderr}"
    );
}

#[test]
fn without_forbid_failed_flag_behavior_unchanged() {
    // A Failed obligation is recorded module data: plain `validate` still
    // exits 0 (the abort is opt-in), matching validate_module's semantics.
    let dir = tempdir().expect("tempdir");
    let path = write_module(dir.path(), &build_failed_status_module());

    let output = trust_ir_cmd()
        .arg("validate")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "without --forbid-failed a Failed obligation must still exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn forbid_failed_and_forbid_trusted_compose() {
    // Both censuses run when both flags are passed; the Failed census fires
    // while the Trusted census stays green — the exit code is the worst.
    let dir = tempdir().expect("tempdir");
    let path = write_module(dir.path(), &build_failed_status_module());

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--forbid-trusted")
        .arg("--forbid-failed")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("no Trusted obligation status"),
        "the Trusted census should pass, got stdout: {stdout}"
    );
    assert!(
        stderr.contains("failed-obligation census failed"),
        "the Failed census should fire, got stderr: {stderr}"
    );
}
