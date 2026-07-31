// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir validate --forbid-trusted` — the standing
//! zero-`Trusted` evidence-census CI gate (Program CK1 flagship-lane gate).

mod common;

use std::fs;
use std::path::{Path, PathBuf};

use tempfile::tempdir;

use common::{
    build_trusted_evidence_module, build_trusted_status_module, build_valid_module, trust_ir_cmd,
};

fn write_module(dir: &Path, module: &trust_ir::Module) -> PathBuf {
    let path = dir.join("module.tmbc");
    fs::write(&path, trust_ir::binary::serialize_module(module)).expect("write module");
    path
}

#[test]
fn zero_trusted_module_passes_census() {
    // A valid module with no faith-stamped obligations or evidence must have
    // an empty census and leave the gate green.
    let dir = tempdir().expect("tempdir");
    let module = build_valid_module();
    let path = write_module(dir.path(), &module);

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--forbid-trusted")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "zero-Trusted module must exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("trusted census:")
            && stdout.contains("no Trusted obligation status, no Trusted evidence"),
        "stdout should report the empty census, got: {stdout}"
    );
}

#[test]
fn trusted_obligation_status_fails_census() {
    let dir = tempdir().expect("tempdir");
    let path = write_module(dir.path(), &build_trusted_status_module());

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--forbid-trusted")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(1),
        "a Trusted obligation status must exit 1\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("trusted census failed"),
        "stderr should announce the census failure, got: {stderr}"
    );
    // Each occurrence is listed with id, kind, function scope, and the
    // justification (description) — the item is NAMED, not just counted.
    assert!(
        stderr.contains("status Trusted")
            && stderr.contains("PanicFreedom")
            && stderr.contains("function add")
            && stderr.contains("believed panic-free (manual audit)"),
        "stderr should name the Trusted obligation (kind, scope, justification), got: {stderr}"
    );
}

#[test]
fn trusted_evidence_certificate_fails_census() {
    let dir = tempdir().expect("tempdir");
    let path = write_module(dir.path(), &build_trusted_evidence_module());

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--forbid-trusted")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(1),
        "Trusted evidence must exit 1\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("trusted census failed"),
        "stderr should announce the census failure, got: {stderr}"
    );
    assert!(
        stderr.contains("Trusted evidence") && stderr.contains("hand-checked 2026-07-10"),
        "stderr should name the Trusted evidence and its justification, got: {stderr}"
    );
}

#[test]
fn without_forbid_trusted_flag_behavior_unchanged() {
    // Both internally consistent faith-stamped modules validate cleanly
    // without the flag: the
    // census is opt-in and the default verdict is untouched.
    let dir = tempdir().expect("tempdir");
    for (name, module) in [
        ("status.tmbc", build_trusted_status_module()),
        ("evidence.tmbc", build_trusted_evidence_module()),
    ] {
        let path = dir.path().join(name);
        fs::write(&path, trust_ir::binary::serialize_module(&module)).expect("write module");
        let output = trust_ir_cmd()
            .arg("validate")
            .arg(&path)
            .output()
            .expect("run trust-ir");
        assert!(
            output.status.success(),
            "without --forbid-trusted {name} must still exit 0\nstdout: {}\nstderr: {}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
