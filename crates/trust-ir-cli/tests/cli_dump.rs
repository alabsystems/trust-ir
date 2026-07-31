// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir dump`.

mod common;

use std::fs;

use tempfile::tempdir;

use common::{build_diagnostics_module, build_valid_module, trust_ir_cmd};

#[test]
fn dump_binary_module_prints_text_format() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("m.tmbc");
    let bytes = trust_ir::binary::serialize_module(&build_valid_module());
    fs::write(&path, bytes).expect("write");

    let output = trust_ir_cmd()
        .arg("dump")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "expected exit 0, got {:?}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Text format starts with "; TrustIr text format"
    assert!(
        stdout.contains("; TrustIr text format"),
        "dump output should be text format, got:\n{stdout}"
    );
    assert!(
        stdout.contains("test_valid"),
        "dump should contain module name, got:\n{stdout}"
    );
    assert!(
        stdout.contains("add"),
        "dump should contain function name, got:\n{stdout}"
    );
}

#[test]
fn dump_renders_obligation_diagnostics_on_stderr_only() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("diag.tmbc");
    let bytes = trust_ir::binary::serialize_module(&build_diagnostics_module());
    fs::write(&path, bytes).expect("write");

    let output = trust_ir_cmd()
        .arg("dump")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    // stdout stays the parseable text form (raw `diagnostic …` lines with a
    // bare file index).
    assert!(
        stdout.contains("diagnostic ") && stdout.contains("at 0 12 5"),
        "stdout should carry the raw text-format diagnostics, got:\n{stdout}"
    );
    assert!(
        !stdout.contains("src/main.rs:12:5:"),
        "the rendered report must not pollute the parseable stdout, got:\n{stdout}"
    );
    // stderr carries the rendered report with the file table resolved.
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "src/main.rs:12:5: error: could not prove a + b stays in range \
             [counterexample: a=i64::MAX, b=1]"
        ),
        "stderr should render the resolved diagnostic, got: {stderr}"
    );
}

#[test]
fn dump_json_module_prints_text_format() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("m.json");
    let bytes = serde_json::to_vec(&build_valid_module()).expect("json");
    fs::write(&path, bytes).expect("write");

    let output = trust_ir_cmd()
        .arg("dump")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("; TrustIr text format"));
    assert!(stdout.contains("test_valid"));
}

#[test]
fn dump_text_module_prints_text_format() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("m.trust_ir");
    let text = format!("{}", build_valid_module());
    fs::write(&path, text).expect("write");

    let output = trust_ir_cmd()
        .arg("dump")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("; TrustIr text format"));
}
