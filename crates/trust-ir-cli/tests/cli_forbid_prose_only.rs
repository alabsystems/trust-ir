// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir validate --forbid-prose-only` — the
//! formula-less non-`Pending` census (roadmap WS1.8 rule (g), finding F-024).
//!
//! A row whose `formula` is `None` states its claim in prose alone; once its
//! status is a verdict (`Discharged` / `Failed` / `Trusted` / `Certified`) the
//! verdict is about nothing a verifier can bind. The census lists every such
//! row and exits 1. A formula-less `Pending` row is legitimate (F-086) and is
//! never listed. Opt-in, mirroring `--forbid-trusted`: the default verdict is
//! untouched.

mod common;

use std::fs;
use std::path::{Path, PathBuf};

use tempfile::tempdir;

use common::{
    build_prose_only_discharged_module, build_prose_only_failed_module,
    build_prose_only_pending_module, build_valid_module, trust_ir_cmd,
};

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
fn zero_prose_only_module_passes_census() {
    let dir = tempdir().expect("tempdir");
    let path = write_module(dir.path(), &build_valid_module());
    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--forbid-prose-only")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "a module with no formula-less non-Pending row must exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("prose-only census:")
            && stdout.contains("no formula-less non-Pending obligation"),
        "stdout should report the empty census, got: {stdout}"
    );
}

/// The increment's positive row: a formula-less Discharged row exits 1 and is
/// NAMED by the census (the structural `DischargedWithoutCertificate` refusal
/// is reported beside it, never instead of it).
#[test]
fn formula_less_discharged_row_fails_census() {
    let dir = tempdir().expect("tempdir");
    let path = write_module(dir.path(), &build_prose_only_discharged_module());
    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--forbid-prose-only")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(1),
        "a formula-less Discharged row must exit 1\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("prose-only census failed")
            && stderr.contains("status Discharged with no formula")
            && stderr.contains("PanicFreedom")
            && stderr.contains("function add")
            && stderr.contains("discharged in prose only"),
        "stderr should name the prose-only Discharged row (kind, scope, description), got: {stderr}"
    );
}

/// A formula-less Failed row: structurally valid (plain `validate` exits 0),
/// refused by the census alone — so the exit code is the census's.
#[test]
fn formula_less_failed_row_fails_census_only_under_the_flag() {
    let dir = tempdir().expect("tempdir");
    let path = write_module(dir.path(), &build_prose_only_failed_module());

    let plain = trust_ir_cmd()
        .arg("validate")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        plain.status.success(),
        "without --forbid-prose-only a formula-less Failed row must still exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&plain.stdout),
        String::from_utf8_lossy(&plain.stderr)
    );

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--forbid-prose-only")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("prose-only census failed")
            && stderr.contains("status Failed with no formula")
            && stderr.contains("refuted in prose"),
        "stderr should name the prose-only Failed row, got: {stderr}"
    );
}

/// The control: a formula-less Pending row is the legitimate
/// recorded-before-stated shape (F-086) and passes the census.
#[test]
fn formula_less_pending_row_passes_census() {
    let dir = tempdir().expect("tempdir");
    let path = write_module(dir.path(), &build_prose_only_pending_module());
    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--forbid-prose-only")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "a formula-less Pending row must exit 0 under --forbid-prose-only\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("no formula-less non-Pending obligation"),
        "stdout should report the empty census, got: {stdout}"
    );
}

/// The three censuses compose: the prose-only census fires while the Trusted
/// and Failed censuses report whatever they see, and the exit code is the
/// worst.
#[test]
fn forbid_prose_only_composes_with_the_other_censuses() {
    let dir = tempdir().expect("tempdir");
    let path = write_module(dir.path(), &build_prose_only_failed_module());
    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--forbid-trusted")
        .arg("--forbid-prose-only")
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
        stderr.contains("prose-only census failed"),
        "the prose-only census should fire, got stderr: {stderr}"
    );
}
