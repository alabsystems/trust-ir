// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir show-gpu-eligibility`.

mod common;

use std::fs;

use tempfile::tempdir;

use common::{
    build_gpu_eligible_module, build_gpu_high_divergence_module, build_valid_module, trust_ir_cmd,
};

#[test]
fn gpu_eligibility_true_when_all_annotations_present() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("m.tmbc");
    fs::write(
        &path,
        trust_ir::binary::serialize_module(&build_gpu_eligible_module()),
    )
    .expect("write");

    let output = trust_ir_cmd()
        .arg("show-gpu-eligibility")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("function kernel"),
        "missing function header, got:\n{stdout}"
    );
    assert!(
        stdout.contains("is_safe_for_gpu  = true"),
        "expected is_safe_for_gpu=true, got:\n{stdout}"
    );
    assert!(
        stdout.contains("is_gpu_eligible  = true"),
        "expected is_gpu_eligible=true, got:\n{stdout}"
    );
    assert!(
        stdout.contains("divergence_class = uniform"),
        "expected uniform divergence, got:\n{stdout}"
    );
    assert!(
        stdout.contains("ParallelMap"),
        "gpu_proofs list should include ParallelMap, got:\n{stdout}"
    );
}

#[test]
fn gpu_eligibility_false_when_divergence_is_high() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("m.tmbc");
    fs::write(
        &path,
        trust_ir::binary::serialize_module(&build_gpu_high_divergence_module()),
    )
    .expect("write");

    let output = trust_ir_cmd()
        .arg("show-gpu-eligibility")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Base contract still holds — safe_for_gpu must be true per the frozen
    // design §3.2 predicate.
    assert!(
        stdout.contains("is_safe_for_gpu  = true"),
        "safe_for_gpu must be true under frozen contract, got:\n{stdout}"
    );
    // But the stricter gate rejects High divergence.
    assert!(
        stdout.contains("is_gpu_eligible  = false"),
        "is_gpu_eligible must be false for DivergenceClass(High), got:\n{stdout}"
    );
    assert!(
        stdout.contains("divergence_class = high"),
        "should report divergence high, got:\n{stdout}"
    );
}

#[test]
fn gpu_eligibility_without_parallel_map_is_not_eligible() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("m.tmbc");
    fs::write(
        &path,
        trust_ir::binary::serialize_module(&build_valid_module()),
    )
    .expect("write");

    let output = trust_ir_cmd()
        .arg("show-gpu-eligibility")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("is_safe_for_gpu  = true"));
    assert!(
        stdout.contains("is_gpu_eligible  = false"),
        "no ParallelMap ⇒ not gpu_eligible, got:\n{stdout}"
    );
    assert!(stdout.contains("divergence_class = <none>"));
}

#[test]
fn gpu_eligibility_func_filter_hits_and_misses() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("m.tmbc");
    fs::write(
        &path,
        trust_ir::binary::serialize_module(&build_gpu_eligible_module()),
    )
    .expect("write");

    // Hit.
    let output = trust_ir_cmd()
        .arg("show-gpu-eligibility")
        .arg(&path)
        .arg("--func")
        .arg("kernel")
        .output()
        .expect("run trust-ir");
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("function kernel"));

    // Miss -> exit nonzero.
    let output = trust_ir_cmd()
        .arg("show-gpu-eligibility")
        .arg(&path)
        .arg("--func")
        .arg("does_not_exist")
        .output()
        .expect("run trust-ir");
    assert!(
        !output.status.success(),
        "expected nonzero exit for unknown function, stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("no function named"), "stderr: {stderr}");
}
