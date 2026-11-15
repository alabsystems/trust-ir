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
    let bytes = trust_ir::binary::serialize_module(&build_valid_module())
        .expect("serialize_module: test fixture");
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
    let bytes = trust_ir::binary::serialize_module(&build_diagnostics_module())
        .expect("serialize_module: test fixture");
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

/// Roadmap WS4.2: `dump` keeps the human `Display` form and still succeeds on
/// a module text cannot carry, but marks it `; #lossy:` right after the
/// header — and that dump is refused by the parser (`convert --from text`).
#[test]
fn dump_marks_a_lossy_module_and_the_dump_does_not_parse_back() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("summary.tmbc");
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort, ProofFormula};
    let mut module = build_valid_module();
    // A field text still cannot carry: a summary clause whose binding sort
    // nests deeper than `MAX_TEXT_CLAUSE_SORT_DEPTH` (WS4.4 carries every
    // shallower summary; until WS4.5 this was a `global_asm` block, which
    // text now carries).
    let mut sort = ClauseSort::Bool;
    for _ in 0..trust_ir::text_loss::MAX_TEXT_CLAUSE_SORT_DEPTH {
        sort = ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(sort));
    }
    let mut clause = ProofFormula::smtlib2("(= x x)", "Bool");
    clause.bindings.push((
        "x".to_string(),
        ClauseBinding {
            sort,
            place: ClausePlace::World,
        },
    ));
    module.functions[0].summary = Some(trust_ir::FunctionSummary::new().ensuring(clause));
    fs::write(
        &path,
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
    )
    .expect("write");

    let output = trust_ir_cmd()
        .arg("dump")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        stdout.lines().nth(1),
        Some("; #lossy: function-summary(fn 0)"),
        "{stdout}"
    );

    let dumped = dir.path().join("summary.trust_ir");
    fs::write(&dumped, stdout.as_bytes()).expect("write dump");
    let out = trust_ir_cmd()
        .arg("convert")
        .arg("--from")
        .arg("text")
        .arg("--to")
        .arg("json")
        .arg(&dumped)
        .arg(dir.path().join("summary.json"))
        .output()
        .expect("run trust-ir");
    assert!(!out.status.success(), "a #lossy dump must not convert back");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("printed LOSSILY"), "{stderr}");
}
