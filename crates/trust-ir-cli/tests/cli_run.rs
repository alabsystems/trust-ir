// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir run` — the multi-module linker + reference
//! interpreter execution front (the emit-each battery oracle).

mod common;

use std::fs;
use std::path::Path;

use tempfile::tempdir;

use common::trust_ir_cmd;

fn write_module(dir: &Path, name: &str, text: &str) {
    fs::write(dir.join(name), text).expect("write module");
}

fn run_dir(dir: &Path) -> std::process::Output {
    trust_ir_cmd()
        .arg("run")
        .arg(dir)
        .output()
        .expect("run trust-ir")
}

#[test]
fn links_declaration_against_definition_across_modules() {
    let dir = tempdir().expect("tempdir");
    // Module A: `program` calls a DECLARED-only @helper.
    write_module(
        dir.path(),
        "a.trust_ir",
        r#"; TrustIr text format v1
module "a"

functy.0 = (i64) -> (i64)

functy.1 = () -> (i64)

fn @helper(functy.0) {
}

fn @program(functy.1) {
bb0:
    %1 = const i64 41
    %2 = call @func.0(%1)
    ret %2
}
"#,
    );
    // Module B: the definition of @helper (adds 1).
    write_module(
        dir.path(),
        "b.trust_ir",
        r#"; TrustIr text format v1
module "b"

functy.0 = (i64) -> (i64)

fn @helper(functy.0) {
bb0(%0: i64):
    %1 = const i64 1
    %2 = add i64 %0, %1
    ret %2
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "42");
}

#[test]
fn conflicting_definitions_are_a_link_error() {
    let dir = tempdir().expect("tempdir");
    let def = |value: i64| {
        format!(
            r#"; TrustIr text format v1
module "m{value}"

functy.0 = () -> (i64)

fn @helper(functy.0) {{
bb0:
    %1 = const i64 {value}
    ret %1
}}
"#
        )
    };
    write_module(dir.path(), "a.trust_ir", &def(1));
    write_module(dir.path(), "b.trust_ir", &def(2));
    // A `program` entry so resolution gets past loading.
    write_module(
        dir.path(),
        "c.trust_ir",
        r#"; TrustIr text format v1
module "c"

functy.0 = () -> (i64)

fn @program(functy.0) {
bb0:
    %1 = const i64 0
    ret %1
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("conflicting definitions of @helper"),
        "stderr: {stderr}"
    );
}

#[test]
fn identical_duplicate_definitions_are_deduped() {
    let dir = tempdir().expect("tempdir");
    let def = r#"; TrustIr text format v1
module "m"

functy.0 = () -> (i64)

fn @helper(functy.0) {
bb0:
    %1 = const i64 5
    ret %1
}
"#;
    write_module(dir.path(), "a.trust_ir", def);
    write_module(dir.path(), "b.trust_ir", def);
    write_module(
        dir.path(),
        "c.trust_ir",
        r#"; TrustIr text format v1
module "c"

functy.0 = () -> (i64)

functy.1 = () -> (i64)

fn @helper(functy.0) {
}

fn @program(functy.1) {
bb0:
    %1 = call @func.0()
    ret %1
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "5");
}

#[test]
fn calling_a_bodyless_extern_traps_with_its_name() {
    let dir = tempdir().expect("tempdir");
    write_module(
        dir.path(),
        "t.trust_ir",
        r#"; TrustIr text format v1
module "t"

functy.0 = () -> ()

functy.1 = () -> (i64)

fn @mystery_extern(functy.0) {
}

fn @program(functy.1) {
bb0:
    call @func.0()
    %1 = const i64 7
    ret %1
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("trap: reached extern builtin stub @mystery_extern"),
        "stderr: {stderr}"
    );
}

#[test]
fn bool_icmp_is_legalized_and_executes() {
    let dir = tempdir().expect("tempdir");
    // `icmp eq bool` is valid format-side but outside the interpreter's
    // integer comparator; `run` legalizes it into selects.
    write_module(
        dir.path(),
        "m.trust_ir",
        r#"; TrustIr text format v1
module "m"

functy.0 = () -> (i64)

fn @program(functy.0) {
bb0:
    %1 = const bool true
    %2 = const bool false
    %3 = icmp eq bool %1, %2
    %4 = const bool true
    %5 = icmp eq bool %4, %4
    %6 = const i64 10
    %7 = const i64 1
    %8 = select i64 %3, %6, %7
    %9 = const i64 100
    %10 = select i64 %5, %9, %7
    %11 = add i64 %8, %10
    ret %11
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    // eq(true,false) = false -> 1; eq(true,true) = true -> 100.
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "101");
}

#[test]
fn rust_alloc_builtin_maps_to_interpreter_heap() {
    let dir = tempdir().expect("tempdir");
    write_module(
        dir.path(),
        "m.trust_ir",
        r#"; TrustIr text format v1
module "m"

functy.0 = (u64, u64) -> (ptr)

functy.1 = (ptr, u64, u64) -> ()

functy.2 = () -> (i64)

fn @_RNvCsoF1AqU8Qvp_7___rustc12___rust_alloc(functy.0) {
}

fn @_RNvCsoF1AqU8Qvp_7___rustc14___rust_dealloc(functy.1) {
}

fn @program(functy.2) {
bb0:
    %1 = const u64 16
    %2 = const u64 8
    %3 = call @func.0(%1, %2)
    %4 = const i64 12345
    store i64 %4, ptr %3
    %5 = load i64, ptr %3
    call @func.1(%3, %1, %2)
    ret %5
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "12345");
}

#[test]
fn missing_entry_is_a_user_error() {
    let dir = tempdir().expect("tempdir");
    write_module(
        dir.path(),
        "m.trust_ir",
        r#"; TrustIr text format v1
module "m"

functy.0 = () -> (i64)

fn @not_program(functy.0) {
bb0:
    %1 = const i64 3
    ret %1
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("no function named @program"),
        "stderr: {stderr}"
    );

    // The same image runs with an explicit --entry.
    let out = trust_ir_cmd()
        .arg("run")
        .arg(dir.path())
        .arg("--entry")
        .arg("not_program")
        .output()
        .expect("run trust-ir");
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "3");
}
