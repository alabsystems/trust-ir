// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! D1a: a construct the binary writer cannot encode is refused BY NAME at
//! every CLI entry point that needs a wire image or a digest — never a panic.
//!
//! The input is ONE edited file: a JSON module whose type table spells the
//! producer-internal `Ty::Error` (`"types": ["Error"]`). JSON and MessagePack
//! can spell it; the binary writer cannot. Before D1a, `convert --to bin`,
//! `validate --link` (dependency and root) and `run` (an input carrying an
//! import row) all reached the writer's `Ty::Error` arm and exited 101 with a
//! panic banner, because every hand-written pre-check omitted `Ty::Error`.
//! The pre-check is now the writer itself in check mode
//! (`Module::wire_image_refusal`), so it cannot omit a construct the writer
//! refuses (`docs/SPEC_RATIFICATIONS.md`, "A construct or count with no wire
//! image is refused by the writer's own arm, at every trust-ir entry point").
//!
//! Each test asserts the exit code, that stderr names the construct, and that
//! no panic banner appears. Test rung: evidence on these inputs, not proof.

mod common;

use std::fs;
use std::path::PathBuf;
use std::process::Output;

use tempfile::{TempDir, tempdir};

use common::{build_valid_module, trust_ir_cmd};
use trust_ir::proof::ProofDigest;
use trust_ir::ty::Ty;
use trust_ir::{Module, ModuleImport};
use trust_ir_build::ModuleBuilder;

#[path = "../../trust-ir-conformance/tests/generate/signature_abi.rs"]
mod abi_fixture;

/// The user-error exit code (`EXIT_USER` in `src/main.rs`).
const EXIT_USER: i32 = 1;
/// Rust's exit code for a panicking `main`.
const EXIT_PANIC: i32 = 101;

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

fn write(dir: &TempDir, name: &str, bytes: &[u8]) -> PathBuf {
    let path = dir.path().join(name);
    fs::write(&path, bytes).expect("write fixture");
    path
}

/// `identity(x: u16) -> u16`, built through the builder (so it is valid).
fn identity_module(name: &str) -> Module {
    let mut mb = ModuleBuilder::new(name);
    let ft = mb.add_func_type(vec![Ty::U16], vec![Ty::U16]);
    let mut fb = mb.function("identity", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U16);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The ONE edit: every `U16` of `module`'s JSON spelling becomes the
/// producer-internal `Error`.
fn json_with_producer_internal_type(module: &Module) -> Vec<u8> {
    let json = serde_json::to_string(module).expect("json encode");
    assert!(json.contains("\"U16\""), "{json}");
    json.replace("\"U16\"", "\"Error\"").into_bytes()
}

fn assert_named_refusal(out: &Output, what: &str) {
    let err = stderr(out);
    assert_ne!(
        out.status.code(),
        Some(EXIT_PANIC),
        "{what}: a refusal, never a panic: {err}"
    );
    assert_eq!(out.status.code(), Some(EXIT_USER), "{what}: {err}");
    assert!(!err.contains("panicked"), "{what}: no panic banner: {err}");
    assert!(
        err.contains("Ty::Error"),
        "{what}: names the construct: {err}"
    );
}

/// T-A1. `convert --to bin` of a module the writer cannot encode is a user
/// error naming `Ty::Error`, and writes nothing.
#[test]
fn convert_refuses_a_producer_internal_type_by_name() {
    let dir = tempdir().expect("tempdir");
    let input = write(
        &dir,
        "err.json",
        &json_with_producer_internal_type(&identity_module("err")),
    );
    let output = dir.path().join("err.trust-ir.bin");
    let out = trust_ir_cmd()
        .args(["convert", "--from", "json", "--to", "bin"])
        .arg(&input)
        .arg(&output)
        .output()
        .expect("run trust-ir convert");
    assert_named_refusal(&out, "convert");
    assert!(!output.exists(), "nothing is written on a refusal");

    // Control: the unedited module converts.
    let control = write(
        &dir,
        "ok.json",
        &serde_json::to_vec(&identity_module("ok")).expect("json"),
    );
    let out = trust_ir_cmd()
        .args(["convert", "--from", "json", "--to", "bin"])
        .arg(&control)
        .arg(dir.path().join("ok.trust-ir.bin"))
        .output()
        .expect("run trust-ir convert");
    assert!(out.status.success(), "control: {}", stderr(&out));
}

/// T-A2. `validate --link` keys on the digest of the dependency AND of the
/// root; a `Ty::Error` on either side is `ModuleHasNoWireIdentity`, by name.
#[test]
fn validate_link_refuses_a_producer_internal_type_by_name() {
    let dir = tempdir().expect("tempdir");
    let err = write(
        &dir,
        "err.json",
        &json_with_producer_internal_type(&identity_module("err")),
    );
    let control = write(
        &dir,
        "control.json",
        &serde_json::to_vec(&build_valid_module()).expect("json"),
    );

    // The dependency carries the construct.
    let out = trust_ir_cmd()
        .args(["validate", "--format", "json", "--link"])
        .arg(&err)
        .arg(&control)
        .output()
        .expect("run trust-ir validate --link");
    assert_named_refusal(&out, "validate --link <dependency>");
    assert!(
        stderr(&out).contains("has no wire identity"),
        "{}",
        stderr(&out)
    );

    // The root carries it.
    let out = trust_ir_cmd()
        .args(["validate", "--format", "json", "--link"])
        .arg(&control)
        .arg(&err)
        .output()
        .expect("run trust-ir validate --link");
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), stderr(&out));
    assert_ne!(out.status.code(), Some(EXIT_PANIC), "root: {text}");
    assert_eq!(out.status.code(), Some(EXIT_USER), "root: {text}");
    assert!(!text.contains("panicked"), "root: {text}");
    assert!(
        text.contains("ModuleHasNoWireIdentity") && text.contains("Ty::Error"),
        "root: ModuleHasNoWireIdentity names the construct: {text}"
    );
}

/// `run` hashes every input once an input carries an import row; an input
/// the writer cannot encode is refused by name before any hashing.
#[test]
fn run_refuses_a_producer_internal_type_before_hashing_imports() {
    let dir = tempdir().expect("tempdir");
    let mut module = identity_module("err");
    module
        .intern_import(ModuleImport::new("dep", ProofDigest::sha256([7; 32])))
        .expect("Module::intern_import: test fixture");
    let input = write(&dir, "err.json", &json_with_producer_internal_type(&module));
    let out = trust_ir_cmd()
        .args(["run", "--format", "json"])
        .arg(&input)
        .args(["--entry", "identity", "--arg", "1"])
        .output()
        .expect("run trust-ir run");
    assert_named_refusal(&out, "run");
    assert!(
        stderr(&out).contains("has no wire identity"),
        "{}",
        stderr(&out)
    );
}

/// `convert --to bin` of a module whose typed signature ABI (wire v60) is
/// past its encoding limits is a user error naming the descriptor: the
/// writer's own `func_types` arm refuses it, so the one pre-check does. Kind
/// (i): before D1a the CLI's hand-written list did not probe the descriptor
/// and the writer's byte-limit `assert!` exited 101.
#[test]
fn convert_refuses_an_over_limit_signature_abi_by_name() {
    let dir = tempdir().expect("tempdir");
    let mut module = abi_fixture::module().expect("signature_abi::module: test fixture");
    if let Some(abi) = module.func_types[0].abi.as_mut() {
        abi.frontend.revision = "r".repeat(trust_ir::signature_abi::MAX_ABI_TEXT_BYTES + 1);
    }
    let input = write(
        &dir,
        "abi.json",
        &serde_json::to_vec(&module).expect("json"),
    );
    let output = dir.path().join("abi.trust-ir.bin");
    let out = trust_ir_cmd()
        .args(["convert", "--from", "json", "--to", "bin"])
        .arg(&input)
        .arg(&output)
        .output()
        .expect("run trust-ir convert");
    let err = stderr(&out);
    assert_ne!(out.status.code(), Some(EXIT_PANIC), "never a panic: {err}");
    assert_eq!(out.status.code(), Some(EXIT_USER), "{err}");
    assert!(!err.contains("panicked"), "no panic banner: {err}");
    assert!(
        err.contains("signature ABI 0"),
        "names the descriptor: {err}"
    );
    assert!(!output.exists(), "nothing is written on a refusal");

    // Control: the fixture's own descriptor converts.
    let control = write(
        &dir,
        "abi-ok.json",
        &serde_json::to_vec(&abi_fixture::module().expect("signature_abi::module: test fixture"))
            .expect("json"),
    );
    let out = trust_ir_cmd()
        .args(["convert", "--from", "json", "--to", "bin"])
        .arg(&control)
        .arg(dir.path().join("abi-ok.trust-ir.bin"))
        .output()
        .expect("run trust-ir convert");
    assert!(out.status.success(), "control: {}", stderr(&out));
}
