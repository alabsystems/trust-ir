// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `trust-ir validate` holds a BINARY input to the v41 producer conformance
//! rule ([`trust_ir::BodyGate`]) against the header version the blob
//! declared, and SAYS when it cannot (text / JSON / MessagePack carry no wire
//! version). The library twin is `trust-ir-build/tests/decoded_wire_provenance.rs`,
//! which is `binary`-gated and runs under `--all-features` only; this file
//! is the STANDING-gate lane (gate 3, `test -p trust-ir-cli`), so every
//! boundary the rule has — v38, v40 (the last version before the tag), v41,
//! the declaration cut, the writer's re-emission property, a `--link`
//! dependency, and the transcoder residual — is pinned here as well.

mod common;

use std::fs;

use tempfile::tempdir;
use trust_ir::binary::{
    BASE_FORMAT_VERSION, CONTAINER_VTABLE_FORMAT_VERSION, CONTRACT_SURFACE_FORMAT_VERSION,
};
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::{FatPtrKind, FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId};
use trust_ir::{
    Block, BodyGate, CallingConv, Endianness, Function, Linkage, Module, ModuleImport, Producer,
    TargetInfo,
};

use common::trust_ir_cmd;

fn stdout(out: &std::process::Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &std::process::Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// One nullary function `f` with NO `body_gate` claim: bodied unless
/// `declaration`. `at_v41` adds a `display_path` (a v41 feature), so the
/// writer selects v41 without touching the license.
fn module(name: &str, declaration: bool, at_v41: bool) -> Module {
    let mut module = Module::new(name);
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", signature, BlockId::new(0));
    f.linkage = Linkage::External;
    f.calling_conv = CallingConv::Rust;
    f.body_gate = None;
    if !declaration {
        let mut block = Block::new(BlockId::new(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(block);
    }
    if at_v41 {
        f.display_path = Some("crate::f".into());
    }
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    module
}

fn validate(path: &std::path::Path) -> std::process::Output {
    trust_ir_cmd()
        .arg("validate")
        .arg(path)
        .arg("--no-giveback")
        .output()
        .expect("run trust-ir validate")
}

#[test]
fn a_v41_blob_with_a_bodied_unlicensed_function_is_refused() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("v41_bodied_none.tmbc");
    let bytes = trust_ir::binary::serialize_module(&module("v41_bodied_none", false, true))
        .expect("serialize_module: test fixture");
    assert_eq!(
        &bytes[8..12],
        &CONTRACT_SURFACE_FORMAT_VERSION.to_le_bytes()
    );
    fs::write(&path, bytes).expect("write");

    let out = validate(&path);
    let err = stderr(&out);
    assert_eq!(
        out.status.code(),
        Some(1),
        "stdout: {}\nstderr: {err}",
        stdout(&out)
    );
    assert!(err.contains("validation failed"), "stderr: {err}");
    assert!(
        err.contains("ProducerOmittedBodyGate") && err.contains("wire_version: 41"),
        "the refusal is the named producer-side variant with the declared version: {err}"
    );
    assert!(
        !err.contains("UnlicensedBodyForCodegen"),
        "plain validate is not the codegen pass: {err}"
    );
}

#[test]
fn the_same_content_in_a_pre_v41_blob_is_grandfathered() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("v38_bodied_none.tmbc");
    let bytes = trust_ir::binary::serialize_module(&module("v38_bodied_none", false, false))
        .expect("serialize_module: test fixture");
    assert_eq!(&bytes[8..12], &BASE_FORMAT_VERSION.to_le_bytes());
    fs::write(&path, bytes).expect("write");

    let out = validate(&path);
    let text = stdout(&out);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
    assert!(text.contains("module is well-formed"), "stdout: {text}");
    assert!(
        text.contains("decoded provenance:")
            && text.contains("v38 blob")
            && text.contains("pre-v41")
            && text.contains("does not apply"),
        "the grandfathering is stated, not silent: {text}"
    );
}

#[test]
fn a_bodyless_declaration_at_v41_is_accepted_and_the_check_is_reported() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("v41_declaration_none.tmbc");
    let bytes = trust_ir::binary::serialize_module(&module("v41_declaration_none", true, true))
        .expect("serialize_module: test fixture");
    assert_eq!(
        &bytes[8..12],
        &CONTRACT_SURFACE_FORMAT_VERSION.to_le_bytes()
    );
    fs::write(&path, bytes).expect("write");

    let out = validate(&path);
    let text = stdout(&out);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
    assert!(
        text.contains("decoded provenance:")
            && text.contains("v41 blob")
            && text.contains("v41 producer rule checked"),
        "a v41 blob that conforms says the rule was checked: {text}"
    );
}

#[test]
fn a_non_binary_input_states_that_the_rule_is_unchecked() {
    // The SAME module that a v41 blob would fail on, as JSON: there is no wire
    // version, so the run says the rule is UNCHECKED (never "passed") and
    // exits 0 on structural well-formedness alone.
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("v41_bodied_none.json");
    let json = serde_json::to_vec_pretty(&module("v41_bodied_none", false, true)).expect("json");
    fs::write(&path, json).expect("write");

    let out = validate(&path);
    let text = stdout(&out);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
    assert!(text.contains("module is well-formed"), "stdout: {text}");
    assert!(
        text.contains("decoded provenance:")
            && text.contains("carries no wire version")
            && text.contains("UNCHECKED, not passed"),
        "the missing provenance is stated, never skipped: {text}"
    );
    assert!(!stderr(&out).contains("ProducerOmittedBodyGate"));
}

/// The same bodied unlicensed function beside a `ContainerVtable` fat
/// pointer, which raises the header to exactly v40 — the last version before
/// the tag existed — and nothing higher.
fn module_at_v40(name: &str) -> Module {
    let mut m = module(name, false, false);
    m.add_func_type(FuncTy {
        params: vec![Ty::FatPtr(FatPtrKind::ContainerVtable)],
        returns: vec![],
        abi: None,
        is_vararg: false,
    })
    .expect("Module::add_func_type: test fixture");
    m
}

fn convert(from: &str, to: &str, input: &std::path::Path, output: &std::path::Path) {
    let out = trust_ir_cmd()
        .args(["convert", "--from", from, "--to", to])
        .arg(input)
        .arg(output)
        .output()
        .expect("run trust-ir convert");
    assert!(
        out.status.success(),
        "convert {from}->{to}: stdout: {}\nstderr: {}",
        stdout(&out),
        stderr(&out)
    );
}

#[test]
fn the_same_content_in_a_v40_blob_is_grandfathered() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("v40_bodied_none.tmbc");
    let bytes = trust_ir::binary::serialize_module(&module_at_v40("v40_bodied_none"))
        .expect("serialize_module: test fixture");
    assert_eq!(
        &bytes[8..12],
        &CONTAINER_VTABLE_FORMAT_VERSION.to_le_bytes(),
        "the fixture must sit exactly on the boundary"
    );
    fs::write(&path, bytes).expect("write");

    let out = validate(&path);
    let text = stdout(&out);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
    assert!(
        text.contains("decoded provenance:")
            && text.contains("v40 blob")
            && text.contains("pre-v41")
            && text.contains("does not apply"),
        "v40 is grandfathered and says so: {text}"
    );
}

#[test]
fn a_faithful_re_emission_of_pre_v41_content_keeps_its_header() {
    // The retired prose exception as the writer's measured property: a
    // pre-v41 blob transcoded out and back lands at the SAME pre-v41 version,
    // byte-identically, so `validate` grandfathers the re-emission exactly as
    // it did the original. Both boundaries, through the CLI's own transcoder.
    let dir = tempdir().expect("tempdir");
    for (name, m, version) in [
        (
            "v38",
            module("v38_bodied_none", false, false),
            BASE_FORMAT_VERSION,
        ),
        (
            "v40",
            module_at_v40("v40_bodied_none"),
            CONTAINER_VTABLE_FORMAT_VERSION,
        ),
    ] {
        let original = dir.path().join(format!("{name}.tmbc"));
        let json = dir.path().join(format!("{name}.json"));
        let re_emitted = dir.path().join(format!("{name}.re.tmbc"));
        let bytes = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
        assert_eq!(&bytes[8..12], &version.to_le_bytes(), "{name}");
        fs::write(&original, &bytes).expect("write");
        convert("bin", "json", &original, &json);
        convert("json", "bin", &json, &re_emitted);
        assert_eq!(
            fs::read(&re_emitted).expect("read"),
            bytes,
            "{name}: the re-emission is byte-identical, header included"
        );
        let out = validate(&re_emitted);
        let text = stdout(&out);
        assert_eq!(
            out.status.code(),
            Some(0),
            "{name}: stderr: {}",
            stderr(&out)
        );
        assert!(
            text.contains(&format!("v{version} blob")) && text.contains("does not apply"),
            "{name}: the re-emission is grandfathered like the original: {text}"
        );
    }
}

#[test]
fn a_transcoded_module_is_first_checkable_as_binary() {
    // `convert` is a transcoder. A provenance-less input (JSON here) whose
    // bodied function makes no claim beside a v41 feature is UNCHECKED as
    // JSON and REFUSED once it is a v41 blob: the residual made visible at
    // the first point a header exists, with nothing changed in between.
    let dir = tempdir().expect("tempdir");
    let seed = dir.path().join("seed.tmbc");
    let json = dir.path().join("v41_bodied_none.json");
    let blob = dir.path().join("v41_bodied_none.tmbc");
    fs::write(
        &seed,
        trust_ir::binary::serialize_module(&module("v41_bodied_none", false, true))
            .expect("serialize_module: test fixture"),
    )
    .expect("write");
    convert("bin", "json", &seed, &json);

    let out = validate(&json);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
    assert!(
        stdout(&out).contains("UNCHECKED, not passed"),
        "the JSON input is reported unchecked: {}",
        stdout(&out)
    );

    convert("json", "bin", &json, &blob);
    assert_eq!(
        &fs::read(&blob).expect("read")[8..12],
        &CONTRACT_SURFACE_FORMAT_VERSION.to_le_bytes(),
        "the display_path makes the transcoded blob a v41 blob"
    );
    let out = validate(&blob);
    let err = stderr(&out);
    assert_eq!(out.status.code(), Some(1), "stdout: {}", stdout(&out));
    assert!(
        err.contains("ProducerOmittedBodyGate") && err.contains("wire_version: 41"),
        "the transcoded blob is refused by name: {err}"
    );
}

#[test]
fn a_link_dependency_is_held_to_the_producer_rule() {
    // `--link` dependencies are decoded with their own header version and
    // held to the rule exactly as the subject is; before 2026-09-24 they went
    // through the version-dropping loader and were neither refused nor
    // reported. The subject conforms (an `Ungated` claim, an authenticated
    // import row, both modules pinned to one target so the walk can bind
    // them); only the dependency carries the bodied tag-0 at v41.
    let target = || TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    };
    let dir = tempdir().expect("tempdir");
    let mut dep = module("dep", false, true);
    dep.target_info = Some(target());
    dep.functions[0].producer = Some(Producer::TRust);
    let mut root = module("root", false, true);
    root.target_info = Some(target());
    root.functions[0].body_gate = Some(BodyGate::Ungated);
    root.intern_import(
        ModuleImport::new("dep", dep.stable_digest()).with_producer(Producer::TRust),
    )
    .expect("Module::intern_import: test fixture");
    let dep_path = dir.path().join("dep.tmbc");
    let root_path = dir.path().join("root.tmbc");
    fs::write(
        &dep_path,
        trust_ir::binary::serialize_module(&dep).expect("serialize_module: test fixture"),
    )
    .expect("write dep");
    fs::write(
        &root_path,
        trust_ir::binary::serialize_module(&root).expect("serialize_module: test fixture"),
    )
    .expect("write root");

    let out = trust_ir_cmd()
        .arg("validate")
        .arg("--no-giveback")
        .arg("--link")
        .arg(&dep_path)
        .arg(&root_path)
        .output()
        .expect("run trust-ir validate --link");
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert_eq!(out.status.code(), Some(1), "{text}");
    assert!(
        text.contains("validation failed: --link")
            && text.contains("dep.tmbc")
            && text.contains("ProducerOmittedBodyGate")
            && text.contains("wire_version: 41"),
        "the dependency's refusal is reported by path and by name: {text}"
    );

    // The control: the same dependency with the claim stamped links green,
    // so the refusal above is the dependency's provenance and nothing else.
    dep.functions[0].body_gate = Some(BodyGate::Ungated);
    let mut root = module("root", false, true);
    root.target_info = Some(target());
    root.functions[0].body_gate = Some(BodyGate::Ungated);
    root.intern_import(
        ModuleImport::new("dep", dep.stable_digest()).with_producer(Producer::TRust),
    )
    .expect("Module::intern_import: test fixture");
    fs::write(
        &dep_path,
        trust_ir::binary::serialize_module(&dep).expect("serialize_module: test fixture"),
    )
    .expect("write dep");
    fs::write(
        &root_path,
        trust_ir::binary::serialize_module(&root).expect("serialize_module: test fixture"),
    )
    .expect("write root");
    let out = trust_ir_cmd()
        .arg("validate")
        .arg("--no-giveback")
        .arg("--link")
        .arg(&dep_path)
        .arg(&root_path)
        .output()
        .expect("run trust-ir validate --link");
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert_eq!(out.status.code(), Some(0), "{text}");
    assert!(
        text.contains("dep.tmbc is a v41 blob")
            && text.contains("1 bodied function carries a `body_gate` claim"),
        "the dependency's check is reported, not silent: {text}"
    );
}
