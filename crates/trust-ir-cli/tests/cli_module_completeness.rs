// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS5.3b review: the CLI on a module carrying a completeness claim
//! (`Module.completeness`, F-090).
//!
//! The claim has no binary carrier until its wire batch lands, so every binary
//! writer refuses it — fallibly by name, infallibly by PANIC. A CLI is the
//! place a panic becomes a crash banner, so each command that reaches the
//! writer must refuse by name with the user exit code instead (the WS4.19
//! `ScopeData.inlined_at` precedent, `cli_inlined_scope_chain.rs`):
//!
//!   * `convert --to bin` names the field and exits 1, writing nothing; the
//!     three carrying formats still convert, claim intact (control);
//!   * `digest` reports the module as not encodable, naming the claim;
//!   * `validate --link <dep>` refuses a claim-bearing dependency by name
//!     (it has no wire identity to index or authenticate);
//!   * `validate` and `run` of a claim-bearing module with no import rows
//!     succeed — nothing is hashed, and the claim is not a validation error.

mod common;

use std::fs;

use tempfile::tempdir;
use trust_ir::{Endianness, Module, ModuleCompleteness, Producer, TargetInfo, Ty, UnloweredRow};
use trust_ir_build::ModuleBuilder;

use common::trust_ir_cmd;

/// `fn program() -> i64 { 42 }` lowered, `total` refused and emitted as a
/// bodyless declaration, and the module says so.
fn partial_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(
        "ws5_3b_cli_partial",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        },
    );
    let sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("program", sig);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let forty = fb.iconst(Ty::I64, 40);
    let two = fb.iconst(Ty::I64, 2);
    let sum = fb.add(Ty::I64, forty, two);
    fb.ret(vec![sum]);
    fb.build();
    let total = mb.declare_function("total", sig);
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.function_by_id_mut(total).unwrap().producer = Some(Producer::TRust);
    m.completeness = Some(ModuleCompleteness::Partial(vec![UnloweredRow {
        symbol: "total".into(),
        display_path: Some("q04_heap::total".into()),
        reason: "unsupported shape: Vec<u64> body".into(),
    }]));
    assert!(m.completeness_claim_unencodable());
    m
}

fn stderr(out: &std::process::Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

#[test]
fn convert_to_bin_refuses_a_claim_by_name_and_the_other_formats_carry_it() {
    let dir = tempdir().expect("tempdir");
    for claim in [
        ModuleCompleteness::Complete,
        partial_module().completeness.unwrap(),
    ] {
        let mut m = partial_module();
        m.completeness = Some(claim);
        let text_path = dir.path().join("claim.trust-ir.txt");
        fs::write(&text_path, format!("{m}")).expect("write text");

        let bin_path = dir.path().join("claim.trust-ir.bin");
        let out = trust_ir_cmd()
            .args(["convert", "--from", "text", "--to", "bin"])
            .arg(&text_path)
            .arg(&bin_path)
            .output()
            .expect("run trust-ir convert");
        assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
        let err = stderr(&out);
        assert!(
            err.contains("Module.completeness") && err.contains("no binary encoding"),
            "the refusal names the field: {err}"
        );
        assert!(!err.contains("panicked"), "a refusal, not a crash: {err}");
        assert!(!bin_path.exists(), "nothing is written on a refusal");

        // Control: json and msgpack carry the claim losslessly through the CLI.
        for (to, ext) in [("json", "json"), ("msgpack", "msgpack")] {
            let out_path = dir.path().join(format!("claim.{ext}"));
            let out = trust_ir_cmd()
                .args(["convert", "--from", "text", "--to", to])
                .arg(&text_path)
                .arg(&out_path)
                .output()
                .expect("run trust-ir convert");
            assert!(out.status.success(), "{to}: stderr: {}", stderr(&out));
            let bytes = fs::read(&out_path).expect("read");
            let back: Module = if to == "json" {
                serde_json::from_slice(&bytes).expect("json decode")
            } else {
                rmp_serde::from_slice(&bytes).expect("msgpack decode")
            };
            assert_eq!(back.completeness, m.completeness, "{to}");
        }
    }

    // Control: the same module with NO claim converts to bin — the refusal is
    // about the claim, not the module.
    let mut plain = partial_module();
    plain.completeness = None;
    let text_path = dir.path().join("plain.trust-ir.txt");
    fs::write(&text_path, format!("{plain}")).expect("write text");
    let bin_path = dir.path().join("plain.trust-ir.bin");
    let out = trust_ir_cmd()
        .args(["convert", "--from", "text", "--to", "bin"])
        .arg(&text_path)
        .arg(&bin_path)
        .output()
        .expect("run trust-ir convert");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let back = trust_ir::binary::deserialize_module(&fs::read(&bin_path).expect("read bin"))
        .expect("decode");
    assert_eq!(back.completeness, None, "a decoded blob is NO CLAIM");
}

#[test]
fn digest_reports_a_claim_bearing_module_as_not_encodable() {
    let dir = tempdir().expect("tempdir");
    let m = partial_module();
    let text_path = dir.path().join("claim.trust-ir.txt");
    fs::write(&text_path, format!("{m}")).expect("write text");
    let out = trust_ir_cmd()
        .arg("digest")
        .arg(&text_path)
        .output()
        .expect("run trust-ir digest");
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    let err = stderr(&out);
    assert!(
        err.contains("module is not encodable") && err.contains("Module.completeness"),
        "stderr: {err}"
    );
    assert!(!err.contains("panicked"), "a refusal, not a crash: {err}");
}

#[test]
fn validate_and_run_accept_a_claim_bearing_module_that_has_no_import_rows() {
    let dir = tempdir().expect("tempdir");
    let m = partial_module();
    assert!(m.imports.is_empty());
    let text_path = dir.path().join("claim.trust_ir");
    fs::write(&text_path, format!("{m}")).expect("write text");

    let out = trust_ir_cmd()
        .arg("validate")
        .arg(&text_path)
        .output()
        .expect("run trust-ir validate");
    assert!(out.status.success(), "stderr: {}", stderr(&out));

    let out = trust_ir_cmd()
        .arg("run")
        .arg(&text_path)
        .output()
        .expect("run trust-ir run");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "42");
}

/// `validate --link <dep>` where the dependency carries a claim: the set it
/// would be indexed into is keyed by `stable_digest`, which the writer refuses
/// — so the dependency is refused by name (exit 1), never by a crash.
/// Control: the same dependency without the claim is indexed and the subject
/// validates.
#[test]
fn validate_link_refuses_a_claim_bearing_dependency_by_name() {
    let dir = tempdir().expect("tempdir");
    let dep = partial_module();
    let dep_path = dir.path().join("dep.trust-ir.txt");
    fs::write(&dep_path, format!("{dep}")).expect("write dep");
    let subject = {
        let mut mb = ModuleBuilder::new("subject");
        let sig = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function("main", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let c = fb.iconst(Ty::I64, 1);
        fb.ret(vec![c]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let subject_path = dir.path().join("subject.trust-ir.txt");
    fs::write(&subject_path, format!("{subject}")).expect("write subject");

    let out = trust_ir_cmd()
        .arg("validate")
        .arg("--link")
        .arg(&dep_path)
        .arg(&subject_path)
        .output()
        .expect("run trust-ir validate");
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    let err = stderr(&out);
    assert!(
        err.contains("no wire identity") && err.contains("Module.completeness"),
        "stderr: {err}"
    );
    assert!(!err.contains("panicked"), "a refusal, not a crash: {err}");

    // Control: strip the claim and the same command succeeds.
    let mut plain = dep.clone();
    plain.completeness = None;
    fs::write(&dep_path, format!("{plain}")).expect("write plain dep");
    let out = trust_ir_cmd()
        .arg("validate")
        .arg("--link")
        .arg(&dep_path)
        .arg(&subject_path)
        .output()
        .expect("run trust-ir validate");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
}
