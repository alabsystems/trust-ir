// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS4.19 review: the CLI on a module whose lexical scope table carries an
//! inlining chain link (`ScopeData.inlined_at`).
//!
//! The chain has no binary carrier until its wire batch lands, so every binary
//! writer refuses it — fallibly by name, infallibly by PANIC. A CLI is the
//! place a panic becomes a crash banner, so each command that reaches the
//! writer must refuse by name with the user exit code instead:
//!
//!   * `convert --to bin` names the field and the scope and exits 1; the
//!     three carrying formats still convert (control);
//!   * `digest` reports the module as not encodable, naming the chain;
//!   * `run` of a chain-bearing module with NO import rows executes — there is
//!     nothing to authenticate, so nothing is hashed (before the review it
//!     hashed every input unconditionally and aborted on the chain).

mod common;

use std::fs;

use tempfile::tempdir;
use trust_ir::{InlinedAt, Module, Producer, ScopeData, SourceSpan, Ty};
use trust_ir_build::ModuleBuilder;

use common::trust_ir_cmd;

/// `fn program() -> i64 { island() }` with the island inlined: the add sits
/// in scope #1, inlined from `clean::island::forty_two` at `caller.rs:12:9`.
fn module_with_chain() -> Module {
    let mut mb = ModuleBuilder::new("ws4_19_cli_chain");
    let caller_rs = mb.intern_file("src/caller.rs");
    let island = mb.intern_file("src/island.clean");
    let sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("program", sig);
    fb.set_producer(Producer::TRust);
    fb.set_scopes(vec![
        ScopeData::new(
            None,
            Some(SourceSpan {
                file: caller_rs,
                line: 10,
                col: 1,
            }),
        ),
        ScopeData {
            parent: Some(0),
            span: Some(SourceSpan {
                file: island,
                line: 3,
                col: 1,
            }),
            inlined_at: Some(InlinedAt {
                span: SourceSpan {
                    file: caller_rs,
                    line: 12,
                    col: 9,
                },
                callee: "clean::island::forty_two".into(),
            }),
        },
    ]);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_scope(1);
    let forty = fb.iconst(Ty::I64, 40);
    let two = fb.iconst(Ty::I64, 2);
    let sum = fb.add(Ty::I64, forty, two);
    fb.set_scope(0);
    fb.ret(vec![sum]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(m.first_inlined_scope_chain(), Some((0, 1)));
    m
}

fn stderr(out: &std::process::Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

#[test]
fn convert_to_bin_refuses_a_chain_by_name_and_the_other_formats_carry_it() {
    let dir = tempdir().expect("tempdir");
    let m = module_with_chain();
    let text_path = dir.path().join("chain.trust-ir.txt");
    fs::write(&text_path, format!("{m}")).expect("write text");

    let bin_path = dir.path().join("chain.trust-ir.bin");
    let out = trust_ir_cmd()
        .args(["convert", "--from", "text", "--to", "bin"])
        .arg(&text_path)
        .arg(&bin_path)
        .output()
        .expect("run trust-ir convert");
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    let err = stderr(&out);
    assert!(
        err.contains("inlined_at") && err.contains("lexical scope #1") && err.contains("program"),
        "the refusal names the field, the scope and the function: {err}"
    );
    assert!(!err.contains("panicked"), "a refusal, not a crash: {err}");
    assert!(!bin_path.exists(), "nothing is written on a refusal");

    // Control: json and msgpack carry the chain losslessly through the CLI.
    for (to, ext) in [("json", "json"), ("msgpack", "msgpack")] {
        let out_path = dir.path().join(format!("chain.{ext}"));
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
        assert_eq!(back.functions[0].scopes, m.functions[0].scopes, "{to}");
    }
}

#[test]
fn digest_reports_a_chain_bearing_module_as_not_encodable() {
    let dir = tempdir().expect("tempdir");
    let m = module_with_chain();
    let text_path = dir.path().join("chain.trust-ir.txt");
    fs::write(&text_path, format!("{m}")).expect("write text");
    let out = trust_ir_cmd()
        .arg("digest")
        .arg(&text_path)
        .output()
        .expect("run trust-ir digest");
    assert!(!out.status.success());
    let err = stderr(&out);
    assert!(
        err.contains("module is not encodable") && err.contains("inlined_at"),
        "stderr: {err}"
    );
    assert!(!err.contains("panicked"), "a refusal, not a crash: {err}");
}

#[test]
fn run_executes_a_chain_bearing_module_that_has_no_import_rows() {
    let dir = tempdir().expect("tempdir");
    let m = module_with_chain();
    assert!(m.imports.is_empty());
    let text_path = dir.path().join("chain.trust_ir");
    fs::write(&text_path, format!("{m}")).expect("write text");
    let out = trust_ir_cmd()
        .arg("run")
        .arg(&text_path)
        .output()
        .expect("run trust-ir run");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "42");
}

/// `validate --link <dep>` where the dependency carries a chain: the set it
/// would be indexed into is keyed by `stable_digest`, which the writer refuses
/// — so the dependency is refused by name (exit 1) before anything is hashed,
/// never by a crash. Control: the same dependency without the link is indexed
/// and the subject (no import rows) validates.
#[test]
fn validate_link_refuses_a_chain_bearing_dependency_by_name() {
    let dir = tempdir().expect("tempdir");
    let dep = module_with_chain();
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
        err.contains("no wire identity") && err.contains("inlined_at"),
        "stderr: {err}"
    );
    assert!(!err.contains("panicked"), "a refusal, not a crash: {err}");

    // Control: strip the link and the same command succeeds.
    let mut plain = dep.clone();
    plain.functions[0].scopes.as_mut().expect("scopes")[1].inlined_at = None;
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
