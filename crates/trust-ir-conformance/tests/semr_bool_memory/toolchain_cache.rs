// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Both native compilers must keep working over the same canonical sources.
//! A successful 4.30 proof build cannot invalidate the standing 4.8 oracle.

use super::{LEAN_COMPONENT, command, lake};
use serde_json::json;
use std::fs;
use std::path::Path;
use std::process::Output;
use trust_ir::inst::BinOp;
use trust_ir::ty::Ty;
use trust_ir_build::ModuleBuilder;

fn succeeded(output: Output, what: &str) -> String {
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "{what} failed:\n{text}");
    text
}

fn run_oracle(legacy: &Path) {
    let mut module = ModuleBuilder::new("toolchain_cache_control");
    let signature = module.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut function = module.function("subtract", signature);
    let entry = function.create_block();
    let left = function.add_block_param(entry, Ty::I32);
    let right = function.add_block_param(entry, Ty::I32);
    function.switch_to_block(entry);
    let difference = function.binop(BinOp::Sub, Ty::I32, left, right);
    function.ret(vec![difference]);
    let id = function.build();
    let module = module
        .build()
        .expect("validated oracle cache-control module");
    let request = json!({
        "fuel": 10_000, "call_depth": 64,
        "batches": [{"module": module, "runs": [
            {"function": id.0, "args": [
                {"int": {"width": 32, "raw": "9"}},
                {"int": {"width": 32, "raw": "6"}}
            ]},
            {"function": id.0, "args": [
                {"int": {"width": 32, "raw": "6"}},
                {"int": {"width": 32, "raw": "9"}}
            ]}
        ]}]
    });
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "toolchain-cache-oracle-{}.json",
        std::process::id()
    ));
    fs::create_dir_all(path.parent().unwrap()).expect("owned oracle request directory");
    fs::write(&path, serde_json::to_vec(&request).unwrap()).expect("write actual oracle request");
    let reply = succeeded(
        std::process::Command::new(legacy.join(".lake/build/bin/trustir_eval"))
            .arg(&path)
            .output()
            .expect("run actual native oracle request"),
        "native oracle request",
    );
    let reply: serde_json::Value = serde_json::from_str(&reply).expect("typed oracle response");
    assert_eq!(
        reply,
        json!([[
            {"ok": {"graph": {"version": 2, "nodes": [["int", 32, "3"]], "roots": [0]}}},
            {"ok": {"graph": {"version": 2, "nodes": [["int", 32, "4294967293"]], "roots": [0]}}}
        ]])
    );
}

#[test]
fn semr_proof_build_preserves_the_pinned_legacy_oracle_cache() {
    let _guard = LEAN_COMPONENT
        .lock()
        .expect("previous Lean component check passed");
    let Some(lake) = lake() else {
        assert_ne!(
            std::env::var("TRUST_IR_REQUIRE_LEAN").as_deref(),
            Ok("1"),
            "both pinned Lean compilers are required"
        );
        eprintln!("SKIPPED: the cross-version cache control needs Lake");
        return;
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean");
    let legacy = root.join("trust_ir-semantics");
    let proof = root.join("semr-memory");
    for (package, version) in [(&legacy, "4.8.0"), (&proof, "4.30.0-rc2")] {
        let actual = succeeded(
            command(&lake, package)
                .arg("--version")
                .output()
                .expect("native Lake version"),
            "package compiler selection",
        );
        assert!(
            actual.contains(&format!("Lean version {version})")),
            "use a native version-aware Lake frontend for each package pin; got {actual}"
        );
    }
    succeeded(
        command(&lake, &legacy)
            .args(["build", "trustir_eval"])
            .output()
            .expect("legacy oracle build"),
        "initial 4.8 oracle build",
    );
    run_oracle(&legacy);
    let artifacts: Vec<_> = [
        ".lake/build/lib/TrustIr/Semantics/Memory.olean",
        ".lake/build/ir/TrustIr/Semantics/Memory.c",
    ]
    .into_iter()
    .map(|relative| {
        let path = legacy.join(relative);
        let bytes = fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        (path, bytes)
    })
    .collect();
    succeeded(
        command(&lake, &proof)
            .args(["build", "SemRBoolMemory"])
            .output()
            .expect("4.30 proof build"),
        "intervening 4.30 proof build",
    );
    succeeded(
        command(&lake, &proof)
            .args(["env", "lean", "SemRBoolMemory.lean"])
            .output()
            .expect("load actual 4.30 proof imports"),
        "4.30 proof import load",
    );
    for (path, before) in artifacts {
        let after = fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        assert_eq!(
            before,
            after,
            "4.30 overwrote the pinned 4.8 artifact {}",
            path.display()
        );
    }
    succeeded(
        command(&lake, &legacy)
            .args(["build", "trustir_eval"])
            .output()
            .expect("legacy oracle rebuild"),
        "4.8 oracle build after 4.30 without cleanup",
    );
    // A warm executable/build may survive while lib/lean from the other
    // compiler shadows the core Lean namespace. Elaborate the actual oracle
    // root again; do not count reuse of that old native binary as an import
    // compatibility check.
    succeeded(
        command(&lake, &legacy)
            .args(["env", "lean", "TrustIrEval/Main.lean"])
            .output()
            .expect("load actual 4.8 oracle imports after 4.30"),
        "4.8 oracle import load after 4.30 without cleanup",
    );
    run_oracle(&legacy);
    let ready = std::process::Command::new(legacy.join(".lake/build/bin/trustir_eval"))
        .output()
        .expect("run the rebuilt native 4.8 oracle");
    assert_eq!(ready.status.code(), Some(2), "native oracle usage status");
    assert_eq!(
        String::from_utf8_lossy(&ready.stderr).trim(),
        "usage: trustir_eval <request.json>"
    );
}
