// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir validate --lineage` — the standing
//! lineage-closure CI gate (bootstrap-trust-model.md sketch item 2).

mod common;

use std::fs;
use std::path::{Path, PathBuf};

use tempfile::tempdir;

use common::{
    build_lineage_closed_fixture, build_lineage_misthreaded_fixture,
    build_lineage_opaque_smt_fixture, build_lineage_trusted_rung_fixture, trust_ir_cmd,
};
use trust_ir::proof::ProofLineageManifest;

/// Write the module as a `.tmbc` and the manifest as a `.tmpl` sidecar into
/// `dir`, returning both paths.
fn write_fixture(
    dir: &Path,
    module: &trust_ir::Module,
    manifest: &ProofLineageManifest,
) -> (PathBuf, PathBuf) {
    let module_path = dir.join("module.tmbc");
    fs::write(
        &module_path,
        trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
    )
    .expect("write module");
    let manifest_path = dir.join("lineage.tmpl");
    fs::write(
        &manifest_path,
        trust_ir::binary::serialize_proof_lineage_manifest(manifest),
    )
    .expect("write manifest");
    (module_path, manifest_path)
}

#[test]
fn closed_lineage_passes() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = build_lineage_closed_fixture();
    let (module_path, manifest_path) = write_fixture(dir.path(), &module, &manifest);

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(&manifest_path)
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "closed lineage must exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("lineage: closed"),
        "stdout should report the closed verdict, got: {stdout}"
    );
}

#[test]
fn opaque_smt_lineage_fails_without_replay_authority() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = build_lineage_opaque_smt_fixture();
    let (module_path, manifest_path) = write_fixture(dir.path(), &module, &manifest);

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(&manifest_path)
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(1),
        "opaque proof bytes must not close lineage\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("was not replayed by this validator") && stderr.contains("opaque evidence"),
        "stderr should identify the missing replay authority, got: {stderr}"
    );
}

#[test]
fn trusted_rung_open_lineage_fails() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = build_lineage_trusted_rung_fixture();
    let (module_path, manifest_path) = write_fixture(dir.path(), &module, &manifest);

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(&manifest_path)
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(1),
        "a faith-stamped rung must exit 1\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("lineage check failed"),
        "stderr should announce the lineage failure, got: {stderr}"
    );
    assert!(
        stderr.contains("faith-stamped (Trusted)") && stderr.contains("hand-checked by reviewer"),
        "stderr should name the Trusted rung and its justification, got: {stderr}"
    );
}

#[test]
fn misthreaded_lineage_fails() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = build_lineage_misthreaded_fixture();
    let (module_path, manifest_path) = write_fixture(dir.path(), &module, &manifest);

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(&manifest_path)
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(1),
        "a mis-threaded chain must exit 1\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    // The digest mismatch is caught by `validate_against` (structural
    // validation), not by the closure walk — the flag must run both.
    assert!(
        stderr.contains("does not match dependency"),
        "stderr should report the dependency digest mismatch, got: {stderr}"
    );
}

#[test]
fn json_manifest_sidecar_accepted() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = build_lineage_closed_fixture();
    let module_path = dir.path().join("module.tmbc");
    fs::write(
        &module_path,
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
    )
    .expect("write module");
    let manifest_path = dir.path().join("lineage.json");
    fs::write(
        &manifest_path,
        serde_json::to_vec_pretty(&manifest).expect("json"),
    )
    .expect("write manifest");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(&manifest_path)
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "closed lineage via .json sidecar must exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("lineage: closed"),
        "stdout should report the closed verdict, got: {stdout}"
    );
}

#[test]
fn missing_manifest_file_exits_io_error() {
    let dir = tempdir().expect("tempdir");
    let (module, _) = build_lineage_closed_fixture();
    let module_path = dir.path().join("module.tmbc");
    fs::write(
        &module_path,
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
    )
    .expect("write module");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--lineage")
        .arg(dir.path().join("nonexistent.tmpl"))
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(2),
        "unreadable manifest is an I/O error\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("error:"),
        "expected error message, got: {stderr}"
    );
}

#[test]
fn without_lineage_flag_behavior_unchanged() {
    // The same open-lineage module validates cleanly when --lineage is not
    // passed: the gate is opt-in and the default verdict is untouched.
    let dir = tempdir().expect("tempdir");
    let (module, _) = build_lineage_trusted_rung_fixture();
    let module_path = dir.path().join("module.tmbc");
    fs::write(
        &module_path,
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
    )
    .expect("write module");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "without --lineage the verdict must be unchanged\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// WS1.4 (F-005, c04 CLI layer): `plus(a,b) = a*b + a`, `minus(a,b) = a*b - a`,
/// `top(a,b) = plus(a,b) + 7`, with `plus` (obligation 0) and `top`
/// (obligation 1) kernel-certified by the public minter and `top` grounded by
/// `InheritedFromCallee{plus, #0}`. With `retarget`, `top`'s call is moved to
/// `minus` after certification and the inheritance row is left alone.
fn tv_composition_fixture(retarget: bool) -> (trust_ir::Module, ProofLineageManifest) {
    use trust_ir::proof::{
        ProofCertificate, ProofEvidence, ProofLineageId, ProofTransform, ProofTransformStage,
    };
    use trust_ir::ty::Ty;
    use trust_ir::value::ProofId;
    use trust_ir::{BodyGate, Inst, Producer};

    let mut mb = trust_ir_build::ModuleBuilder::new("cli_tv_callee_binding");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut leaf = |name: &str, op: trust_ir::inst::BinOp| {
        let mut f = mb.function(name, sig);
        let e = f.create_block();
        let a = f.add_block_param(e, Ty::U64);
        let b = f.add_block_param(e, Ty::U64);
        f.switch_to_block(e);
        let p = f.mul(Ty::U64, a, b);
        let r = f.binop(op, Ty::U64, p, a);
        f.ret(vec![r]);
        f.build()
    };
    let plus = leaf("plus", trust_ir::inst::BinOp::Add);
    let minus = leaf("minus", trust_ir::inst::BinOp::Sub);
    let mut f = mb.function("top", sig);
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let b = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let c = f.call(plus, vec![a, b]);
    let k = f.iconst(Ty::U64, 7);
    let r = f.add(Ty::U64, c, k);
    f.ret(vec![r]);
    let top = f.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    for function in &mut module.functions {
        function.body_gate = Some(BodyGate::Gated {
            authority: "clean-kernel-tv".to_string(),
            evidence: None,
        });
    }
    let mut manifest = ProofLineageManifest::new();
    for (index, function) in [plus, top].into_iter().enumerate() {
        let id = u32::try_from(index).expect("two rungs");
        let (node, obligation, certificate) = trust_ir_build::certify_identity_lineage_rung(
            &module,
            ProofLineageId::new(id),
            ProofId::new(id),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "identity",
                "trust-ir-cli-test",
                "1.0.0",
            ),
            function,
        )
        .expect("fixture is in the backend-TV fragment");
        module.proof_obligations.push(obligation);
        module.proof_certificates.push(certificate);
        manifest.roots.push(node.id);
        manifest.nodes.push(node);
    }
    module.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(1),
        prover: "clean-backend-tv-compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: plus,
            obligation: ProofId::new(0),
            external: None,
        },
        assurance: None,
    });
    if retarget {
        let caller = module
            .functions
            .iter_mut()
            .find(|function| function.id == top)
            .expect("top exists");
        for node in &mut caller.blocks[0].body {
            if let Inst::Call { callee, .. } = &mut node.inst {
                *callee = minus;
            }
        }
    }
    (module, manifest)
}

fn validate_strict_lineage(module_path: &Path, manifest_path: &Path) -> std::process::Output {
    trust_ir_cmd()
        .args([
            "validate",
            "--format",
            "bin",
            "--forbid-trusted",
            "--forbid-failed",
            "--lineage",
        ])
        .arg(manifest_path)
        .arg(module_path)
        .output()
        .expect("run trust-ir")
}

/// Positive control for the c04 CLI layer: the honest grounded composition
/// passes `validate --forbid-trusted --forbid-failed --lineage`.
#[test]
fn tv_grounded_composition_passes_strict_lineage() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = tv_composition_fixture(false);
    let (module_path, manifest_path) = write_fixture(dir.path(), &module, &manifest);
    let output = validate_strict_lineage(&module_path, &manifest_path);
    assert!(
        output.status.success(),
        "grounded composition must exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Rows `verify.c04.L1` / `verify.c04.L2` (the repro and by-design lenses, CLI
/// layer) — CLOSED: the call retargeted plus→minus after certification is
/// refused by `validate --lineage`, naming the unbound call edge.
#[test]
fn tv_retargeted_call_fails_strict_lineage() {
    let dir = tempdir().expect("tempdir");
    let (module, manifest) = tv_composition_fixture(true);
    let (module_path, manifest_path) = write_fixture(dir.path(), &module, &manifest);
    let output = validate_strict_lineage(&module_path, &manifest_path);
    assert_eq!(
        output.status.code(),
        Some(1),
        "a retargeted certified call must exit 1\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        all.contains(
            "callee `minus` (fn#1) is called by `top` but no InheritedFromCallee row on \
             obligation #1 names it"
        ),
        "the CLI must name the unbound call edge, got: {all}"
    );
}
