// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS5.4 (5): `trust-ir discharge --bvblast IN OUT` (feature `ay`).
//!
//! Run with `targo --unverified test -p trust-ir-cli --features ay --test
//! cli_discharge`; without the feature this target compiles to nothing.
#![cfg(feature = "ay")]

use std::path::Path;
use std::process::Command;

use trust_ir::Module;
use trust_ir::inst::{BinOp, OverflowOp};
use trust_ir::proof::{ObligationKind, ObligationSite, ProofObligation, ProofStatus};
use trust_ir::ty::Ty;
use trust_ir::value::ProofId;
use trust_ir_build::ModuleBuilder;

/// The direct lane's checked `u64` add, optionally range-guarded, with one
/// Pending `ArithmeticSafety` row sited on its `assert`.
fn checked_add(guard: bool) -> Module {
    let mut mb = ModuleBuilder::new("cli_discharge");
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let func = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut fb = mb.function("checked_add", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let (x, y) = if guard {
        let m = fb.iconst(Ty::U64, 0xff);
        (
            fb.binop(BinOp::And, Ty::U64, a, m),
            fb.binop(BinOp::And, Ty::U64, b, m),
        )
    } else {
        (a, b)
    };
    let (r, o) = fb.overflow(OverflowOp::AddOverflow, Ty::U64, x, y);
    let f = fb.bool_const(false);
    let t = fb.bool_const(true);
    let c = fb.select(Ty::Bool, o, f, t);
    fb.assert(c);
    let (block, index) = fb.last_emitted_position().unwrap();
    fb.ret(vec![r]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::ArithmeticSafety,
            ProofStatus::Pending,
            "checked add",
        )
        .with_function(func)
        .with_site(ObligationSite::new(func, block, index)),
    );
    module
}

fn run(args: &[&str]) -> (i32, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_trust-ir"))
        .args(args)
        .output()
        .expect("run trust-ir");
    (
        out.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

fn write(dir: &Path, name: &str, module: &Module) -> String {
    let path = dir.join(name);
    std::fs::write(
        &path,
        trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
    )
    .unwrap();
    path.to_str().unwrap().to_string()
}

#[test]
fn discharge_writes_a_separate_artifact_valid_only_under_the_authority() {
    let dir = tempfile::tempdir().unwrap();
    let input = write(dir.path(), "in.tmbc", &checked_add(true));
    let output = dir.path().join("out.tmbc");
    let before = std::fs::read(&input).unwrap();

    let (code, stdout, stderr) = run(&["discharge", "--bvblast", &input, output.to_str().unwrap()]);
    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    assert!(
        stdout.contains("1 of 1 in-scope obligation(s) discharged"),
        "{stdout}"
    );

    // The input is untouched: it stays the Pending module.
    assert_eq!(std::fs::read(&input).unwrap(), before);

    let discharged =
        trust_ir::binary::deserialize_module(&std::fs::read(&output).unwrap()).unwrap();
    assert_eq!(
        discharged.proof_obligations[0].status,
        ProofStatus::Discharged
    );
    // Provenance: the certificate names the ay revision this build links.
    assert_eq!(
        discharged.proof_certificates[0].prover,
        format!("trust-ir-ay/bvblast@{}", trust_ir_ay::vc::AY_REV)
    );
    // Structural `validate` (no authority) refuses the replay-less Discharged row.
    let (code, stdout, _) = run(&["validate", "--no-giveback", output.to_str().unwrap()]);
    assert_eq!(code, 1, "{stdout}");
}

#[test]
fn an_unprovable_row_is_reported_and_left_pending() {
    let dir = tempfile::tempdir().unwrap();
    let input = write(dir.path(), "in.tmbc", &checked_add(false));
    let output = dir.path().join("out.tmbc");
    let (code, stdout, stderr) = run(&["discharge", "--bvblast", &input, output.to_str().unwrap()]);
    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    assert!(stdout.contains("0 of 1"), "{stdout}");
    assert!(stdout.contains("not provable locally"), "{stdout}");
    let module = trust_ir::binary::deserialize_module(&std::fs::read(&output).unwrap()).unwrap();
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Pending);
    assert!(module.proof_certificates.is_empty());
}

#[test]
fn discharge_refuses_to_overwrite_its_input_or_run_without_a_route() {
    let dir = tempfile::tempdir().unwrap();
    let input = write(dir.path(), "in.tmbc", &checked_add(true));
    let before = std::fs::read(&input).unwrap();
    let (code, _, stderr) = run(&["discharge", "--bvblast", &input, &input]);
    assert_eq!(code, 1);
    assert!(stderr.contains("refusing to write the discharged artifact over its input"));
    assert_eq!(std::fs::read(&input).unwrap(), before);

    let output = dir.path().join("out.tmbc");
    let (code, _, stderr) = run(&["discharge", &input, output.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(stderr.contains("--bvblast"), "{stderr}");
    assert!(!output.exists());
}

/// ADVERSARIAL (review): an input that already carries a forged `Discharged`
/// row — no certificate the authority can replay — is not laundered into a
/// discharged artifact. The discharge route leaves non-Pending rows alone, the
/// authority refuses the forgery, and NOTHING is written.
#[test]
fn a_forged_discharged_row_in_the_input_is_refused_and_nothing_is_written() {
    let dir = tempfile::tempdir().unwrap();
    // The UNguarded add: its assert is not provable, so only a forgery could
    // make the row Discharged.
    let mut forged = checked_add(false);
    forged.proof_obligations[0].status = ProofStatus::Discharged;
    let input = write(dir.path(), "forged.tmbc", &forged);
    let output = dir.path().join("out.tmbc");
    let (code, stdout, stderr) = run(&["discharge", "--bvblast", &input, output.to_str().unwrap()]);
    assert_eq!(code, 1, "stdout: {stdout}\nstderr: {stderr}");
    assert!(
        stderr.contains("does not validate under BvBlastAuthority"),
        "{stderr}"
    );
    assert!(!output.exists(), "a refused module must never be written");
}
