// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Integration tests for the `trust-ir-diff` CLI. Exercises the 6 acceptance
// criteria from issue #63:
//
//   1. Identical modules → exit 0, no output
//   2. ID-renumbered modules → exit 0, no output
//   3. Reordered declarations → exit 0, no output
//   4. Added instruction → exit 1, report names exactly that diff
//   5. `--json` emits valid JSON
//   6. `--ignore-proofs` suppresses proof-only diffs
//
// The CLI itself is a thin shell over `trust-ir::diff`; these tests cover
// the end-to-end plumbing (argument parsing, file I/O, exit codes,
// output formatting).

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

use trust_ir::{
    AttrEntry, AttrValue, BinOp, Block, BlockId, CallingConv, DialectInst, FuncId, FuncTy,
    FuncTyId, Function, ICmpOp, Inst, InstrNode, Linkage, Module, ProofAnnotation, Ty, ValueId,
};

fn bin_path() -> PathBuf {
    // `CARGO_BIN_EXE_<name>` is set by cargo test for each binary in the crate.
    PathBuf::from(env!("CARGO_BIN_EXE_trust-ir-diff"))
}

fn write_tmp(name: &str, body: &str) -> PathBuf {
    static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let mut p = std::env::temp_dir();
    // Namespace by PID and a process-wide counter so parallel tests cannot
    // collide. The wall clock alone is NOT enough: on macOS it has microsecond
    // resolution, and two tests writing the same `name` in the same
    // microsecond shared (and then deleted) one file.
    p.push(format!(
        "trust_ir-diff-test-{}-{}-{}-{}.json",
        std::process::id(),
        COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0),
        name
    ));
    let mut f = std::fs::File::create(&p).expect("create tmp");
    f.write_all(body.as_bytes()).expect("write tmp");
    p
}

fn run_cli(args: &[&str]) -> Output {
    Command::new(bin_path())
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("spawn trust_ir-diff")
}

// ---- Module builders ---------------------------------------------------

fn empty_module(name: &str) -> Module {
    let mut m = Module::new(name);
    m.func_types.push(FuncTy {
        params: Vec::new(),
        returns: vec![Ty::I32],
        abi: None,
        is_vararg: false,
    });
    m
}

fn add_simple_return_func(
    m: &mut Module,
    fid: u32,
    fname: &str,
    entry_bid: u32,
    ret_vid: u32,
) -> FuncId {
    let id = FuncId::new(fid);
    let entry = BlockId::new(entry_bid);
    let mut blk = Block::new(entry);
    // Return a constant i32.
    blk.body.push(InstrNode {
        inst: Inst::Const {
            ty: Ty::I32,
            value: trust_ir::Constant::Int(0),
        },
        results: vec![ValueId::new(ret_vid)],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    blk.body.push(InstrNode {
        inst: Inst::Return {
            values: vec![ValueId::new(ret_vid)],
        },
        results: Vec::new(),
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    let mut f = Function::new(id, fname, FuncTyId::new(0), entry);
    f.blocks.push(blk);
    f.calling_conv = CallingConv::C;
    f.linkage = Linkage::External;
    m.functions.push(f);
    id
}

fn add_binop_func(m: &mut Module, fid: u32, fname: &str) -> FuncId {
    let id = FuncId::new(fid);
    let entry = BlockId::new(10);
    let mut blk = Block::new(entry);
    blk.body.push(InstrNode {
        inst: Inst::Const {
            ty: Ty::I32,
            value: trust_ir::Constant::Int(1),
        },
        results: vec![ValueId::new(100)],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    blk.body.push(InstrNode {
        inst: Inst::Const {
            ty: Ty::I32,
            value: trust_ir::Constant::Int(2),
        },
        results: vec![ValueId::new(101)],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    blk.body.push(InstrNode {
        inst: Inst::BinOp {
            op: BinOp::Add,
            lhs: ValueId::new(100),
            rhs: ValueId::new(101),
            ty: Ty::I32,
        },
        results: vec![ValueId::new(102)],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    blk.body.push(InstrNode {
        inst: Inst::Return {
            values: vec![ValueId::new(102)],
        },
        results: Vec::new(),
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    let mut f = Function::new(id, fname, FuncTyId::new(0), entry);
    f.blocks.push(blk);
    m.functions.push(f);
    id
}

fn to_json(m: &Module) -> String {
    serde_json::to_string(m).expect("serialize module")
}

// ---- Acceptance criterion 1: identical modules → exit 0 ----------------

#[test]
fn identical_modules_exit_zero() {
    let m = {
        let mut m = empty_module("X");
        add_binop_func(&mut m, 0, "f");
        m
    };
    let j = to_json(&m);
    let a = write_tmp("ac1-a", &j);
    let b = write_tmp("ac1-b", &j);

    let out = run_cli(&[a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        out.stdout.is_empty(),
        "expected empty stdout, got: {}",
        String::from_utf8_lossy(&out.stdout)
    );
}

// ---- Acceptance criterion 2: ID renumbering → exit 0 -------------------

#[test]
fn id_renumbering_exit_zero() {
    let a_mod = {
        let mut m = empty_module("X");
        add_simple_return_func(&mut m, 0, "f", 0, 1);
        m
    };
    let b_mod = {
        let mut m = empty_module("X");
        // Different FuncId, different BlockId, different ValueId — same semantics.
        add_simple_return_func(&mut m, 99, "f", 77, 123);
        m
    };

    let a = write_tmp("ac2-a", &to_json(&a_mod));
    let b = write_tmp("ac2-b", &to_json(&b_mod));

    let out = run_cli(&[a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "stderr: {}\nstdout: {}",
        String::from_utf8_lossy(&out.stderr),
        String::from_utf8_lossy(&out.stdout)
    );
    assert!(out.stdout.is_empty());
}

// ---- Acceptance criterion 3: declaration order → exit 0 ---------------

#[test]
fn declaration_order_exit_zero() {
    let a_mod = {
        let mut m = empty_module("X");
        add_simple_return_func(&mut m, 0, "f", 0, 1);
        add_simple_return_func(&mut m, 1, "g", 2, 3);
        m
    };
    let b_mod = {
        let mut m = empty_module("X");
        // Reversed function order.
        add_simple_return_func(&mut m, 1, "g", 2, 3);
        add_simple_return_func(&mut m, 0, "f", 0, 1);
        m
    };

    let a = write_tmp("ac3-a", &to_json(&a_mod));
    let b = write_tmp("ac3-b", &to_json(&b_mod));

    let out = run_cli(&[a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "stderr: {}\nstdout: {}",
        String::from_utf8_lossy(&out.stderr),
        String::from_utf8_lossy(&out.stdout)
    );
}

// ---- Acceptance criterion 4: added instruction reports that diff -------

#[test]
fn added_instruction_exit_one() {
    let a_mod = {
        let mut m = empty_module("X");
        add_binop_func(&mut m, 0, "f");
        m
    };
    let b_mod = {
        let mut m = empty_module("X");
        let id = FuncId::new(0);
        let entry = BlockId::new(10);
        let mut blk = Block::new(entry);
        blk.body.push(InstrNode {
            inst: Inst::Const {
                ty: Ty::I32,
                value: trust_ir::Constant::Int(1),
            },
            results: vec![ValueId::new(100)],
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        blk.body.push(InstrNode {
            inst: Inst::Const {
                ty: Ty::I32,
                value: trust_ir::Constant::Int(2),
            },
            results: vec![ValueId::new(101)],
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        blk.body.push(InstrNode {
            inst: Inst::BinOp {
                op: BinOp::Add,
                lhs: ValueId::new(100),
                rhs: ValueId::new(101),
                ty: Ty::I32,
            },
            results: vec![ValueId::new(102)],
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        // Extra instruction: ICmp::Eq on the sum with 0.
        blk.body.push(InstrNode {
            inst: Inst::ICmp {
                op: ICmpOp::Eq,
                lhs: ValueId::new(102),
                rhs: ValueId::new(100),
                ty: Ty::I32,
            },
            results: vec![ValueId::new(103)],
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        blk.body.push(InstrNode {
            inst: Inst::Return {
                values: vec![ValueId::new(102)],
            },
            results: Vec::new(),
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        let mut f = Function::new(id, "f", FuncTyId::new(0), entry);
        f.blocks.push(blk);
        m.functions.push(f);
        m
    };

    let a = write_tmp("ac4-a", &to_json(&a_mod));
    let b = write_tmp("ac4-b", &to_json(&b_mod));

    let out = run_cli(&[a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(1),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("icmp"),
        "expected text diff to mention 'icmp', got: {stdout}"
    );
    // Should identify the function containing the new instruction.
    assert!(stdout.contains("function @f"), "stdout: {stdout}");
}

// ---- Acceptance criterion 5: --json emits valid JSON -------------------

#[test]
fn json_output_is_valid() {
    let a_mod = {
        let mut m = empty_module("X");
        add_binop_func(&mut m, 0, "f");
        m
    };
    let b_mod = {
        let mut m = empty_module("X");
        // Different op: Sub instead of Add.
        let id = FuncId::new(0);
        let entry = BlockId::new(10);
        let mut blk = Block::new(entry);
        blk.body.push(InstrNode {
            inst: Inst::Const {
                ty: Ty::I32,
                value: trust_ir::Constant::Int(1),
            },
            results: vec![ValueId::new(100)],
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        blk.body.push(InstrNode {
            inst: Inst::Const {
                ty: Ty::I32,
                value: trust_ir::Constant::Int(2),
            },
            results: vec![ValueId::new(101)],
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        blk.body.push(InstrNode {
            inst: Inst::BinOp {
                op: BinOp::Sub,
                lhs: ValueId::new(100),
                rhs: ValueId::new(101),
                ty: Ty::I32,
            },
            results: vec![ValueId::new(102)],
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        blk.body.push(InstrNode {
            inst: Inst::Return {
                values: vec![ValueId::new(102)],
            },
            results: Vec::new(),
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        let mut f = Function::new(id, "f", FuncTyId::new(0), entry);
        f.blocks.push(blk);
        m.functions.push(f);
        m
    };

    let a = write_tmp("ac5-a", &to_json(&a_mod));
    let b = write_tmp("ac5-b", &to_json(&b_mod));

    let out = run_cli(&["--json", a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(1));
    let stdout = String::from_utf8_lossy(&out.stdout);
    // Re-parse to confirm valid JSON.
    let v: serde_json::Value = serde_json::from_str(stdout.trim()).expect("valid json output");
    assert_eq!(v["schema_version"], 1);
    assert_eq!(v["module_a"], "X");
    assert_eq!(v["module_b"], "X");
    assert!(v["changes"].is_array());
    let changes = v["changes"].as_array().unwrap();
    assert_eq!(changes.len(), 1);
    assert_eq!(changes[0]["kind"], "func_changed");
    assert_eq!(changes[0]["name"], "f");
}

// ---- Acceptance criterion 6: --ignore-proofs suppresses proof diffs ----

#[test]
fn ignore_proofs_suppresses_proof_only_diffs() {
    let a_mod = {
        let mut m = empty_module("X");
        add_binop_func(&mut m, 0, "f");
        m
    };
    let b_mod = {
        let mut m = empty_module("X");
        add_binop_func(&mut m, 0, "f");
        // Add a function-level proof annotation only.
        m.functions[0].proofs.push(ProofAnnotation::Pure);
        m
    };

    let a = write_tmp("ac6-a", &to_json(&a_mod));
    let b = write_tmp("ac6-b", &to_json(&b_mod));

    // Without the flag: exit 1.
    let out = run_cli(&[a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(1),
        "expected proof-only diff to produce exit 1, stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    // With the flag: exit 0.
    let out = run_cli(&["--ignore-proofs", a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.stdout.is_empty());
}

// ---- Error handling: missing file → exit 2 -----------------------------

#[test]
fn missing_file_exits_two() {
    let a = write_tmp("err-a", &to_json(&empty_module("X")));
    let out = run_cli(&[
        a.to_str().unwrap(),
        "/nonexistent/path/for/trust_ir-diff-test.json",
    ]);
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("error"), "stderr: {stderr}");
}

// ---- Error handling: parse error → exit 2 ------------------------------

#[test]
fn parse_error_exits_two() {
    let a = write_tmp("err-parse-a", "not valid json");
    let b = write_tmp("err-parse-b", &to_json(&empty_module("X")));
    let out = run_cli(&[a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(2));
}

// ---- Error handling: unknown option → exit 2 ---------------------------

#[test]
fn unknown_option_exits_two() {
    let a = write_tmp("err-opt-a", &to_json(&empty_module("X")));
    let b = write_tmp("err-opt-b", &to_json(&empty_module("X")));
    let out = run_cli(&["--frobnicate", a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(2));
}

// ---- Error handling: wrong positional count → exit 2 --------------------
// Pins `parse_args`'s arity refusal (its index step became a saturating add
// so the verified lane sees no panicking `+=`).

#[test]
fn wrong_positional_count_exits_two_and_names_the_count() {
    let a = write_tmp("err-arity-a", &to_json(&empty_module("X")));
    let a = a.to_str().unwrap();
    for (args, got) in [
        (&[][..], 0),
        (&[a][..], 1),
        (&[a, a, a][..], 3),
        (&["--json", a][..], 1),
    ] {
        let out = run_cli(args);
        assert_eq!(out.status.code(), Some(2), "{args:?}");
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            stderr.contains(&format!(
                "expected exactly 2 positional arguments (got {got})"
            )),
            "{args:?}: {stderr}"
        );
    }
}

// ---- Dialect instructions are handled via fingerprint ------------------

#[test]
fn dialect_op_attr_diff_is_reported() {
    let build = |op: &str| -> Module {
        let mut m = empty_module("X");
        let id = FuncId::new(0);
        let entry = BlockId::new(0);
        let mut blk = Block::new(entry);
        blk.body.push(InstrNode {
            inst: Inst::DialectOp(Box::new(DialectInst {
                dialect: "tla".into(),
                op: op.to_string(),
                operands: Vec::new(),
                result_tys: vec![Ty::I32],
                attrs: vec![AttrEntry {
                    name: "k".into(),
                    value: AttrValue::I64(1),
                }],
                version: 1,
            })),
            results: vec![ValueId::new(0)],
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        blk.body.push(InstrNode {
            inst: Inst::Return {
                values: vec![ValueId::new(0)],
            },
            results: Vec::new(),
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        let mut f = Function::new(id, "f", FuncTyId::new(0), entry);
        f.blocks.push(blk);
        m.functions.push(f);
        m
    };

    let a_mod = build("foo");
    let b_mod = build("bar");

    let a = write_tmp("dialect-a", &to_json(&a_mod));
    let b = write_tmp("dialect-b", &to_json(&b_mod));

    let out = run_cli(&[a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(1),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

// ---- Module proof state: obligation status difference ------------------
//
// Two modules identical except one obligation's status. The default diff
// reports it (exit 1); `--ignore-proofs` suppresses it (exit 0).

#[test]
fn obligation_status_difference_reported_and_suppressed() {
    use trust_ir::{ObligationKind, ProofId, ProofObligation, ProofStatus};

    let build = |status: ProofStatus| -> Module {
        let mut m = empty_module("X");
        add_simple_return_func(&mut m, 0, "f", 0, 1);
        m.proof_obligations.push(ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            status,
            "result is non-negative",
        ));
        m
    };

    let a = write_tmp("po-a", &to_json(&build(ProofStatus::Pending)));
    let b = write_tmp("po-b", &to_json(&build(ProofStatus::Discharged)));

    // Default: the status change is reported.
    let out = run_cli(&[a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(1),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("obligation")
            && stdout.contains("pending")
            && stdout.contains("discharged"),
        "expected obligation status diff, got: {stdout}"
    );

    // --ignore-proofs: suppressed.
    let out = run_cli(&["--ignore-proofs", a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.stdout.is_empty());
}

// ---- Module proof state: a missing certificate -------------------------

#[test]
fn missing_certificate_reported_and_suppressed() {
    use trust_ir::{
        ObligationKind, ProofCertificate, ProofEvidence, ProofId, ProofObligation, ProofStatus,
    };

    let build = |with_cert: bool| -> Module {
        let mut m = empty_module("X");
        add_simple_return_func(&mut m, 0, "f", 0, 1);
        m.proof_obligations.push(ProofObligation::new(
            ProofId::new(0),
            ObligationKind::MemorySafety,
            ProofStatus::Discharged,
            "no out-of-bounds access",
        ));
        if with_cert {
            m.proof_certificates.push(ProofCertificate {
                obligation: ProofId::new(0),
                prover: "ay".into(),
                evidence: ProofEvidence::SmtProof(vec![0xde, 0xad]),
                assurance: None,
            });
        }
        m
    };

    let a = write_tmp("cert-a", &to_json(&build(true)));
    let b = write_tmp("cert-b", &to_json(&build(false)));

    // Default JSON: a certificate_removed entry in proof_state.
    let out = run_cli(&["--json", a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(1));
    let stdout = String::from_utf8_lossy(&out.stdout);
    let v: serde_json::Value = serde_json::from_str(stdout.trim()).expect("valid json output");
    let ps = v["proof_state"].as_array().expect("proof_state array");
    assert_eq!(ps.len(), 1, "proof_state: {ps:?}");
    assert_eq!(ps[0]["kind"], "certificate_removed");

    // --ignore-proofs: suppressed.
    let out = run_cli(&["--ignore-proofs", a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(0));
    assert!(out.stdout.is_empty());
}

// ---- Per-call proof_context difference ---------------------------------

#[test]
fn differing_proof_context_reported_and_suppressed() {
    use trust_ir::proof::ProofContext;
    use trust_ir::{ObligationKind, ProofId, ProofObligation, ProofStatus};

    // Module with callee `g` and caller `f` whose `call @g` node carries a
    // proof_context. The two builds differ only in which obligation the
    // context assumes.
    let build = |assume_id: u32| -> Module {
        let mut m = empty_module("X");

        // Two distinct obligations scoped to the callee.
        m.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Postcondition,
                ProofStatus::Discharged,
                "g returns even",
            )
            .with_function(FuncId::new(1)),
        );
        m.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(1),
                ObligationKind::Postcondition,
                ProofStatus::Discharged,
                "g returns positive",
            )
            .with_function(FuncId::new(1)),
        );

        // Callee g (id 1).
        add_simple_return_func(&mut m, 1, "g", 20, 21);

        // Caller f (id 0) calls g with a proof_context.
        let entry = BlockId::new(0);
        let mut blk = Block::new(entry);
        blk.body.push(InstrNode {
            inst: Inst::Call {
                callee: FuncId::new(1),
                args: Vec::new(),
            },
            results: Vec::new(),
            proofs: Vec::new(),
            span: None,
            proof_context: Some(ProofContext {
                assumes: vec![ProofId::new(assume_id)],
                establishes: Vec::new(),
            }),
            scope: None,
        });
        blk.body.push(InstrNode {
            inst: Inst::Return { values: Vec::new() },
            results: Vec::new(),
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        let mut f = Function::new(FuncId::new(0), "f", FuncTyId::new(0), entry);
        f.blocks.push(blk);
        f.calling_conv = CallingConv::C;
        f.linkage = Linkage::External;
        m.functions.push(f);
        m
    };

    let a = write_tmp("ctx-a", &to_json(&build(0)));
    let b = write_tmp("ctx-b", &to_json(&build(1)));

    // Default: the call node is reported as replaced, mentioning the context.
    let out = run_cli(&[a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(1),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("function @f") && stdout.contains("ctx{"),
        "expected call diff citing proof context, got: {stdout}"
    );

    // --ignore-proofs: suppressed (the call instructions are otherwise equal).
    let out = run_cli(&["--ignore-proofs", a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.stdout.is_empty());
}

fn tuple_layout_module() -> Module {
    let mut m = Module::new("tuple_layout");
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let ty = m
        .add_type(Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U8]))
        .expect("Module::add_type: test fixture");
    m.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type: ty,
        size: 16,
        align: 8,
        field_offsets: vec![8, 0, 9],
    });
    m
}

#[test]
fn tuple_layout_changes_are_reported_even_with_ignore_proofs() {
    let a = tuple_layout_module();
    let mut b = a.clone();
    b.tuple_layouts[0].field_offsets.swap(0, 2);
    let pa = write_tmp("tuple-a", &serde_json::to_string(&a).unwrap());
    let pb = write_tmp("tuple-b", &serde_json::to_string(&b).unwrap());
    let out = run_cli(&[
        "--ignore-proofs",
        "--json",
        pa.to_str().unwrap(),
        pb.to_str().unwrap(),
    ]);
    assert_eq!(out.status.code(), Some(1), "{:?}", out);
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(json["module_meta"][0]["field"], "tuple_layouts");
    assert!(json["changes"].as_array().unwrap().is_empty());
    std::fs::remove_file(pa).unwrap();
    std::fs::remove_file(pb).unwrap();
}

#[test]
fn tuple_layout_cli_rejects_unused_invalid_evidence() {
    let a = tuple_layout_module();
    let mut cases = Vec::new();
    let mut b = a.clone();
    b.tuple_layouts[0].field_offsets[2] = 8;
    cases.push(b);
    let mut b = a.clone();
    b.tuple_layouts.push(b.tuple_layouts[0].clone());
    cases.push(b);
    let mut b = a.clone();
    b.target_info = None;
    cases.push(b);
    let mut b = a.clone();
    b.types[0] = Ty::Tuple(vec![Ty::Array(trust_ir::TyId::new(0), 1)]);
    b.tuple_layouts[0].field_offsets = vec![0];
    cases.push(b);
    let pa = write_tmp("tuple-good", &serde_json::to_string(&a).unwrap());
    for b in cases {
        let pb = write_tmp("tuple-bad", &serde_json::to_string(&b).unwrap());
        let out = run_cli(&[
            "--ignore-proofs",
            pa.to_str().unwrap(),
            pb.to_str().unwrap(),
        ]);
        assert_eq!(out.status.code(), Some(2), "{:?}", out);
        assert!(String::from_utf8_lossy(&out.stderr).contains("validate "));
        std::fs::remove_file(pb).unwrap();
    }
    std::fs::remove_file(pa).unwrap();
}

// ---- Authority / ABI / linkage metadata is reported (c05 part d) ---------
//
// Audit rows `b1.gap.diff_blind_to_{body_gate,display_path,function_linkage,
// calling_conv,globals,spec_modules_and_target}` (2026-09-17): the CLI exited 0
// with empty output on JSON twins that differed only in a function's codegen
// license, its linkage or calling convention, a global's visibility or
// initializer, or the module target. Each is now an exit-1 report naming the
// field, in text and `--json`, and it survives `--ignore-proofs` because none
// of it is proof coverage.

fn fn_mut<'m>(m: &'m mut Module, name: &str) -> &'m mut Function {
    m.functions.iter_mut().find(|f| f.name == name).unwrap()
}

fn licensed_module() -> Module {
    let mut m = empty_module("licensed");
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    add_simple_return_func(&mut m, 0, "clean_f", 0, 1);
    let f = fn_mut(&mut m, "clean_f");
    f.producer = Some(trust_ir::Producer::Clean);
    f.body_gate = Some(trust_ir::BodyGate::Gated {
        authority: "clean-kernel-tv".into(),
        evidence: None,
    });
    f.display_path = Some("app::clean_f".into());
    m.globals.push(trust_ir::Global {
        name: "APP_BIAS".into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(trust_ir::Constant::Int(1)),
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Hidden,
        retained: false,
    });
    m
}

/// Runs the CLI on `a` / `b` with and without `--ignore-proofs`, in text and
/// JSON mode, and asserts every run reports exactly the one expected
/// function-level or module-level `MetaChange` with exit 1.
fn assert_cli_reports_meta(a: &Module, b: &Module, func: Option<&str>, field: &str) {
    let pa = write_tmp("meta-a", &to_json(a));
    let pb = write_tmp("meta-b", &to_json(b));
    for ignore in [false, true] {
        let mut text_args = Vec::new();
        let mut json_args = vec!["--json"];
        if ignore {
            text_args.push("--ignore-proofs");
            json_args.push("--ignore-proofs");
        }
        text_args.extend([pa.to_str().unwrap(), pb.to_str().unwrap()]);
        json_args.extend([pa.to_str().unwrap(), pb.to_str().unwrap()]);

        let out = run_cli(&text_args);
        assert_eq!(out.status.code(), Some(1), "{field}: {out:?}");
        let text = String::from_utf8_lossy(&out.stdout);
        let expected_line = match func {
            Some(_) => format!("    ~ {field}: "),
            None => format!("~ module {field}: "),
        };
        assert!(
            text.contains(&expected_line),
            "{field} (ignore_proofs={ignore}): text report lacks `{expected_line}`:\n{text}"
        );
        if let Some(func) = func {
            assert!(text.contains(&format!("~ function @{func}")), "{text}");
        }

        let out = run_cli(&json_args);
        assert_eq!(out.status.code(), Some(1), "{field}: {out:?}");
        let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        match func {
            Some(func) => {
                let changes = json["changes"].as_array().unwrap();
                assert_eq!(changes.len(), 1, "{field}: {json}");
                assert_eq!(changes[0]["kind"], "func_changed");
                assert_eq!(changes[0]["name"], func);
                let meta = changes[0]["meta"].as_array().unwrap();
                assert_eq!(meta.len(), 1, "{field}: {json}");
                assert_eq!(meta[0]["field"], field, "{field}: {json}");
                assert!(changes[0]["blocks"].as_array().unwrap().is_empty());
                assert!(changes[0]["proofs"].as_array().unwrap().is_empty());
                assert!(json["module_meta"].as_array().unwrap().is_empty());
            }
            None => {
                assert!(json["changes"].as_array().unwrap().is_empty(), "{json}");
                let meta = json["module_meta"].as_array().unwrap();
                assert_eq!(meta.len(), 1, "{field}: {json}");
                assert_eq!(meta[0]["field"], field, "{field}: {json}");
            }
        }
    }
    std::fs::remove_file(pa).unwrap();
    std::fs::remove_file(pb).unwrap();
}

#[test]
fn licensed_module_is_isomorphic_to_itself() {
    let m = licensed_module();
    let j = to_json(&m);
    let pa = write_tmp("lic-a", &j);
    let pb = write_tmp("lic-b", &j);
    let out = run_cli(&[pa.to_str().unwrap(), pb.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    assert!(out.stdout.is_empty());
    std::fs::remove_file(pa).unwrap();
    std::fs::remove_file(pb).unwrap();
}

#[test]
fn body_gate_regression_is_reported_even_with_ignore_proofs() {
    let a = licensed_module();
    let mut b = a.clone();
    fn_mut(&mut b, "clean_f").body_gate = Some(trust_ir::BodyGate::Ungated);
    assert_cli_reports_meta(&a, &b, Some("clean_f"), "body_gate");

    // The exact rendering distinguishes `None` (permitted) from `Ungated`
    // (refused) and names the authority.
    let pa = write_tmp("gate-a", &to_json(&a));
    let pb = write_tmp("gate-b", &to_json(&b));
    let out = run_cli(&[pa.to_str().unwrap(), pb.to_str().unwrap()]);
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(
        text.contains("    ~ body_gate: gated \"clean-kernel-tv\" -> ungated"),
        "{text}"
    );
    std::fs::remove_file(pa).unwrap();
    std::fs::remove_file(pb).unwrap();
}

#[test]
fn display_path_linkage_and_calling_conv_are_reported() {
    let a = licensed_module();
    let mut b = a.clone();
    fn_mut(&mut b, "clean_f").display_path = Some("evil::other".into());
    assert_cli_reports_meta(&a, &b, Some("clean_f"), "display_path");

    let mut b = a.clone();
    fn_mut(&mut b, "clean_f").linkage = Linkage::Internal;
    assert_cli_reports_meta(&a, &b, Some("clean_f"), "linkage");

    let mut b = a.clone();
    fn_mut(&mut b, "clean_f").calling_conv = CallingConv::Rust;
    assert_cli_reports_meta(&a, &b, Some("clean_f"), "calling_conv");
}

#[test]
fn global_and_target_changes_are_reported_without_tuple_layouts() {
    let a = licensed_module();
    assert!(a.tuple_layouts.is_empty());
    let mut b = a.clone();
    b.globals[0].visibility = trust_ir::Visibility::Default;
    assert_cli_reports_meta(&a, &b, None, "global @APP_BIAS");

    let mut b = a.clone();
    b.globals[0].initializer = Some(trust_ir::Constant::Int(2));
    assert_cli_reports_meta(&a, &b, None, "global @APP_BIAS");

    let mut b = a.clone();
    b.target_info.as_mut().unwrap().triple = "x86_64-unknown-linux-gnu".into();
    assert_cli_reports_meta(&a, &b, None, "target_info");
}

#[test]
fn help_documents_the_metadata_that_is_never_ignored() {
    let out = run_cli(&["--help"]);
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let text = String::from_utf8_lossy(&out.stdout);
    for needle in [
        "body_gate",
        "linkage",
        "calling_conv",
        "global @",
        "target_info",
    ] {
        assert!(text.contains(needle), "--help lacks `{needle}`:\n{text}");
    }
}

// ---- WS4.19 review: --include-debug surfaces a changed inlining chain ----

/// A changed `ScopeData.inlined_at` link is DEBUG metadata: the default lane
/// reports nothing (exit 0), `--include-debug` reports the `scopes` row
/// (exit 1) and renders the new link. Pinned at the CLI so the flag is wired,
/// not only the library option.
#[test]
fn include_debug_reports_a_changed_inlining_chain_link() {
    let with_link = |line: u32, callee: &str| {
        let mut m = empty_module("X");
        add_binop_func(&mut m, 0, "f");
        m.files.push("src/caller.rs".into());
        m.functions[0].scopes = Some(vec![
            trust_ir::ScopeData::new(None, None),
            trust_ir::ScopeData {
                parent: Some(0),
                span: None,
                inlined_at: Some(trust_ir::InlinedAt {
                    span: trust_ir::SourceSpan {
                        file: 0,
                        line,
                        col: 9,
                    },
                    callee: callee.to_string(),
                }),
            },
        ]);
        m
    };
    let a = write_tmp("dbg-a", &to_json(&with_link(12, "clean::island::a")));
    let b = write_tmp("dbg-b", &to_json(&with_link(99, "clean::island::b")));

    let out = run_cli(&[a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "default lane ignores the chain: stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let out = run_cli(&["--include-debug", a.to_str().unwrap(), b.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(1));
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(
        text.contains("scopes")
            && text.contains("inlined-at 0 99 9")
            && text.contains("clean::island::b"),
        "stdout: {text}"
    );

    // Control: the same module on both sides is empty under the flag too.
    let out = run_cli(&["--include-debug", a.to_str().unwrap(), a.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(0));
    assert!(out.stdout.is_empty());
}
