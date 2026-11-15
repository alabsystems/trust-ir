// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap WS4.13: the in-repo ports of the two remaining F-073 audit rows
// that are about the `trust-ir-diff` TOOL (the library rows live in the
// conformance targets `diff_fields` / `diff_authority_metadata`):
//
// * `scout-lean.A4` — `trust-ir-diff` could not read a valid `.trust_ir`
//   text module (`expected value at line 1 column 1`: JSON-only input);
// * `crit.misw05` — the critic weighted the six `b1.gap.diff_blind_to_*`
//   rows as tooling that gated nothing. This target is a gate leg now
//   (`scripts/ci_gates.sh` gate 3 runs `-p trust-ir-diff` wholesale).

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use trust_ir::{
    BinOp, Block, BlockId, BodyGate, CallingConv, Constant, FuncId, FuncTy, Function, Global, Inst,
    InstrNode, Linkage, Module, TargetInfo, Ty, ValueId,
};

fn bin_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-ir-diff"))
}

/// A fresh directory per call: tests run in parallel and name files freely.
fn scratch_dir() -> PathBuf {
    static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "trust-ir-diff-f073-{}-{}",
        std::process::id(),
        COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    dir
}

fn write(dir: &Path, name: &str, bytes: &[u8]) -> PathBuf {
    let path = dir.join(name);
    std::fs::write(&path, bytes).expect("write input");
    path
}

fn run(args: &[&Path], flags: &[&str]) -> Output {
    Command::new(bin_path())
        .args(flags)
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("spawn trust-ir-diff")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// `f(p: i32) -> i32 { p + p }` — small enough that every transport,
/// text included, carries it losslessly.
fn module(op: BinOp) -> Module {
    let mut m = Module::new("formats");
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(0);
    let mut f = Function::new(FuncId::new(0), "f", ft, entry);
    let mut blk = Block::new(entry);
    blk.params.push((ValueId::new(0), Ty::I32));
    blk.body.push(
        InstrNode::new(Inst::BinOp {
            op,
            ty: Ty::I32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    f.blocks.push(blk);
    m.functions.push(f);
    m
}

fn bin(m: &Module) -> Vec<u8> {
    trust_ir::binary::serialize_module(m).expect("serialize_module: test fixture")
}

fn text(m: &Module) -> Vec<u8> {
    trust_ir::format::text_checked(m)
        .expect("the fixture is loss-free in text")
        .into_bytes()
}

fn json(m: &Module) -> Vec<u8> {
    serde_json::to_vec(m).unwrap()
}

// ---------------------------------------------------------------------------
// The ported GAP row
// ---------------------------------------------------------------------------

/// `scout-lean.A4` (F-073), flipped GAP -> PASS. The scout ran
/// `trust-ir-diff applyTwice.trust_ir applyTwice.rt.trust_ir` on two valid
/// TEXT modules and got `parse ...: expected value at line 1 column 1`,
/// exit 2: the CLI read serde JSON only. A text module now diffs empty
/// against itself and against its JSON twin, and a real change between two
/// text modules is reported (exit 1).
#[test]
#[allow(non_snake_case)]
fn scout_lean_A4() {
    let dir = scratch_dir();
    let add = module(BinOp::Add);
    let a = write(&dir, "applyTwice.trust_ir", &text(&add));
    let rt = write(&dir, "applyTwice.rt.trust_ir", &text(&add));
    let out = run(&[&a, &rt], &[]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
    assert!(out.stdout.is_empty(), "{}", stdout(&out));
    assert!(
        !stderr(&out).contains("expected value at line 1 column 1"),
        "{}",
        stderr(&out)
    );

    let j = write(&dir, "applyTwice.json", &json(&add));
    let out = run(&[&a, &j], &[]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));

    let mul = write(&dir, "applyTwice.mul.trust_ir", &text(&module(BinOp::Mul)));
    let out = run(&[&a, &mul], &[]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(stdout(&out).contains("~ function @f"), "{}", stdout(&out));
}

// ---------------------------------------------------------------------------
// crit.misw05
// ---------------------------------------------------------------------------

/// A module carrying every field of the six `b1.gap.diff_blind_to_*` rows,
/// non-default.
fn licensed() -> Module {
    let mut m = module(BinOp::Add);
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let f = &mut m.functions[0];
    f.body_gate = Some(BodyGate::Gated {
        authority: "clean-kernel-tv".into(),
        evidence: None,
    });
    f.display_path = Some("app::f".into());
    f.linkage = Linkage::External;
    f.calling_conv = CallingConv::C;
    m.globals.push(Global {
        name: "APP_BIAS".into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(1)),
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Hidden,
        retained: false,
    });
    m.spec_modules
        .push(trust_ir::spec::SpecModule::design_only("Counter"));
    m
}

/// One named single-field mutation of the licensed module.
type Mutation = fn(&mut Module);

/// `crit.misw05` (F-073): the critic weighted the six
/// `b1.gap.diff_blind_to_*` rows as TOOLING — `trust-ir-diff` — not format,
/// and noted they gated nothing. Ported at that lens: the shipped
/// `trust-ir-diff` binary, over the producer's own `.trust-ir.bin`
/// transport (the one it could not read at audit time), reports each of the
/// six fields as its named row with exit 1 — and this target is now a gate
/// leg (`scripts/ci_gates.sh` gate 3 runs `-p trust-ir-diff`).
#[test]
#[allow(non_snake_case)]
fn crit_misw05() {
    let dir = scratch_dir();
    let a = licensed();
    let pa = write(&dir, "a.trust-ir.bin", &bin(&a));
    let rows: [(&str, Mutation); 6] = [
        ("body_gate", |m| {
            m.functions[0].body_gate = Some(BodyGate::Ungated)
        }),
        ("display_path", |m| m.functions[0].display_path = None),
        ("linkage", |m| m.functions[0].linkage = Linkage::Internal),
        ("calling_conv", |m| {
            m.functions[0].calling_conv = CallingConv::Rust
        }),
        ("global @APP_BIAS", |m| {
            m.globals[0].initializer = Some(Constant::Int(2))
        }),
        ("target_info", |m| {
            m.target_info.as_mut().unwrap().triple = "x86_64-unknown-linux-gnu".into()
        }),
    ];
    for (field, mutate) in rows {
        let mut b = a.clone();
        mutate(&mut b);
        let pb = write(&dir, "b.trust-ir.bin", &bin(&b));
        for flags in [&[][..], &["--ignore-proofs"][..]] {
            let out = run(&[&pa, &pb], flags);
            assert_eq!(out.status.code(), Some(1), "{field}: {}", stderr(&out));
            assert!(
                stdout(&out).contains(&format!("~ {field}: "))
                    || stdout(&out).contains(&format!("~ module {field}: ")),
                "{field}: {}",
                stdout(&out)
            );
        }
    }
    // The spec-module leg of `_spec_modules_and_target`.
    let mut b = a.clone();
    b.spec_modules[0].actions.push("Incr".into());
    let pb = write(&dir, "b.trust-ir.bin", &bin(&b));
    let out = run(&[&pa, &pb], &[]);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(
        stdout(&out).contains("spec_module Counter"),
        "{}",
        stdout(&out)
    );
    // Control: the unmutated module is isomorphic to itself across transports.
    let pj = write(&dir, "a.json", &json(&a));
    let out = run(&[&pa, &pj], &[]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
}
