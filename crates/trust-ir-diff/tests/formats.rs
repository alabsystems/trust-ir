// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap WS4.13 / WS4.9 remainder: `trust-ir-diff` reads all four formats
// through the ONE resolution rule every TrustIr tool shares
// (`trust_ir::codec::resolve_module_format`), and `--format` overrides it.
//
// Measured 2026-09-17 (scout-lean A4, scout-emit): `trust-ir-diff` read serde
// JSON only, so a valid `.trust_ir` text module failed with
// `expected value at line 1 column 1` (exit 2), and a producer's
// `.trust-ir.bin` could not be diffed at all without a `trust-ir convert`
// first. Every input here is the SAME module in a different transport; the
// negative twins are refused by their SPECIFIC named reason with exit 2
// (never 1: 1 is a verdict about two modules that were both read).

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use trust_ir::{
    BinOp, Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

fn bin_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-ir-diff"))
}

/// A fresh directory per call: tests run in parallel and name files freely.
fn scratch_dir() -> PathBuf {
    static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "trust-ir-diff-formats-{}-{}",
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

fn msgpack(m: &Module) -> Vec<u8> {
    rmp_serde::to_vec(m).unwrap()
}

/// Every transport, with the file names that select it.
fn transports(m: &Module) -> Vec<(&'static str, Vec<u8>)> {
    vec![
        ("m.trust-ir.bin", bin(m)),
        ("m.tmbc", bin(m)),
        ("m.trust-ir.txt", text(m)),
        ("m.trust_ir", text(m)),
        ("m.json", json(m)),
        ("m.msgpack", msgpack(m)),
    ]
}

// ---------------------------------------------------------------------------
// Positive: every transport, every pairing
// ---------------------------------------------------------------------------

/// The same module in any two transports is isomorphic; a changed module in
/// any transport is reported against the original in any other.
#[test]
fn every_transport_pair_is_read() {
    let dir = scratch_dir();
    let add = module(BinOp::Add);
    let mul = module(BinOp::Mul);
    let adds: Vec<PathBuf> = transports(&add)
        .into_iter()
        .map(|(name, bytes)| write(&dir, &format!("add.{name}"), &bytes))
        .collect();
    let muls: Vec<PathBuf> = transports(&mul)
        .into_iter()
        .map(|(name, bytes)| write(&dir, &format!("mul.{name}"), &bytes))
        .collect();
    for a in &adds {
        for b in &adds {
            let out = run(&[a, b], &[]);
            assert_eq!(
                out.status.code(),
                Some(0),
                "{} vs {}: {}{}",
                a.display(),
                b.display(),
                stdout(&out),
                stderr(&out)
            );
        }
        for b in &muls {
            let out = run(&[a, b], &[]);
            assert_eq!(
                out.status.code(),
                Some(1),
                "{} vs {}: {}",
                a.display(),
                b.display(),
                stderr(&out)
            );
        }
    }
}

/// A name that says nothing (`.bin`, no extension) takes the content's
/// claim — binary, JSON and text are sniffed.
#[test]
fn a_silent_name_takes_the_sniffed_format() {
    let dir = scratch_dir();
    let add = module(BinOp::Add);
    let reference = write(&dir, "ref.json", &json(&add));
    for (name, bytes) in [
        ("m.bin", bin(&add)),
        ("m_bin", bin(&add)),
        ("m.out", json(&add)),
        ("m.txt", text(&add)),
    ] {
        let path = write(&dir, name, &bytes);
        let out = run(&[&reference, &path], &[]);
        assert_eq!(out.status.code(), Some(0), "{name}: {}", stderr(&out));
    }
}

// ---------------------------------------------------------------------------
// Negative twins: refused by the SPECIFIC reason, exit 2
// ---------------------------------------------------------------------------

fn assert_refused(out: &Output, needle: &str) {
    assert_eq!(
        out.status.code(),
        Some(2),
        "stdout: {}\nstderr: {}",
        stdout(out),
        stderr(out)
    );
    assert!(out.stdout.is_empty(), "{}", stdout(out));
    assert!(
        stderr(out).contains(needle),
        "wanted `{needle}` in: {}",
        stderr(out)
    );
}

/// trust-cg's `tMBC` container is refused BY NAME under any file name —
/// `.tmbc` included, the extension TrustIr itself uses for its binary.
#[test]
fn a_trust_cg_container_is_refused_by_name() {
    let dir = scratch_dir();
    let add = module(BinOp::Add);
    let reference = write(&dir, "ref.json", &json(&add));
    let mut container = b"tMBC".to_vec();
    container.extend_from_slice(&1u32.to_le_bytes());
    container.extend_from_slice(&bin(&add));
    for name in ["c.tmbc", "c.trust-ir.bin", "c.bin", "c.json"] {
        let path = write(&dir, name, &container);
        assert_refused(
            &run(&[&reference, &path], &[]),
            "this is a trust-cg tMBC container, not a trust-ir module",
        );
        // Either side.
        assert_refused(
            &run(&[&path, &reference], &[]),
            "this is a trust-cg tMBC container, not a trust-ir module",
        );
    }
}

/// A name the content contradicts is refused naming both claims, never
/// decoded under either guess.
#[test]
fn a_name_the_content_contradicts_is_refused() {
    let dir = scratch_dir();
    let add = module(BinOp::Add);
    let reference = write(&dir, "ref.json", &json(&add));
    let lying = write(&dir, "lying.json", &bin(&add));
    assert_refused(
        &run(&[&reference, &lying], &[]),
        "the file name says json but the content says TrustIr binary (TRUST_IR magic)",
    );
    let lying = write(&dir, "lying.trust-ir.bin", &text(&add));
    assert_refused(
        &run(&[&reference, &lying], &[]),
        "the file name says bin but the content says TrustIr text",
    );
}

/// MessagePack is never sniffed: without its extension (or `--format`) it
/// is undetectable, and says how to fix it.
#[test]
fn unnamed_msgpack_is_undetectable() {
    let dir = scratch_dir();
    let add = module(BinOp::Add);
    let reference = write(&dir, "ref.json", &json(&add));
    let unnamed = write(&dir, "m.bin", &msgpack(&add));
    assert_refused(
        &run(&[&reference, &unnamed], &[]),
        "cannot auto-detect format",
    );
    // Positive twin: `--format msgpack` names it — but it then applies to
    // BOTH inputs, so the reference must be MessagePack too.
    let reference = write(&dir, "ref.msgpack", &msgpack(&add));
    let out = run(&[&reference, &unnamed], &["--format", "msgpack"]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
}

// ---------------------------------------------------------------------------
// `--format` overrides detection
// ---------------------------------------------------------------------------

/// An explicit format is never second-guessed: a text module in a file named
/// `.json` is read as text under `--format text` (and `--format=text`).
#[test]
fn explicit_format_overrides_the_name() {
    let dir = scratch_dir();
    let add = module(BinOp::Add);
    let a = write(&dir, "a.json", &text(&add));
    let b = write(&dir, "b.json", &text(&add));
    for flags in [&["--format", "text"][..], &["--format=text"][..]] {
        let out = run(&[&a, &b], flags);
        assert_eq!(out.status.code(), Some(0), "{flags:?}: {}", stderr(&out));
    }
    // Without the flag the name is cross-checked against the content, and
    // the two disagree.
    assert_refused(
        &run(&[&a, &b], &[]),
        "the file name says json but the content says TrustIr text",
    );
    // Forcing the name's own format hands the text to the JSON decoder.
    assert_refused(&run(&[&a, &b], &["--format", "json"]), "json decode error");
}

/// Mutation control for the container refusal: forcing `--format bin` hands
/// the container to the BINARY DECODER, which fails with its own error — so
/// the named refusal above is the resolver's verdict, not a decoder
/// accident. (A resolver that ignored `--format`, or a sniff that mapped
/// `tMBC` to binary, would flip one of these two.)
#[test]
fn a_forced_format_reaches_the_decoder_not_the_resolver() {
    let dir = scratch_dir();
    let add = module(BinOp::Add);
    let reference = write(&dir, "ref.tmbc", &bin(&add));
    let mut container = b"tMBC".to_vec();
    container.extend_from_slice(&bin(&add));
    let path = write(&dir, "c.tmbc", &container);
    let out = run(&[&reference, &path], &["--format", "bin"]);
    assert_refused(&out, "binary decode error");
    assert!(!stderr(&out).contains("tMBC container"), "{}", stderr(&out));
}

#[test]
fn a_bad_format_value_is_a_usage_error() {
    let dir = scratch_dir();
    let add = module(BinOp::Add);
    let a = write(&dir, "a.json", &json(&add));
    assert_refused(
        &run(&[&a, &a], &["--format", "binary"]),
        "invalid --format value",
    );
    let dangling = Command::new(bin_path())
        .arg(&a)
        .arg(&a)
        .arg("--format")
        .output()
        .unwrap();
    assert_refused(&dangling, "--format needs a value");
}

#[test]
fn help_documents_the_four_formats() {
    let out = Command::new(bin_path()).arg("--help").output().unwrap();
    assert_eq!(out.status.code(), Some(0));
    let help = stdout(&out);
    for needle in [
        "--format <FMT>",
        "bin | text | json | msgpack",
        ".trust-ir.bin",
        "tMBC",
        "MessagePack is never sniffed",
    ] {
        assert!(help.contains(needle), "--help lacks `{needle}`:\n{help}");
    }
}

/// Filesystem names are byte-preserving; a lossy Unicode decoy must never be read.
#[cfg(target_os = "linux")]
#[test]
fn non_unicode_paths_select_exact_files_in_either_position() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    let dir = scratch_dir();
    let expected = module(BinOp::Add);
    let actual = dir.join(OsString::from_vec(b"module-\xff.msgpack".to_vec()));
    std::fs::write(&actual, msgpack(&expected)).unwrap();
    let reference = write(&dir, "reference.msgpack", &msgpack(&expected));
    std::fs::write(
        actual.to_string_lossy().as_ref(),
        msgpack(&module(BinOp::Mul)),
    )
    .unwrap();
    assert!(actual.to_str().is_none());
    for flags in [
        vec![],
        vec!["--format", "msgpack"],
        vec!["--format=msgpack"],
    ] {
        for args in [
            [actual.as_path(), reference.as_path()],
            [reference.as_path(), actual.as_path()],
        ] {
            let out = run(&args, &flags);
            assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
            assert!(out.stdout.is_empty());
            assert!(out.stderr.is_empty());
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[cfg(unix)]
#[test]
fn non_unicode_path_arguments_report_io_errors_not_panics() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    let dir = scratch_dir();
    let missing = dir.join(OsString::from_vec(b"missing-\xff.tmbc".to_vec()));
    let reference = write(&dir, "reference.tmbc", &bin(&module(BinOp::Add)));
    // A lossy conversion would compare the reference to this equal decoy.
    std::fs::write(missing.to_string_lossy().as_ref(), bin(&module(BinOp::Add))).unwrap();
    for args in [
        [missing.as_path(), reference.as_path()],
        [reference.as_path(), missing.as_path()],
    ] {
        let out = run(&args, &[]);
        assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
        assert!(out.stdout.is_empty());
        assert!(stderr(&out).contains("read "));
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[cfg(unix)]
#[test]
fn non_unicode_format_values_report_usage_errors_not_panics() {
    use std::ffi::{OsStr, OsString};
    use std::os::unix::ffi::OsStringExt;

    let value = OsString::from_vec(vec![0xff]);
    let inline = OsString::from_vec(b"--format=\xff".to_vec());
    for args in [
        vec![OsStr::new("--format"), value.as_os_str()],
        vec![inline.as_os_str()],
    ] {
        let out = Command::new(bin_path()).args(args).output().unwrap();
        assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
        assert!(out.stdout.is_empty());
        assert!(stderr(&out).contains("error:"));
    }
}

#[cfg(unix)]
#[test]
fn unknown_option_diagnostics_distinguish_invalid_bytes_from_replacement_text() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    let args = [
        OsString::from_vec(b"--bad-\xfe".to_vec()),
        OsString::from_vec(b"--bad-\xff".to_vec()),
        OsString::from("--bad-\u{fffd}"),
    ];
    let mut diagnostics = Vec::new();
    for arg in &args {
        let out = Command::new(bin_path()).arg(arg).output().unwrap();
        assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
        assert!(out.stdout.is_empty());
        assert!(stderr(&out).contains("unknown option:"));
        assert!(std::str::from_utf8(&out.stderr).is_ok());
        diagnostics.push(out.stderr);
    }
    for (i, diagnostic) in diagnostics.iter().enumerate() {
        for other in &diagnostics[i + 1..] {
            assert_ne!(
                diagnostic, other,
                "distinct option bytes lost in diagnostics"
            );
        }
    }
}
