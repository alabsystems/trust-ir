// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap WS4.9 remainder: `trust-ir-fmt` resolves its input through the ONE
// rule every TrustIr tool shares (`trust_ir::codec::resolve_module_format`)
// and reads all four transports. Before it read TEXT only, so a producer's
// `CRATE.trust-ir.bin` — the artifact trustc publishes — could not be
// canonicalized without a `trust-ir convert` first, and a trust-cg `tMBC`
// container or a mis-named file failed as an opaque text parse error.

use std::ffi::OsStr;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use trust_ir::{
    BinOp, Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, StructDef, StructId,
    StructRepr, Ty, ValueId,
};

fn bin_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-ir-fmt"))
}

fn scratch_dir() -> PathBuf {
    static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "trust-ir-fmt-formats-{}-{}",
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

fn run<S: AsRef<OsStr>>(args: &[S], stdin: Option<&[u8]>) -> Output {
    let mut child = Command::new(bin_path())
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn trust-ir-fmt");
    {
        let mut pipe = child.stdin.take().unwrap();
        if let Some(bytes) = stdin {
            pipe.write_all(bytes).unwrap();
        }
    }
    child.wait_with_output().unwrap()
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// `f(p: i32) -> i32 { p * p }`, with SPARSE ids so canonicalization has
/// something to renumber.
fn module() -> Module {
    let mut m = Module::new("fmt_formats");
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(7);
    let mut f = Function::new(FuncId::new(0), "f", ft, entry);
    let mut blk = Block::new(entry);
    blk.params.push((ValueId::new(40), Ty::I32));
    blk.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Mul,
            ty: Ty::I32,
            lhs: ValueId::new(40),
            rhs: ValueId::new(40),
        })
        .with_result(ValueId::new(41)),
    );
    blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(41)],
    }));
    f.blocks.push(blk);
    m.functions.push(f);
    m
}

fn canonical(m: &Module) -> String {
    trust_ir::format::canonical_checked(m).expect("the fixture is loss-free")
}

fn bin(m: &Module) -> Vec<u8> {
    trust_ir::binary::serialize_module(m).expect("serialize_module: test fixture")
}

fn text(m: &Module) -> Vec<u8> {
    trust_ir::format::text_checked(m).unwrap().into_bytes()
}

/// Every transport canonicalizes to the SAME text — the canonical form of
/// the module itself — so producers emitting different transports diff clean.
#[test]
fn every_transport_formats_to_the_same_canonical_text() {
    let dir = scratch_dir();
    let m = module();
    let expected = canonical(&m);
    for (name, bytes) in [
        ("m.trust-ir.bin", bin(&m)),
        ("m.tmbc", bin(&m)),
        ("m.bin", bin(&m)),
        ("m.trust-ir.txt", text(&m)),
        ("m.trust_ir", text(&m)),
        ("m.json", serde_json::to_vec(&m).unwrap()),
        ("m.msgpack", rmp_serde::to_vec(&m).unwrap()),
    ] {
        let path = write(&dir, name, &bytes);
        let out = run(&[path.to_str().unwrap()], None);
        assert_eq!(out.status.code(), Some(0), "{name}: {}", stderr(&out));
        assert_eq!(stdout(&out), expected, "{name}");
    }
}

/// Stdin (`-`) says nothing by name: the content decides — text as before,
/// and now binary too.
#[test]
fn stdin_is_sniffed() {
    let m = module();
    let expected = canonical(&m);
    for bytes in [text(&m), bin(&m)] {
        let out = run(&["-"], Some(&bytes));
        assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
        assert_eq!(stdout(&out), expected);
    }
}

/// The canonical form stays idempotent through the new front door.
#[test]
fn formatting_is_idempotent() {
    let dir = scratch_dir();
    let first = run(
        &[write(&dir, "m.tmbc", &bin(&module())).to_str().unwrap()],
        None,
    );
    assert_eq!(first.status.code(), Some(0), "{}", stderr(&first));
    let again = run(&["-"], Some(&first.stdout));
    assert_eq!(again.status.code(), Some(0), "{}", stderr(&again));
    assert_eq!(stdout(&again), stdout(&first));
}

/// Negative twins, each refused by its SPECIFIC reason (exit 1).
#[test]
fn refusals_are_named() {
    let dir = scratch_dir();
    let m = module();
    let mut container = b"tMBC".to_vec();
    container.extend_from_slice(&bin(&m));
    for name in ["c.tmbc", "c.trust-ir.bin", "c.bin"] {
        let path = write(&dir, name, &container);
        let out = run(&[path.to_str().unwrap()], None);
        assert_eq!(out.status.code(), Some(1), "{name}");
        assert!(
            stderr(&out).contains("this is a trust-cg tMBC container, not a trust-ir module"),
            "{name}: {}",
            stderr(&out)
        );
        assert!(out.stdout.is_empty());
    }
    let lying = write(&dir, "lying.trust_ir", &bin(&m));
    let out = run(&[lying.to_str().unwrap()], None);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        stderr(&out).contains("the file name says text but the content says TrustIr binary"),
        "{}",
        stderr(&out)
    );
    let unnamed = write(&dir, "m.bin", &rmp_serde::to_vec(&m).unwrap());
    let out = run(&[unnamed.to_str().unwrap()], None);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        stderr(&out).contains("cannot auto-detect format"),
        "{}",
        stderr(&out)
    );
}

/// `--format` overrides detection and is never second-guessed — the mutation
/// control for the container refusal: forced to `bin`, the container reaches
/// the BINARY DECODER and fails there, never with the resolver's message.
#[test]
fn explicit_format_wins() {
    let dir = scratch_dir();
    let m = module();
    let unnamed = write(&dir, "m.bin", &rmp_serde::to_vec(&m).unwrap());
    for flags in [&["--format", "msgpack"][..], &["--format=msgpack"][..]] {
        let mut args = flags.to_vec();
        args.push(unnamed.to_str().unwrap());
        let out = run(&args, None);
        assert_eq!(out.status.code(), Some(0), "{flags:?}: {}", stderr(&out));
        assert_eq!(stdout(&out), canonical(&m));
    }
    let mut container = b"tMBC".to_vec();
    container.extend_from_slice(&bin(&m));
    let path = write(&dir, "c.tmbc", &container);
    let out = run(&["--format", "bin", path.to_str().unwrap()], None);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        stderr(&out).contains("binary decode error"),
        "{}",
        stderr(&out)
    );
    assert!(!stderr(&out).contains("tMBC container"), "{}", stderr(&out));

    let out = run(&["--format", "binary", path.to_str().unwrap()], None);
    assert_eq!(
        out.status.code(),
        Some(2),
        "a bad --format value is a usage error"
    );
    assert!(
        stderr(&out).contains("invalid --format value"),
        "{}",
        stderr(&out)
    );
}

/// A binary module carrying a field text cannot hold is REFUSED with the
/// loss list (WS4.2 `canonical_checked`), never printed without it: the
/// binary front door must not become a way to launder a loss. The lossy
/// field is a struct with an empty name, which text cannot spell
/// (`TextLoss::UnspellableName`). It was `global_asm` until WS4.5 made text
/// carry `global_asm` (24e1ef5c); from then on this test printed the module
/// with exit 0 and failed, so the loss it names had to move to a field text
/// still drops.
#[test]
fn a_lossy_binary_input_is_refused() {
    let dir = scratch_dir();
    let mut m = module();
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: String::new(),
        fields: Vec::new(),
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    let path = write(&dir, "lossy.tmbc", &bin(&m));
    let out = run(&[path.to_str().unwrap()], None);
    assert_eq!(out.status.code(), Some(1), "stdout: {}", stdout(&out));
    assert!(out.stdout.is_empty());
    assert!(
        stderr(&out).contains("unspellable-name(struct 0)"),
        "{}",
        stderr(&out)
    );
}

/// OS paths must reach the file reader unchanged, including when a lossy
/// Unicode spelling happens to name a different, valid input.
#[cfg(target_os = "linux")]
#[test]
fn non_unicode_file_paths_preserve_the_exact_input() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    let dir = scratch_dir();
    let path = dir.join(OsString::from_vec(b"module-\xff.msgpack".to_vec()));
    let m = module();
    std::fs::write(&path, rmp_serde::to_vec(&m).unwrap()).unwrap();
    let mut other = module();
    other.name = "wrong_lossy_path".into();
    std::fs::write(
        path.to_string_lossy().as_ref(),
        rmp_serde::to_vec(&other).unwrap(),
    )
    .unwrap();
    assert!(path.to_str().is_none());

    for flags in [
        vec![path.as_os_str()],
        vec![
            OsStr::new("--format"),
            OsStr::new("msgpack"),
            path.as_os_str(),
        ],
        vec![OsStr::new("--format=msgpack"), path.as_os_str()],
    ] {
        let out = run(&flags, None);
        assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
        assert_eq!(stdout(&out), canonical(&m));
        assert!(out.stderr.is_empty());
    }
    std::fs::remove_dir_all(dir).unwrap();
}

/// Even where the filesystem rejects such a name, argv itself can carry it.
/// It must reach the file-error path instead of panicking during argument parsing.
#[cfg(unix)]
#[test]
fn non_unicode_path_argument_is_an_io_error_not_a_panic() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    let dir = scratch_dir();
    let path = dir.join(OsString::from_vec(b"missing-\xff.tmbc".to_vec()));
    // A lossy conversion would open this valid decoy and incorrectly succeed.
    std::fs::write(path.to_string_lossy().as_ref(), bin(&module())).unwrap();
    let out = run(&[path.as_os_str()], None);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(out.stdout.is_empty());
    assert!(stderr(&out).contains("failed to read"));
    std::fs::remove_dir_all(dir).unwrap();
}

#[cfg(unix)]
#[test]
fn non_unicode_option_values_are_usage_errors_not_panics() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    let value = OsString::from_vec(vec![0xff]);
    let inline = OsString::from_vec(b"--format=\xff".to_vec());
    for args in [
        vec![OsStr::new("--format"), value.as_os_str(), OsStr::new("-")],
        vec![inline.as_os_str(), OsStr::new("-")],
    ] {
        let out = run(&args, None);
        assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
        assert!(out.stdout.is_empty());
        assert!(stderr(&out).contains("USAGE:"));
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
        let out = run(&[arg.as_os_str()], None);
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
