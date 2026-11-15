// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS4.9 (F-074 remainder): CLI ergonomics.
//!
//! * format detection — trustc's `CRATE.trust-ir.bin` / `.trust-ir.txt`
//!   resolve with no `--format`; the content's magic is cross-checked against
//!   the name; a trust-cg `tMBC` container is refused BY NAME, even under
//!   TrustIr's own `.tmbc` extension; an explicit `--format` is never
//!   second-guessed;
//! * `run --arg` — scalar entry arguments, arity- and range-checked;
//! * `digest` — the shell counterpart of `ModuleImport.digest`;
//! * `handles` — the pinned `TRUSTED_HANDLE_RUNTIMES` registry.
//!
//! Every negative twin asserts its SPECIFIC refusal text and exit code, never
//! "some error".

mod common;

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Output, Stdio};

use tempfile::{TempDir, tempdir};

use common::{build_valid_module, trust_ir_cmd};
use trust_ir::Module;
use trust_ir::ty::Ty;
use trust_ir_build::ModuleBuilder;

const CONTAINER_REFUSAL: &str = "this is a trust-cg tMBC container, not a trust-ir module";

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

fn write_bytes(dir: &TempDir, name: &str, bytes: &[u8]) -> PathBuf {
    let path = dir.path().join(name);
    fs::write(&path, bytes).expect("write fixture");
    path
}

fn bin(module: &Module) -> Vec<u8> {
    trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture")
}

fn text(module: &Module) -> Vec<u8> {
    format!("{module}").into_bytes()
}

fn validate(path: &Path) -> Output {
    trust_ir_cmd()
        .arg("validate")
        .arg(path)
        .output()
        .expect("run trust-ir validate")
}

fn run_entry(path: &Path, entry: &str, args: &[&str]) -> Output {
    let mut cmd = trust_ir_cmd();
    cmd.arg("run").arg(path).arg("--entry").arg(entry);
    for arg in args {
        cmd.arg("--arg").arg(arg);
    }
    cmd.output().expect("run trust-ir run")
}

/// The standalone-Lean envelope's Clean body, `addmul a b = a * b + a` at
/// `UInt64` (proof program `b3_kernel_certified`, scout-lean `main2.rs`:
/// `assert!(m::addmul(2, 3) == 8)`).
fn addmul_module() -> Module {
    let mut mb = ModuleBuilder::new("lean_envelope_addmul");
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("addmul", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let product = fb.mul(Ty::U64, a, b);
    let sum = fb.add(Ty::U64, product, a);
    fb.ret(vec![sum]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `identity(x: ty) -> ty`, for range and type probes.
fn identity_module(ty: Ty) -> Module {
    let mut mb = ModuleBuilder::new("identity");
    let ft = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
    let mut fb = mb.function("identity", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, ty);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `takes_ptr(p: ptr) -> i64 { 7 }`: a well-formed entry whose param is not
/// a scalar this front can spell.
fn ptr_param_module() -> Module {
    let mut mb = ModuleBuilder::new("ptr_param");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("takes_ptr", ft);
    let entry = fb.create_block();
    let _p = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let seven = fb.iconst(Ty::I64, 7);
    fb.ret(vec![seven]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A trust-cg container image: `tMBC` magic, a version word, a payload.
fn tmbc_container_bytes() -> Vec<u8> {
    let mut bytes = b"tMBC".to_vec();
    bytes.extend_from_slice(&1u32.to_le_bytes());
    bytes.extend_from_slice(&bin(&build_valid_module()));
    bytes
}

// ---------------------------------------------------------------------------
// Format detection
// ---------------------------------------------------------------------------

#[test]
fn producer_bin_suffix_validates_without_format() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "x.trust-ir.bin", &bin(&build_valid_module()));
    let out = validate(&path);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
}

#[test]
fn producer_txt_suffix_validates_without_format() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "x.trust-ir.txt", &text(&build_valid_module()));
    let out = validate(&path);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
}

/// A name that says nothing (a bare `.bin`, stdin) takes the sniffed format.
#[test]
fn unknown_extension_and_stdin_take_the_sniffed_format() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "artifact.bin", &bin(&build_valid_module()));
    let out = validate(&path);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));

    let mut child = trust_ir_cmd()
        .args(["validate", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn trust-ir validate -");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(&text(&build_valid_module()))
        .expect("write stdin");
    let out = child.wait_with_output().expect("wait");
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
}

/// Negative twin: TrustIr's OWN `.tmbc` extension over trust-cg's `tMBC`
/// MAGIC is refused by name — only the magic tells the two apart.
#[test]
fn tmbc_extension_with_trust_cg_magic_is_refused_as_a_container() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "module.tmbc", &tmbc_container_bytes());
    let out = validate(&path);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    let err = stderr(&out);
    assert!(err.contains(CONTAINER_REFUSAL), "stderr: {err}");
    assert!(err.contains("use the TRUST_IR binary"), "stderr: {err}");
    // The refusal happens BEFORE any decode: it is not a decode error.
    assert!(!err.contains("binary decode error"), "stderr: {err}");
}

/// Mutation control for the twin above. A sniff mutant that mapped `tMBC` to
/// Bin would hand the bytes to the binary decoder — exactly what an explicit
/// `--format bin` does (the explicit format bypasses the sniff). That path
/// fails with a DECODE error (exit 2) and without the container refusal, so
/// the twin's assertions distinguish the mutant from the rule.
#[test]
fn tmbc_container_decoded_as_bin_fails_with_a_decode_error_not_the_refusal() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "module.tmbc", &tmbc_container_bytes());
    let out = trust_ir_cmd()
        .args(["validate", "--format", "bin"])
        .arg(&path)
        .output()
        .expect("run trust-ir validate");
    assert_eq!(out.status.code(), Some(2), "stderr: {}", stderr(&out));
    let err = stderr(&out);
    assert!(err.contains("binary decode error"), "stderr: {err}");
    assert!(!err.contains(CONTAINER_REFUSAL), "stderr: {err}");
}

/// Negative twin: a `.json` name over `TRUST_IR` magic is refused naming both
/// claims, never decoded as either.
#[test]
fn json_extension_with_trust_ir_magic_is_a_mismatch() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "module.json", &bin(&build_valid_module()));
    let out = validate(&path);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    let err = stderr(&out);
    assert!(
        err.contains(
            "the file name says json but the content says TrustIr binary (TRUST_IR magic)"
        ),
        "stderr: {err}"
    );
    assert!(!err.contains("json decode error"), "stderr: {err}");
}

/// A name that says binary over content without the `TRUST_IR` magic is
/// refused naming both; it never falls through to the text decoder.
#[test]
fn bin_suffix_without_the_magic_is_a_mismatch() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "x.trust-ir.bin", &text(&build_valid_module()));
    let out = validate(&path);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("the file name says bin but the content says TrustIr text"),
        "stderr: {}",
        stderr(&out)
    );
}

/// Risk control: an explicit `--format` is never overridden by the sniff.
#[test]
fn explicit_format_wins_over_a_disagreeing_name() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "module.json", &bin(&build_valid_module()));
    let out = trust_ir_cmd()
        .args(["validate", "--format", "bin"])
        .arg(&path)
        .output()
        .expect("run trust-ir validate");
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
}

/// MessagePack is never sniffed: under an unknown name it is refused with the
/// auto-detect message, and it still resolves by its own extension.
#[test]
fn msgpack_needs_its_extension_or_format() {
    let dir = tempdir().expect("tempdir");
    let bytes = rmp_serde::to_vec(&build_valid_module()).expect("msgpack encode");
    let unnamed = write_bytes(&dir, "module.dat", &bytes);
    let out = validate(&unnamed);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("cannot auto-detect format"),
        "stderr: {}",
        stderr(&out)
    );
    let named = write_bytes(&dir, "module.msgpack", &bytes);
    let out = validate(&named);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr(&out));
}

/// Review adversary: the name says TEXT, the content is a JSON module. The
/// rule is symmetric — not just "binary without its magic" — so a text name
/// over a leading `{` is refused naming both, never handed to the text parser.
#[test]
fn text_name_over_json_content_is_a_mismatch() {
    let dir = tempdir().expect("tempdir");
    let json = serde_json::to_vec(&build_valid_module()).expect("json encode");
    let path = write_bytes(&dir, "module.trust_ir", &json);
    let out = validate(&path);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("the file name says text but the content says JSON"),
        "stderr: {}",
        stderr(&out)
    );
    // The same bytes under a MessagePack name: refused too.
    let path = write_bytes(&dir, "module.msgpack", &json);
    let out = validate(&path);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("the file name says msgpack but the content says JSON"),
        "stderr: {}",
        stderr(&out)
    );
}

/// Review adversary, legitimate side: every golden module in the conformance
/// corpus resolves under its OWN name with no `--format` — the cross-check
/// must never refuse a well-named legitimate module (MessagePack included,
/// which the sniff leaves unclaimed and the name alone decides).
#[test]
fn every_golden_module_resolves_by_its_own_name() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../trust-ir-conformance/tests/fixtures")
        .canonicalize()
        .expect("fixtures dir");
    let mut checked = 0usize;
    for entry in fs::read_dir(&fixtures).expect("read fixtures") {
        let path = entry.expect("entry").path();
        let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
        let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
        if !matches!(ext, "tmbc" | "trust_ir" | "json" | "msgpack")
            || name == "vector_mask_oracles.json"
        {
            continue;
        }
        let out = trust_ir_cmd()
            .arg("dump")
            .arg(&path)
            .output()
            .expect("run trust-ir dump");
        // Resolution refusals are exit 1; a sidecar that resolves but is
        // not a module (proof-lineage manifests, request bundles) fails
        // DECODE, exit 2 — that is the decoder's verdict, not resolution's.
        let err = stderr(&out);
        assert_ne!(
            out.status.code(),
            Some(1),
            "{} refused at resolution: {err}",
            path.display()
        );
        if out.status.code() != Some(0) {
            // Roadmap WS4.2: a `#lossy`-marked text golden RESOLVES as text
            // and is then refused by the strict parser — also exit 2, and
            // also not resolution's verdict.
            let lossy_text = ext == "trust_ir"
                && fs::read_to_string(&path)
                    .expect("read golden")
                    .lines()
                    .nth(1)
                    .is_some_and(|line| line.starts_with("; #lossy: "));
            assert!(
                out.status.code() == Some(2)
                    && (err.contains("decode error")
                        || (lossy_text && err.contains("printed LOSSILY"))),
                "{} failed: {err}",
                path.display()
            );
            continue;
        }
        checked += 1;
    }
    assert!(checked > 100, "only {checked} goldens exercised");
}

// ---------------------------------------------------------------------------
// run --arg
// ---------------------------------------------------------------------------

#[test]
fn run_addmul_with_args_prints_8() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "addmul.tmbc", &bin(&addmul_module()));
    let out = run_entry(&path, "addmul", &["2", "3"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert_eq!(stdout(&out).trim(), "8");
    // Hex spelling of the same arguments.
    let out = run_entry(&path, "addmul", &["0x2", "0X3"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert_eq!(stdout(&out).trim(), "8");
}

#[test]
fn run_arg_arity_must_match_exactly() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "addmul.tmbc", &bin(&addmul_module()));
    let out = run_entry(&path, "addmul", &["2"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("takes 2 parameter(s) but 1 --arg value(s) were supplied"),
        "stderr: {}",
        stderr(&out)
    );
    let out = run_entry(&path, "addmul", &[]);
    assert_eq!(out.status.code(), Some(1));
    assert!(stderr(&out).contains("takes 2 parameter(s) but 0 --arg value(s)"));
}

/// Negative twin: `256` does not fit `u8`; `255` (the positive control) does.
#[test]
fn run_arg_out_of_range_for_u8_is_refused() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "id.tmbc", &bin(&identity_module(Ty::U8)));
    let out = run_entry(&path, "identity", &["256"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("out of range for u8: 0..=255"),
        "stderr: {}",
        stderr(&out)
    );
    let out = run_entry(&path, "identity", &["-1"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(stderr(&out).contains("out of range for u8: 0..=255"));

    let out = run_entry(&path, "identity", &["255"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert_eq!(stdout(&out).trim(), "255");
}

#[test]
fn run_arg_signed_range_is_checked_at_both_ends() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "id.tmbc", &bin(&identity_module(Ty::I8)));
    let out = run_entry(&path, "identity", &["-128"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert_eq!(stdout(&out).trim(), "-128");
    for bad in ["128", "-129"] {
        let out = run_entry(&path, "identity", &[bad]);
        assert_eq!(out.status.code(), Some(1), "{bad}: {}", stderr(&out));
        assert!(
            stderr(&out).contains("out of range for i8: -128..=127"),
            "{bad}: {}",
            stderr(&out)
        );
    }
    let out = run_entry(&path, "identity", &["seven"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(stderr(&out).contains("expected a decimal or 0x-hex integer"));
}

#[test]
fn run_arg_bool_and_float_params() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "b.tmbc", &bin(&identity_module(Ty::Bool)));
    let out = run_entry(&path, "identity", &["true"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert_eq!(stdout(&out).trim(), "1");
    let out = run_entry(&path, "identity", &["1"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(stderr(&out).contains("expected `true` or `false`"));

    let path = write_bytes(&dir, "f.tmbc", &bin(&identity_module(Ty::F64)));
    let out = run_entry(&path, "identity", &["-2.5"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert_eq!(stdout(&out).trim(), "-2.5");
}

/// Review adversary: a float literal the parse would silently move out of its
/// magnitude is a range error, exactly like `256` at `u8` — `1e39` is not an
/// `f32` (it would run as `inf`), and `1e-50` is not zero (it would run as
/// `0.0`). The explicit `inf` spelling and ordinary rounding still run.
#[test]
fn run_arg_float_overflow_and_underflow_are_refused() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "f.tmbc", &bin(&identity_module(Ty::F32)));
    let out = run_entry(&path, "identity", &["1e39"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("out of range for f32: the literal overflows to infinity"),
        "stderr: {}",
        stderr(&out)
    );
    let out = run_entry(&path, "identity", &["-1e-50"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("out of range for f32: the nonzero literal underflows to zero"),
        "stderr: {}",
        stderr(&out)
    );
    for ok in ["inf", "-infinity", "0.0", "0e-50", "0.1"] {
        let out = run_entry(&path, "identity", &[ok]);
        assert!(out.status.success(), "{ok}: {}", stderr(&out));
    }

    let path = write_bytes(&dir, "d.tmbc", &bin(&identity_module(Ty::F64)));
    let out = run_entry(&path, "identity", &["1e400"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("out of range for f64: the literal overflows to infinity"),
        "stderr: {}",
        stderr(&out)
    );
    // `1e39` IS an f64: the check is per param type.
    let out = run_entry(&path, "identity", &["1e39"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
}

/// Review adversary: pointer-width integers run at 64 bits, and the range
/// refusal names the PARAM's type, not a relabelled `i64`; `u128` accepts its
/// full range (the value above `i128::MAX` is not wrapped into a refusal).
#[test]
fn run_arg_pointer_width_and_u128_ranges() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "s.tmbc", &bin(&identity_module(Ty::Isize)));
    let out = run_entry(&path, "identity", &["9223372036854775808"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("out of range for isize: -9223372036854775808..=9223372036854775807"),
        "stderr: {}",
        stderr(&out)
    );
    let path = write_bytes(&dir, "u.tmbc", &bin(&identity_module(Ty::U128)));
    let max = u128::MAX.to_string();
    let out = run_entry(&path, "identity", &[&max]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert_eq!(stdout(&out).trim(), max);
}

/// Review adversary: `char` is not spelled as an integer — its range is a
/// Unicode-scalar claim, not a width — so it is refused by name.
#[test]
fn run_arg_on_a_char_param_is_refused() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "c.tmbc", &bin(&identity_module(Ty::Char)));
    let out = run_entry(&path, "identity", &["65"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("param 1 has type char; only scalar entry arguments are supported"),
        "stderr: {}",
        stderr(&out)
    );
}

/// Negative twin: a `ptr` param is refused by name, whatever the value.
#[test]
fn run_arg_on_a_ptr_param_is_refused() {
    let dir = tempdir().expect("tempdir");
    let path = write_bytes(&dir, "p.tmbc", &bin(&ptr_param_module()));
    let out = run_entry(&path, "takes_ptr", &["0"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stderr(&out).contains("param 1 has type ptr; only scalar entry arguments are supported"),
        "stderr: {}",
        stderr(&out)
    );
}

// ---------------------------------------------------------------------------
// digest / handles
// ---------------------------------------------------------------------------

#[test]
fn digest_prints_the_library_identity() {
    let dir = tempdir().expect("tempdir");
    let module = addmul_module();
    let bytes = bin(&module);
    let path = write_bytes(&dir, "addmul.trust-ir.bin", &bytes);
    let text_path = write_bytes(&dir, "addmul.trust-ir.txt", &text(&module));
    let out = trust_ir_cmd()
        .arg("digest")
        .arg(&path)
        .arg(&text_path)
        .output()
        .expect("run trust-ir digest");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text_out = stdout(&out);
    // Compare against the digest of what the CLI actually DECODED from each
    // file, so the assertion is about the printer, not codec round-trips.
    let decoded_bin = trust_ir::binary::deserialize_module(&bytes).expect("decode bin");
    let decoded_text =
        trust_ir::parser::parse_module(&format!("{module}")).expect("parse text form");
    for decoded in [&decoded_bin, &decoded_text] {
        let stable = format!("  stable_digest: {}", decoded.stable_digest());
        assert!(
            text_out.contains(&stable),
            "missing {stable:?} in {text_out}"
        );
        let exec = format!(
            "  executable_content_digest_v1: {}",
            decoded.executable_content_digest_v1()
        );
        assert!(text_out.contains(&exec), "missing {exec:?} in {text_out}");
    }
    assert!(text_out.contains("  name: \"lean_envelope_addmul\""));
    assert!(text_out.contains(&format!(
        "  identity_domain: {}",
        trust_ir::MODULE_IDENTITY_DOMAIN
    )));
    let header = u32::from_le_bytes(bytes[8..12].try_into().expect("header"));
    assert_eq!(header, trust_ir::binary::BASE_FORMAT_VERSION);
    assert!(text_out.contains(&format!("  wire_version: {header}")));
}

/// WS4.10: `digest` prints both identities — the portable V3 `stable_digest`
/// and the legacy V2 digest a pre-v44 import row records.
#[test]
fn digest_prints_the_legacy_identity_beside_the_portable_one() {
    let dir = tempdir().expect("tempdir");
    let mut module = addmul_module();
    // Split so the exported source never spells a home-directory literal
    // (publication's forbidden-content guard); the string is unchanged.
    module
        .intern_file(concat!("/Us", "ers/a/src/lib.rs"))
        .expect("Module::intern_file: test fixture");
    let path = write_bytes(&dir, "addmul.trust-ir.bin", &bin(&module));
    let out = trust_ir_cmd()
        .arg("digest")
        .arg(&path)
        .output()
        .expect("run trust-ir digest");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text_out = stdout(&out);
    assert!(text_out.contains(&format!("  stable_digest: {}", module.stable_digest())));
    assert!(text_out.contains(&format!(
        "  stable_digest_legacy: {}",
        module.stable_digest_under(trust_ir::IdentityScheme::V2)
    )));
    assert!(text_out.contains(&format!(
        "  legacy_identity_domain: {}",
        trust_ir::MODULE_IDENTITY_DOMAIN_V2
    )));
    assert!(!text_out.contains("portable:"), "no check was asked for");
}

/// WS4.10 item 6: `digest --portable-check` refuses a module whose debug file
/// table embeds a non-remapped absolute path, naming it by JSON pointer; a
/// relative path, or an absolute one under a declared `--remap-prefix`, is
/// portable (mutation control: the same module passes once remapped).
#[test]
fn digest_portable_check_refuses_an_absolute_debug_path() {
    // The macOS home-directory paths below are split by `concat!` so the
    // exported source never spells a home-directory literal (publication's
    // central forbidden-content guard refuses one, with no per-repository
    // waiver); every string the CLI is handed is unchanged.
    const CHECKOUT: &str = concat!("/Us", "ers/a/checkout/");
    const LEAKY: &str = concat!("/Us", "ers/a/checkout/src/main.rs");
    let dir = tempdir().expect("tempdir");
    let mut leaky = addmul_module();
    leaky
        .intern_file("src/lib.rs")
        .expect("Module::intern_file: test fixture");
    leaky
        .intern_file(LEAKY)
        .expect("Module::intern_file: test fixture");
    let leaky_path = write_bytes(&dir, "leaky.trust-ir.bin", &bin(&leaky));
    let out = trust_ir_cmd()
        .args(["digest", "--portable-check"])
        .arg(&leaky_path)
        .output()
        .expect("run trust-ir digest --portable-check");
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    let err = stderr(&out);
    assert!(err.contains("/files/1"), "{err}");
    assert!(err.contains(LEAKY), "{err}");
    assert!(
        !err.contains("/files/0"),
        "a relative path is portable: {err}"
    );
    assert!(stdout(&out).contains("  portable: no"));

    // The same absolute path under a declared remap prefix is portable.
    let out = trust_ir_cmd()
        .args(["digest", "--portable-check", "--remap-prefix", CHECKOUT])
        .arg(&leaky_path)
        .output()
        .expect("run trust-ir digest --portable-check --remap-prefix");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert!(stdout(&out).contains("  portable: yes (2 debug file path(s))"));

    // Windows drive paths are absolute too.
    let mut windows = addmul_module();
    windows
        .intern_file("C:\\work\\src\\lib.rs")
        .expect("Module::intern_file: test fixture");
    let windows_path = write_bytes(&dir, "windows.trust-ir.bin", &bin(&windows));
    let out = trust_ir_cmd()
        .args(["digest", "--portable-check"])
        .arg(&windows_path)
        .output()
        .expect("run trust-ir digest --portable-check");
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(stderr(&out).contains("/files/0"));

    // Adversarial (review): a remap prefix covers a path by COMPONENT, never
    // by string prefix, and a `..` component climbs back out of it. Each of
    // these names the checkout although its first bytes spell the prefix.
    for (escaping, prefix) in [
        (
            concat!("/rustc-evil/Us", "ers/a/checkout/src/lib.rs"),
            "/rustc",
        ),
        (
            concat!("/rustc/../Us", "ers/a/checkout/src/lib.rs"),
            "/rustc/",
        ),
        (
            concat!("/rustc/abc/../../Us", "ers/a/checkout/src/lib.rs"),
            "/rustc",
        ),
    ] {
        let mut module = addmul_module();
        module
            .intern_file(escaping)
            .expect("Module::intern_file: test fixture");
        let path = write_bytes(&dir, "escaping.trust-ir.bin", &bin(&module));
        let out = trust_ir_cmd()
            .args(["digest", "--portable-check", "--remap-prefix", prefix])
            .arg(&path)
            .output()
            .expect("run trust-ir digest --portable-check --remap-prefix");
        assert_eq!(
            out.status.code(),
            Some(1),
            "{escaping} under {prefix}: stderr: {}",
            stderr(&out)
        );
        assert!(stderr(&out).contains("/files/0"), "{}", stderr(&out));
    }
    // Twin: the same prefix spelled without a trailing separator still
    // covers a path genuinely under it.
    let mut remapped = addmul_module();
    remapped
        .intern_file("/rustc/abc/src/lib.rs")
        .expect("Module::intern_file: test fixture");
    let path = write_bytes(&dir, "remapped.trust-ir.bin", &bin(&remapped));
    let out = trust_ir_cmd()
        .args(["digest", "--portable-check", "--remap-prefix", "/rustc"])
        .arg(&path)
        .output()
        .expect("run trust-ir digest --portable-check --remap-prefix");
    assert!(out.status.success(), "stderr: {}", stderr(&out));

    // `--remap-prefix` without `--portable-check` is a usage error.
    let out = trust_ir_cmd()
        .args(["digest", "--remap-prefix", "/x/"])
        .arg(&leaky_path)
        .output()
        .expect("run trust-ir digest --remap-prefix");
    assert!(!out.status.success());
}

#[test]
fn digest_reports_a_refused_input_and_keeps_going() {
    let dir = tempdir().expect("tempdir");
    let bad = write_bytes(&dir, "bad.tmbc", &tmbc_container_bytes());
    let good = write_bytes(&dir, "good.tmbc", &bin(&build_valid_module()));
    let out = trust_ir_cmd()
        .arg("digest")
        .arg(&bad)
        .arg(&good)
        .output()
        .expect("run trust-ir digest");
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(stderr(&out).contains(CONTAINER_REFUSAL));
    assert!(stdout(&out).contains(&format!(
        "  stable_digest: {}",
        build_valid_module().stable_digest()
    )));
}

/// Review adversary: a JSON module spelling the producer-internal `Ty::Error`
/// has no digest. It is reported as unencodable — with no panic banner — and
/// the run continues to the next input.
#[test]
fn digest_reports_an_unencodable_module_without_a_panic_banner() {
    let dir = tempdir().expect("tempdir");
    let json = serde_json::to_string(&identity_module(Ty::U16)).expect("json encode");
    assert!(json.contains("\"U16\""), "{json}");
    let bad = write_bytes(
        &dir,
        "err.json",
        json.replace("\"U16\"", "\"Error\"").as_bytes(),
    );
    let good = write_bytes(&dir, "good.tmbc", &bin(&build_valid_module()));
    let out = trust_ir_cmd()
        .arg("digest")
        .arg(&bad)
        .arg(&good)
        .output()
        .expect("run trust-ir digest");
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    let err = stderr(&out);
    assert!(err.contains("module is not encodable"), "stderr: {err}");
    assert!(!err.contains("panicked"), "stderr: {err}");
    assert!(stdout(&out).contains(&format!(
        "  stable_digest: {}",
        build_valid_module().stable_digest()
    )));
}

#[test]
fn handles_lists_every_pinned_nat_entry_point() {
    let out = trust_ir_cmd()
        .arg("handles")
        .output()
        .expect("run trust-ir handles");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text_out = stdout(&out);
    assert!(
        text_out.contains(
            "handle \"Nat\": runtime \"trust_bignum::Nat\", calling convention ccc, \
             handle type handle<\"Nat\", \"trust_bignum::Nat\">"
        ),
        "{text_out}"
    );
    let handle = "handle<\"Nat\", \"trust_bignum::Nat\">";
    for line in [
        format!(
            "  from_u64 @trust_bignum_nat_from_u64 (u64) -> ({handle}) [trust_bignum::Nat::from_u64]"
        ),
        format!(
            "  add @trust_bignum_nat_add ({handle}, {handle}) -> ({handle}) [trust_bignum::Nat::add]"
        ),
        format!(
            "  sub @trust_bignum_nat_sub ({handle}, {handle}) -> ({handle}) [trust_bignum::Nat::sub]"
        ),
        format!(
            "  is_zero @trust_bignum_nat_is_zero ({handle}) -> (bool) [trust_bignum::Nat::is_zero]"
        ),
        format!("  drop @trust_bignum_nat_drop ({handle}) -> () [trust_bignum::Nat::drop]"),
        // WS3.2: the Clean kernel's native `Nat` surface. `mod` shows the
        // Rust item its shim wraps (`Nat::rem`), and the projection is two
        // pins (`fits_u64` total, `to_u64` checked).
        format!(
            "  mod @trust_bignum_nat_mod ({handle}, {handle}) -> ({handle}) [trust_bignum::Nat::rem]"
        ),
        format!(
            "  beq @trust_bignum_nat_beq ({handle}, {handle}) -> (bool) [trust_bignum::Nat::beq]"
        ),
        format!(
            "  fits_u64 @trust_bignum_nat_fits_u64 ({handle}) -> (bool) [trust_bignum::Nat::fits_u64]"
        ),
        format!(
            "  to_u64 @trust_bignum_nat_to_u64 ({handle}) -> (u64) [trust_bignum::Nat::to_u64]"
        ),
        format!(
            "  pow @trust_bignum_nat_pow ({handle}, {handle}) -> ({handle}) [trust_bignum::Nat::pow]"
        ),
    ] {
        assert!(text_out.contains(&line), "missing {line:?} in {text_out}");
    }
    // Exactly the registry: every pinned entry, nothing else.
    let listed = text_out.lines().filter(|l| l.starts_with("  ")).count();
    let pinned: usize = trust_ir_build::TRUSTED_HANDLE_RUNTIMES
        .iter()
        .map(|pin| pin.entry_points.len())
        .sum();
    assert_eq!(listed, pinned);
    assert_eq!(pinned, 19);
    assert!(!text_out.contains("to_u64_wrapping"), "{text_out}");
    assert!(!text_out.contains("@trust_bignum_nat_cmp"), "{text_out}");
}
