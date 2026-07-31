// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir convert` — including the 4-format round-trip
//! acceptance criterion from issue #61.

mod common;

use std::fs;

use tempfile::tempdir;

use common::{build_valid_module, trust_ir_cmd};

fn run_convert(
    from: &str,
    to: &str,
    input: &std::path::Path,
    output: &std::path::Path,
) -> std::process::Output {
    trust_ir_cmd()
        .arg("convert")
        .arg("--from")
        .arg(from)
        .arg("--to")
        .arg(to)
        .arg(input)
        .arg(output)
        .output()
        .expect("run trust-ir")
}

#[test]
fn convert_bin_to_json_succeeds() {
    let dir = tempdir().expect("tempdir");
    let bin_path = dir.path().join("m.tmbc");
    let json_path = dir.path().join("m.json");
    let module = build_valid_module();
    fs::write(&bin_path, trust_ir::binary::serialize_module(&module)).expect("write");

    let out = run_convert("bin", "json", &bin_path, &json_path);
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let bytes = fs::read(&json_path).expect("read json");
    let decoded: trust_ir::Module = serde_json::from_slice(&bytes).expect("json decode");
    assert_eq!(decoded, module);
}

/// Acceptance criterion (#61): `trust-ir dump` round-trips through all four
/// formats. We exercise the CLI's `convert` chain rather than `dump` (which
/// only writes text to stdout); the invariant under test is that the CLI
/// preserves the module across every supported format transition.
///
/// NB: the text format is intentionally lossy for a handful of
/// bookkeeping fields — in particular `Module::func_types` and function-
/// level `proofs` are not serialized in v1 text (see
/// `crates/trust_ir/src/display.rs`). This test therefore runs two chains:
///
///   1. Lossless formats only: bin → json → msgpack → bin (module equality).
///   2. Every format including text: bin → text → json → msgpack → bin
///      (pipeline completes without error; text→text is already covered by
///      the parser's own round-trip tests).
#[test]
fn convert_round_trip_through_all_four_formats() {
    let dir = tempdir().expect("tempdir");
    let original = build_valid_module();

    // ---- Chain 1: lossless formats (strict module equality) ----
    let bin_path = dir.path().join("m.tmbc");
    fs::write(&bin_path, trust_ir::binary::serialize_module(&original)).expect("write");

    let json_path = dir.path().join("m.json");
    let out = run_convert("bin", "json", &bin_path, &json_path);
    assert!(
        out.status.success(),
        "bin->json: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let msg_path = dir.path().join("m.msgpack");
    let out = run_convert("json", "msgpack", &json_path, &msg_path);
    assert!(
        out.status.success(),
        "json->msgpack: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let bin2_path = dir.path().join("m_back.tmbc");
    let out = run_convert("msgpack", "bin", &msg_path, &bin2_path);
    assert!(
        out.status.success(),
        "msgpack->bin: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let final_bytes = fs::read(&bin2_path).expect("read bin2");
    let final_module = trust_ir::binary::deserialize_module(&final_bytes).expect("decode bin2");
    assert_eq!(
        final_module, original,
        "lossless round-trip (bin -> json -> msgpack -> bin) must preserve the module"
    );

    // ---- Chain 2: every format including text (pipeline completes) ----
    // We cannot assert module equality here: the v1 text format deliberately
    // omits Module::func_types and Function::proofs (see display.rs). The
    // invariant we CAN check is that every CLI step returns success and
    // produces a file the next step can read.
    let text_path = dir.path().join("m_text.trust_ir");
    let out = run_convert("bin", "text", &bin_path, &text_path);
    assert!(
        out.status.success(),
        "bin->text: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(fs::metadata(&text_path).expect("text exists").len() > 0);

    let json2_path = dir.path().join("m2.json");
    let out = run_convert("text", "json", &text_path, &json2_path);
    assert!(
        out.status.success(),
        "text->json: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let msg2_path = dir.path().join("m2.msgpack");
    let out = run_convert("json", "msgpack", &json2_path, &msg2_path);
    assert!(
        out.status.success(),
        "json->msgpack: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let bin3_path = dir.path().join("m2_back.tmbc");
    let out = run_convert("msgpack", "bin", &msg2_path, &bin3_path);
    assert!(
        out.status.success(),
        "msgpack->bin: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    // Final sanity check: the final binary is a valid TrustIr blob with the
    // TRUST_IR magic and can be re-decoded.
    let tail_bytes = fs::read(&bin3_path).expect("read bin3");
    assert!(tail_bytes.starts_with(b"TRUST_IR"));
    let _final2 = trust_ir::binary::deserialize_module(&tail_bytes).expect("final decode");
}

#[test]
fn convert_text_to_bin_produces_valid_trust_ir_file() {
    let dir = tempdir().expect("tempdir");
    let text_path = dir.path().join("m_text.trust_ir");
    let bin_path = dir.path().join("m.tmbc");
    fs::write(&text_path, format!("{}", build_valid_module())).expect("write");

    let out = run_convert("text", "bin", &text_path, &bin_path);
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let bytes = fs::read(&bin_path).expect("read");
    assert!(
        bytes.starts_with(b"TRUST_IR"),
        "binary output must carry the TRUST_IR magic"
    );
}
