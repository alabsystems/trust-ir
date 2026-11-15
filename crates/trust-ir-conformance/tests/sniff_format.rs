// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS4.9: `trust_ir::codec::sniff_format`'s table test, run over the WHOLE
//! checked-in golden corpus plus the synthetic edge rows.
//!
//! It lives here rather than in core `trust-ir` because core's own tests run
//! in no gate; this file is on gate 8's `--test` list (`scripts/ci_gates.sh`).
//! Every golden must sniff as what its extension says — or, for MessagePack
//! and the lineage-manifest sidecar, as NOTHING, because MessagePack is never
//! sniffed and a `TMPL` sidecar is not a module.

use std::fs;
use std::path::PathBuf;

use trust_ir::codec::{SniffedFormat, TRUST_CG_CONTAINER_MAGIC, sniff_format};

/// JSON goldens that are NOT serialized modules: a top-level JSON ARRAY of
/// oracle rows. A module's serde form is always an object, so the sniff
/// deliberately claims only a leading `{`; these must stay unclaimed.
const NON_MODULE_JSON: &[&str] = &["vector_mask_oracles.json"];

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

#[test]
fn every_golden_sniffs_as_its_extension_says() {
    let mut checked = [0usize; 5];
    for entry in fs::read_dir(fixtures_dir()).expect("read fixtures dir") {
        let path = entry.expect("dir entry").path();
        if !path.is_file() {
            continue;
        }
        let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
        let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
        let (slot, expected) = match ext {
            "json" if NON_MODULE_JSON.contains(&name) => (4, None),
            "tmbc" => (0, Some(SniffedFormat::Binary)),
            "json" => (1, Some(SniffedFormat::Json)),
            "trust_ir" => (2, Some(SniffedFormat::Text)),
            "msgpack" => (3, None),
            "trust_irpl" => (4, None),
            other => panic!(
                "unclassified golden extension {other:?} ({}): extend this table",
                path.display()
            ),
        };
        let bytes = fs::read(&path).expect("read golden");
        assert_eq!(
            sniff_format(&bytes),
            expected,
            "{} sniffed wrongly",
            path.display()
        );
        checked[slot] += 1;
    }
    // The corpus is not empty in any column this table claims to cover.
    for (slot, count) in checked.iter().enumerate() {
        assert!(*count > 0, "no golden exercised table column {slot}");
    }
}

/// `.tmbc` is TrustIr's OWN extension; the conformance corpus' `chc_batch.tmbc`
/// (the gate-4/gate-6 census input) carries the TRUST_IR magic, NOT trust-cg's
/// `tMBC` — the naming collision only the magic resolves.
#[test]
fn the_tmbc_extension_is_not_the_tmbc_magic() {
    let bytes = fs::read(fixtures_dir().join("chc_batch.tmbc")).expect("read chc_batch.tmbc");
    assert!(bytes.starts_with(b"TRUST_IR"));
    assert!(!bytes.starts_with(&TRUST_CG_CONTAINER_MAGIC));
    assert_eq!(sniff_format(&bytes), Some(SniffedFormat::Binary));
}

#[test]
fn synthetic_rows() {
    let rows: &[(&[u8], Option<SniffedFormat>)] = &[
        (b"TRUST_IR", Some(SniffedFormat::Binary)),
        (b"TRUST_IR\x2b\0\0\0rest", Some(SniffedFormat::Binary)),
        (b"tMBC", Some(SniffedFormat::TrustCgContainer)),
        (
            b"tMBC\x01\0\0\0TRUST_IR",
            Some(SniffedFormat::TrustCgContainer),
        ),
        // Amendment S: a template blob is claimed by its own magic, never as a module.
        (b"TRUST_IS", Some(SniffedFormat::TemplateBinary)),
        (
            b"TRUST_IS\x39\0\0\0rest",
            Some(SniffedFormat::TemplateBinary),
        ),
        (b"{", Some(SniffedFormat::Json)),
        (b"\r\n\t {\"name\": \"m\"}", Some(SniffedFormat::Json)),
        (b";", Some(SniffedFormat::Text)),
        (
            b"; TrustIr text format v1\nmodule \"m\"\n",
            Some(SniffedFormat::Text),
        ),
        (b"module \"m\"\n", Some(SniffedFormat::Text)),
        (b"  module \"m\"", Some(SniffedFormat::Text)),
        // Near-misses stay unclaimed.
        (b"", None),
        (b"   ", None),
        (b"TRUST_I", None),
        (b"tMB", None),
        (b"TMBC", None),
        (b" TRUST_IR", None),
        (b" tMBC", None),
        (b"module", None),
        (b"module m", None),
        (b"TMPL\x02\0\0\0", None),
        (b"[1, 2]", None),
        // MessagePack markers: never sniffed.
        (&[0xdc, 0x00, 0x13], None),
        (&[0x83, 0xae], None),
    ];
    for (bytes, expected) in rows {
        assert_eq!(sniff_format(bytes), *expected, "row {bytes:?}");
    }
}

// ---------------------------------------------------------------------------
// The shared resolution rule (`trust_ir::codec::resolve_module_format`)
// ---------------------------------------------------------------------------
//
// WS4.9 remainder / WS4.13: the rule the `trust-ir` CLI spelled privately is
// now ONE function in core, and `trust-ir-fmt` and `trust-ir-diff` resolve
// through it too. Its table lives here for the same reason the sniff's does:
// core's own tests run in no gate.

use std::path::Path;
use trust_ir::codec::{FormatRefusal, ModuleFormat, resolve_module_format};

const BIN: &[u8] = b"TRUST_IR\x2b\0\0\0";
const TMBC: &[u8] = b"tMBC\x01\0\0\0TRUST_IR";
const JSON: &[u8] = b"{\"name\":\"m\"}";
const TEXT: &[u8] = b"; TrustIr text format v1\nmodule \"m\"\n";
const MSGPACK: &[u8] = &[0xdc, 0x00, 0x13];

fn resolve(name: &str, bytes: &[u8]) -> Result<ModuleFormat, FormatRefusal> {
    resolve_module_format(None, Path::new(name), bytes)
}

#[test]
fn format_names_round_trip() {
    for format in ModuleFormat::ALL {
        assert_eq!(ModuleFormat::from_name(format.name()), Some(format));
    }
    assert_eq!(ModuleFormat::from_name("binary"), None);
    assert_eq!(ModuleFormat::from_name("BIN"), None);
    assert_eq!(ModuleFormat::from_name(""), None);
}

/// The name contract: trustc's full suffixes, then the single extensions; a
/// bare `.bin` / `.txt` says nothing.
#[test]
fn name_contract() {
    let by = |name: &str| ModuleFormat::from_path(Path::new(name));
    assert_eq!(by("out/foo.trust-ir.bin"), Some(ModuleFormat::Binary));
    assert_eq!(by("out/foo.trust-ir.txt"), Some(ModuleFormat::Text));
    assert_eq!(by("foo.tmbc"), Some(ModuleFormat::Binary));
    assert_eq!(by("foo.trust_ir"), Some(ModuleFormat::Text));
    assert_eq!(by("foo.json"), Some(ModuleFormat::Json));
    assert_eq!(by("foo.msgpack"), Some(ModuleFormat::Msgpack));
    assert_eq!(by("foo.bin"), None);
    assert_eq!(by("foo.txt"), None);
    assert_eq!(by("-"), None);
    assert_eq!(by("foo"), None);
}

/// Positive rows: a name the content agrees with, a name that says nothing
/// (the content decides), and the formats a sniff leaves to their decoder.
#[test]
fn resolution_accepts_agreeing_and_silent_names() {
    let rows: &[(&str, &[u8], ModuleFormat)] = &[
        ("x.trust-ir.bin", BIN, ModuleFormat::Binary),
        ("x.tmbc", BIN, ModuleFormat::Binary),
        ("x.bin", BIN, ModuleFormat::Binary),
        ("-", BIN, ModuleFormat::Binary),
        ("x.trust-ir.txt", TEXT, ModuleFormat::Text),
        ("x.trust_ir", TEXT, ModuleFormat::Text),
        ("-", TEXT, ModuleFormat::Text),
        ("x.json", JSON, ModuleFormat::Json),
        ("x.out", JSON, ModuleFormat::Json),
        ("x.msgpack", MSGPACK, ModuleFormat::Msgpack),
        // A text / JSON file the sniff cannot place is its decoder's problem.
        ("x.trust_ir", b"garbage", ModuleFormat::Text),
        ("x.json", b"not json", ModuleFormat::Json),
    ];
    for (name, bytes, expected) in rows {
        assert_eq!(resolve(name, bytes), Ok(*expected), "{name} {bytes:?}");
    }
}

/// Negative twins, each refused by its SPECIFIC reason and message.
#[test]
fn resolution_refusals_are_named() {
    // A trust-cg container under ANY name, `.tmbc` included — the text and
    // MessagePack names too, which have no magic of their own to disagree.
    for name in [
        "x.tmbc",
        "x.trust-ir.bin",
        "x.json",
        "-",
        "x.bin",
        "x.trust_ir",
        "x.trust-ir.txt",
        "x.msgpack",
    ] {
        let refusal = resolve(name, TMBC).expect_err(name);
        assert_eq!(
            refusal,
            FormatRefusal::TrustCgContainer {
                path: name.to_string()
            }
        );
        assert!(
            refusal
                .to_string()
                .contains("this is a trust-cg tMBC container, not a trust-ir module"),
            "{refusal}"
        );
    }
    // A name the content contradicts.
    let refusal = resolve("x.json", BIN).expect_err("json name, binary bytes");
    assert_eq!(
        refusal,
        FormatRefusal::NameContradictsContent {
            path: "x.json".into(),
            named: ModuleFormat::Json,
            sniffed: Some(SniffedFormat::Binary),
        }
    );
    assert!(
        refusal
            .to_string()
            .contains("the file name says json but the content says TrustIr binary"),
        "{refusal}"
    );
    // Review (WS4.13): every OTHER named format a content claim contradicts
    // is refused naming both — never decoded under either guess.
    for (name, bytes, named, sniffed) in [
        (
            "x.msgpack",
            BIN,
            ModuleFormat::Msgpack,
            SniffedFormat::Binary,
        ),
        (
            "x.msgpack",
            JSON,
            ModuleFormat::Msgpack,
            SniffedFormat::Json,
        ),
        (
            "x.msgpack",
            TEXT,
            ModuleFormat::Msgpack,
            SniffedFormat::Text,
        ),
        (
            "x.trust-ir.txt",
            JSON,
            ModuleFormat::Text,
            SniffedFormat::Json,
        ),
        ("x.trust_ir", BIN, ModuleFormat::Text, SniffedFormat::Binary),
        ("x.json", TEXT, ModuleFormat::Json, SniffedFormat::Text),
    ] {
        assert_eq!(
            resolve(name, bytes),
            Err(FormatRefusal::NameContradictsContent {
                path: name.into(),
                named,
                sniffed: Some(sniffed),
            }),
            "{name}"
        );
    }
    // A binary name without the mandatory magic.
    let refusal = resolve("x.trust-ir.bin", TEXT).expect_err("bin name, text bytes");
    assert!(matches!(
        refusal,
        FormatRefusal::NameContradictsContent {
            named: ModuleFormat::Binary,
            sniffed: Some(SniffedFormat::Text),
            ..
        }
    ));
    let refusal = resolve("x.tmbc", MSGPACK).expect_err("bin name, no magic");
    assert!(
        refusal
            .to_string()
            .contains("no recognised TrustIr format (no TRUST_IR magic)"),
        "{refusal}"
    );
    // A silent name over content nothing claims (MessagePack is never sniffed).
    let refusal = resolve("x.bin", MSGPACK).expect_err("silent name, msgpack");
    assert_eq!(
        refusal,
        FormatRefusal::Undetectable {
            path: "x.bin".into(),
            extension: "bin".into()
        }
    );
    assert!(
        refusal.to_string().contains("pass --format explicitly"),
        "{refusal}"
    );
}

/// An explicit format is never second-guessed — not even for a trust-cg
/// container. Mutation control for the refusal above: forcing a format hands
/// the bytes to that decoder, so a container read with `--format bin` fails
/// in the BINARY DECODER, never with the container message. A resolver that
/// ignored `explicit` (or a sniff that mapped `tMBC` to binary) would flip
/// one of these rows.
#[test]
fn explicit_format_wins_and_the_container_refusal_is_the_resolvers_own() {
    for format in ModuleFormat::ALL {
        for (name, bytes) in [
            ("x.tmbc", TMBC),
            ("x.json", BIN),
            ("x.bin", MSGPACK),
            ("-", TEXT),
        ] {
            assert_eq!(
                resolve_module_format(Some(format), Path::new(name), bytes),
                Ok(format),
                "{name}"
            );
        }
    }
    let decoded = trust_ir::binary::deserialize_module(TMBC);
    assert!(decoded.is_err(), "a tMBC container is not a TrustIr binary");
    assert!(
        !decoded
            .unwrap_err()
            .to_string()
            .contains("trust-cg tMBC container"),
        "the named container refusal belongs to the resolver, not the decoder"
    );
}
