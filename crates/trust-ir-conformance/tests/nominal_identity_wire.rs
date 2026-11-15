// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS3.9 review — the v58 nominal identity key and closure-layout table on
//! the WIRE, tried adversarially: a forged key tag, a key laundered out of a
//! v38 projection, a Clean declaration name the text format must quote, a
//! closure row the writer emits but no reader may accept, and the identity
//! the key does (and does not) move.

use trust_ir_conformance::fixtures as generate;

use trust_ir::binary::{
    BinaryError, BinaryProjectionError, ModuleBinaryBody, ModuleBinaryOptions,
    NOMINAL_IDENTITY_FORMAT_VERSION, ProjectedModuleBinaryPlan, deserialize_module,
    serialize_module,
};
use trust_ir::proof::ProofDigest;
use trust_ir::ty::{FieldDef, StructDef, Ty, TypeOrigin};
use trust_ir::value::{ClosureTyId, StructId};
use trust_ir::{ClosureLayoutDescriptor, Endianness, Module, TargetInfo};
use trust_ir_build::validate::CLOSURE_LAYOUT_TABLE_REASON_PREFIX;
use trust_ir_build::{ValidationError, validate_module};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// A distinctive crate id, so the key's bytes can be located in a blob.
const CRATE_ID: u64 = 0x1122_3344_5566_7788;

fn keyed_module(origin: Option<TypeOrigin>) -> Module {
    let mut m = Module::new("keyed");
    m.target_info = Some(target());
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "Span".into(),
        fields: vec![FieldDef {
            name: "lo".into(),
            ty: Ty::U32,
            offset: Some(0),
        }],
        size: Some(4),
        align: Some(4),
        repr: Default::default(),
        origin,
    });
    m
}

fn rust_key(path: u8) -> TypeOrigin {
    TypeOrigin::Rust {
        stable_crate_id: CRATE_ID,
        def_path_hash: [path; 16],
        args_digest: ProofDigest::sha256([0x33; 32]),
    }
}

fn header_version(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[8..12].try_into().unwrap())
}

/// Byte offset of the origin PRESENCE byte in `bytes`: the `[1, 0]`
/// (present, `Rust`) pair immediately followed by the little-endian crate id.
fn presence_offset(bytes: &[u8]) -> usize {
    let mut needle = vec![1u8, 0u8];
    needle.extend_from_slice(&CRATE_ID.to_le_bytes());
    let hits: Vec<usize> = bytes
        .windows(needle.len())
        .enumerate()
        .filter(|(_, window)| *window == needle.as_slice())
        .map(|(offset, _)| offset)
        .collect();
    assert_eq!(hits.len(), 1, "the key must occur exactly once: {hits:?}");
    hits[0]
}

/// ADVERSARIAL. A v58 blob whose origin presence byte or variant tag is
/// outside the allocated space is refused by tag, never read as "no key" or
/// as some key; and flipping the presence byte to "absent" while the key's
/// bytes stay in the stream does not decode to the unkeyed twin.
#[test]
fn a_forged_origin_tag_is_refused_and_absence_cannot_be_forged_in_place() {
    let keyed = keyed_module(Some(rust_key(0xa1)));
    let bytes = serialize_module(&keyed).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), NOMINAL_IDENTITY_FORMAT_VERSION);
    assert_eq!(deserialize_module(&bytes).unwrap(), keyed);
    let at = presence_offset(&bytes);

    let mut presence = bytes.clone();
    presence[at] = 2;
    assert!(
        matches!(
            deserialize_module(&presence),
            Err(BinaryError::InvalidTag(2))
        ),
        "presence byte 2 is unallocated"
    );

    let mut variant = bytes.clone();
    variant[at + 1] = 2;
    assert!(
        matches!(
            deserialize_module(&variant),
            Err(BinaryError::InvalidTag(2))
        ),
        "TypeOrigin tag 2 is unallocated"
    );

    let unkeyed = keyed_module(None);
    let mut absent = bytes.clone();
    absent[at] = 0;
    let laundered = deserialize_module(&absent);
    assert!(
        !laundered.as_ref().is_ok_and(|m| *m == unkeyed),
        "the key's bytes are still in the stream; they cannot decode to the unkeyed twin: {laundered:?}"
    );
}

/// ADVERSARIAL. The explicit v38 projections are the one writer path that
/// does NOT select the minimum lossless version, so they must REFUSE a keyed
/// definition and a declared closure frame by name rather than silently
/// dropping either — a keyed module projected to v38 would be an unkeyed
/// module with the same name, which is precisely the laundering the split
/// rule exists to prevent.
#[test]
fn a_v38_projection_refuses_the_key_and_the_closure_table_by_name() {
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        let keyed = keyed_module(Some(rust_key(0xa1)));
        let refused = ProjectedModuleBinaryPlan::try_new(
            &keyed,
            ModuleBinaryOptions {
                body,
                ..ModuleBinaryOptions::default()
            },
        )
        .err();
        assert_eq!(
            refused,
            Some(BinaryProjectionError::NominalIdentityRequiresV58),
            "{body:?}: a keyed definition"
        );

        let with_frame = generate::build_closure_layout().expect("the fixture builds");
        let refused = ProjectedModuleBinaryPlan::try_new(
            &with_frame,
            ModuleBinaryOptions {
                body,
                ..ModuleBinaryOptions::default()
            },
        )
        .err();
        assert_eq!(
            refused,
            Some(BinaryProjectionError::NominalIdentityRequiresV58),
            "{body:?}: a declared closure frame"
        );

        // CONTROL: the unkeyed twin projects.
        let unkeyed = keyed_module(None);
        assert!(
            ProjectedModuleBinaryPlan::try_new(
                &unkeyed,
                ModuleBinaryOptions {
                    body,
                    ..ModuleBinaryOptions::default()
                },
            )
            .is_ok(),
            "{body:?}: an unkeyed module keeps its v38 projection"
        );
    }
}

/// The key is part of module identity EXACTLY when present: keying, re-keying
/// and un-keying each move `stable_digest`, while an unkeyed module keeps its
/// pre-v58 header word — so no existing identity moves.
#[test]
fn the_key_moves_module_identity_only_when_present() {
    let unkeyed = keyed_module(None);
    let keyed = keyed_module(Some(rust_key(0xa1)));
    let rekeyed = keyed_module(Some(rust_key(0xa2)));
    let clean = keyed_module(Some(TypeOrigin::Clean {
        decl: "Span".into(),
        env_digest: ProofDigest::sha256([0x33; 32]),
    }));

    assert!(
        header_version(&serialize_module(&unkeyed).expect("serialize_module: test fixture"))
            < NOMINAL_IDENTITY_FORMAT_VERSION
    );
    let digests = [
        unkeyed.stable_digest(),
        keyed.stable_digest(),
        rekeyed.stable_digest(),
        clean.stable_digest(),
    ];
    for (i, a) in digests.iter().enumerate() {
        for (j, b) in digests.iter().enumerate() {
            assert_eq!(i == j, a == b, "digest {i} vs {j}");
        }
    }
    // Determinism: the same key is the same identity.
    assert_eq!(
        keyed.stable_digest(),
        keyed_module(Some(rust_key(0xa1))).stable_digest()
    );
}

/// A Clean declaration name is arbitrary text: quotes, a backslash, a newline
/// and a non-ASCII letter must all survive the text format, and so must the
/// extreme `Rust` key bytes. A parser that mis-read one hex digit would
/// silently mint a DIFFERENT entity.
#[test]
fn awkward_key_spellings_survive_every_format() {
    let mut m = Module::new("awkward");
    m.target_info = Some(target());
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "A".into(),
        fields: vec![FieldDef {
            name: String::new(),
            ty: Ty::U32,
            offset: None,
        }],
        size: Some(4),
        align: Some(4),
        repr: Default::default(),
        origin: Some(TypeOrigin::Clean {
            decl: "Trust.List'.cons \"q\" \\ \n\t\u{3b1})".into(),
            env_digest: ProofDigest::sha256([0xff; 32]),
        }),
    });
    m.add_struct(StructDef {
        id: StructId::new(1),
        name: "B".into(),
        fields: vec![FieldDef {
            name: String::new(),
            ty: Ty::U32,
            offset: None,
        }],
        size: Some(4),
        align: Some(4),
        repr: Default::default(),
        origin: Some(TypeOrigin::Rust {
            stable_crate_id: u64::MAX,
            def_path_hash: [0xff; 16],
            args_digest: ProofDigest {
                algorithm: trust_ir::proof::ProofDigestAlgorithm::TrustIrStableV1,
                bytes: [0x00; 32],
            },
        }),
    });
    m.add_struct(StructDef {
        id: StructId::new(2),
        name: "C".into(),
        fields: vec![FieldDef {
            name: String::new(),
            ty: Ty::U32,
            offset: None,
        }],
        size: Some(4),
        align: Some(4),
        repr: Default::default(),
        origin: Some(TypeOrigin::Rust {
            stable_crate_id: 0,
            def_path_hash: [0x00; 16],
            args_digest: ProofDigest::sha256([0x00; 32]),
        }),
    });
    assert_eq!(validate_module(&m), vec![], "the fixture must validate");

    let text = format!("{m}");
    let parsed = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("text round trip: {error:?}\n{text}"));
    assert_eq!(parsed, m, "text\n{text}");
    assert_eq!(format!("{parsed}"), text, "the text form is idempotent");

    let bytes = serialize_module(&m).expect("serialize_module: test fixture");
    assert_eq!(deserialize_module(&bytes).unwrap(), m, "binary round trip");

    let json = serde_json::to_string(&m).unwrap();
    assert_eq!(
        serde_json::from_str::<Module>(&json).unwrap(),
        m,
        "json round trip"
    );
    let packed = rmp_serde::to_vec(&m).unwrap();
    assert_eq!(
        rmp_serde::from_slice::<Module>(&packed).unwrap(),
        m,
        "msgpack round trip"
    );
}

/// ADVERSARIAL (a wrong emitted module). The writer does not validate the
/// closure table (the v42 tuple precedent), so a producer CAN emit a row that
/// names no closure type or an incoherent frame. No reader may accept it: the
/// binary decoder refuses on decode, and the serde path — which cannot refuse
/// on decode — is refused by `validate_module` by name.
#[test]
fn an_incoherent_closure_row_is_refused_by_every_reader() {
    let mut dangling = Module::new("dangling");
    dangling.target_info = Some(target());
    dangling.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(5),
        size: 8,
        align: 8,
        capture_offsets: vec![0],
    });
    let bytes = serialize_module(&dangling).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), NOMINAL_IDENTITY_FORMAT_VERSION);
    assert!(
        matches!(deserialize_module(&bytes), Err(BinaryError::InvalidData(_))),
        "a row naming no closure type must not decode"
    );
    let json = serde_json::to_string(&dangling).unwrap();
    let decoded: Module = serde_json::from_str(&json).unwrap();
    assert!(
        validate_module(&decoded)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { reason } if reason.starts_with(CLOSURE_LAYOUT_TABLE_REASON_PREFIX))),
        "the serde path is refused by the validator"
    );

    // A coherent row with the target REMOVED: a frame is sized against the
    // target's scalar layout, so without one there is no evidence to check
    // it against, and the reader fails closed rather than trusting the row.
    let mut untargeted = generate::build_closure_layout().expect("the fixture builds");
    untargeted.target_info = None;
    let bytes = serialize_module(&untargeted).expect("serialize_module: test fixture");
    assert!(
        matches!(deserialize_module(&bytes), Err(BinaryError::InvalidData(_))),
        "a closure frame with no target to size it against must not decode"
    );
}

/// Review — an identity key has ONE text spelling. The printer writes every
/// key byte as lowercase hex, and the parser's doc said it read exactly that;
/// it accepted uppercase too (`char::to_digit(16)`), so a hand-edited key
/// could pass for the one a producer printed. Each adversarial spelling below
/// is the printed text with ONE run upper-cased, and each is refused — in the
/// crate id, the def-path hash, the `Rust` args digest, and the `Clean` env
/// digest. The positive twin is the printed text itself, which parses back to
/// the module.
#[test]
fn an_uppercase_key_spelling_is_refused_not_folded() {
    let rust = keyed_module(Some(TypeOrigin::Rust {
        stable_crate_id: 0xabcd_ef01_2345_6789,
        def_path_hash: [0xab; 16],
        args_digest: ProofDigest::sha256([0xcd; 32]),
    }));
    let clean = keyed_module(Some(TypeOrigin::Clean {
        decl: "Trust.Nat".into(),
        env_digest: ProofDigest::sha256([0xef; 32]),
    }));
    for module in [&rust, &clean] {
        let text = format!("{module}");
        assert_eq!(
            trust_ir::parser::parse_module(&text).as_ref(),
            Ok(module),
            "positive twin: the printed spelling parses back\n{text}"
        );
    }

    let rust_text = format!("{rust}");
    let clean_text = format!("{clean}");
    let run = |prefix: &str, byte: &str, count: usize| format!("{prefix}{}", byte.repeat(count));
    let upcased = [
        (
            &rust_text,
            run("crate=0x", "abcdef0123456789", 1),
            run("crate=0x", "ABCDEF0123456789", 1),
        ),
        (&rust_text, run("path=", "ab", 16), run("path=", "AB", 16)),
        (
            &rust_text,
            run("args=sha256:", "cd", 32),
            run("args=sha256:", "CD", 32),
        ),
        (
            &clean_text,
            run("env=sha256:", "ef", 32),
            run("env=sha256:", "EF", 32),
        ),
    ];
    for (text, lower, upper) in &upcased {
        assert!(
            text.contains(lower.as_str()),
            "fixture drift: {lower:?} not in\n{text}"
        );
        let forged = text.replacen(lower.as_str(), upper, 1);
        assert!(
            trust_ir::parser::parse_module(&forged).is_err(),
            "an uppercase spelling of a key byte must be refused: {upper:?}\n{forged}"
        );
    }
}

/// Review — the missing TEXT twin of `an_incoherent_closure_row_is_refused_by_every_reader`:
/// the text parser, like serde, cannot refuse an incoherent closure row on
/// read, and the row it parses is refused by `validate_module` by name.
#[test]
fn an_incoherent_closure_row_read_from_text_is_refused_by_the_validator() {
    let mut dangling = Module::new("dangling");
    dangling.target_info = Some(target());
    dangling.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(5),
        size: 8,
        align: 8,
        capture_offsets: vec![0],
    });
    let text = format!("{dangling}");
    let parsed = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("the row must spell and parse: {error:?}\n{text}"));
    assert_eq!(parsed.closure_layouts, dangling.closure_layouts);
    assert!(
        validate_module(&parsed)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { reason } if reason.starts_with(CLOSURE_LAYOUT_TABLE_REASON_PREFIX))),
        "the text path is refused by the validator"
    );
}

/// Review — the text parser's "exactly `2 * N` hex digits" claim
/// (`read_hex_bytes`: "a short or over-long run is a parse error rather than a
/// silent truncation") had no test. A key field one digit SHORT or one digit
/// LONG, an unknown key kind and an unknown digest algorithm must each be
/// refused; the printed spelling (the positive twin) still parses back. A
/// parser that read "the first 16 digits" of a 17-digit crate id, or padded a
/// 15-digit one, would mint a DIFFERENT entity from a hand-edited key.
#[test]
fn a_key_field_of_the_wrong_length_or_kind_is_refused_not_truncated() {
    let rust = keyed_module(Some(TypeOrigin::Rust {
        stable_crate_id: 0xabcd_ef01_2345_6789,
        def_path_hash: [0xab; 16],
        args_digest: ProofDigest::sha256([0xcd; 32]),
    }));
    let clean = keyed_module(Some(TypeOrigin::Clean {
        decl: "Trust.Nat".into(),
        env_digest: ProofDigest::sha256([0xef; 32]),
    }));
    let rust_text = format!("{rust}");
    let clean_text = format!("{clean}");
    assert_eq!(
        trust_ir::parser::parse_module(&rust_text).as_ref(),
        Ok(&rust),
        "positive twin: the printed Rust key parses back\n{rust_text}"
    );
    assert_eq!(
        trust_ir::parser::parse_module(&clean_text).as_ref(),
        Ok(&clean),
        "positive twin: the printed Clean key parses back\n{clean_text}"
    );

    // (field as printed, one digit short, one digit long)
    let crate_id = "crate=0xabcdef0123456789".to_string();
    let path = format!("path={}", "ab".repeat(16));
    let args = format!("args=sha256:{}", "cd".repeat(32));
    let env = format!("env=sha256:{}", "ef".repeat(32));
    let cases = [
        (&rust_text, &crate_id),
        (&rust_text, &path),
        (&rust_text, &args),
        (&clean_text, &env),
    ];
    for (text, field) in cases {
        assert!(
            text.contains(field.as_str()),
            "fixture drift: {field:?} not in\n{text}"
        );
        let short = &field[..field.len() - 1];
        let long = format!("{field}a");
        for forged_field in [short.to_string(), long] {
            let forged = text.replacen(field.as_str(), &forged_field, 1);
            assert!(
                trust_ir::parser::parse_module(&forged).is_err(),
                "a key field of the wrong length must be refused, not truncated or padded: \
                 {forged_field:?}\n{forged}"
            );
        }
    }

    // An unknown key kind and an unknown digest algorithm are refused by name,
    // never read as "no key".
    for (text, printed, forged_spelling) in [
        (&rust_text, "origin=rust(", "origin=swift("),
        (&clean_text, "origin=clean(", "origin=Clean("),
        (&rust_text, "args=sha256:", "args=md5:"),
        (&clean_text, "env=sha256:", "env=SHA256:"),
    ] {
        assert!(
            text.contains(printed),
            "fixture drift: {printed:?} not in\n{text}"
        );
        let forged = text.replacen(printed, forged_spelling, 1);
        assert!(
            trust_ir::parser::parse_module(&forged).is_err(),
            "an unknown key spelling must be refused: {forged_spelling:?}\n{forged}"
        );
    }
}
