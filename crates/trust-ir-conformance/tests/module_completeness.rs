// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS5.3b / F-090: the typed module COMPLETENESS carrier
// (`Module.completeness: Option<ModuleCompleteness>`), non-wire half.
//
// F-090 measured that the Rust producer silently drops bodies it cannot lower
// and still emits a module that validates rc=0 — a Vec/Box crate yields a
// VALID module with ZERO functions. `coverage.json` beside the module
// discloses each drop honestly; the module does not. G3 ("a silently
// incomplete module must not read as complete") needs the claim IN the
// bytes, and it needs THREE values: `None` (no claim: every pre-carrier blob
// and every hand-built module), `Complete`, `Partial(rows)`. The v41
// `body_gate` lesson is why two would be wrong: with a two-state carrier a
// re-serialized legacy module silently claims completeness.
//
// What this file pins:
//   * a `Partial` module round-trips LOSSLESSLY through the text, JSON and
//     MessagePack formats and validates (`validate_module == []`) — positive
//     fixture;
//   * the BINARY format has no carrier yet (the wire part is a member of the
//     next open wire batch, reserved first per `docs/wire-allocation.md`):
//     every binary entry point REFUSES a module carrying ANY claim with the
//     named `CompletenessClaimUnencodable` instead of dropping it, and a
//     decoded blob always reads `None` — the mutation the roadmap names
//     ("decode a legacy blob, re-encode it: it must NOT carry `Complete`");
//   * a module WITHOUT a claim keeps its exact pre-WS5.3b JSON and
//     MessagePack bytes save for three flips to always-emitted, each forced
//     because positional MessagePack may only skip a TRAILING field:
//     `tuple_layouts` (WS5.3b appended the claim after it), the claim itself
//     (amendment D appended `drop_glue` after it, so an absent claim spells
//     `null`) and, since wire v58, `drop_glue` (`closure_layouts` was
//     appended after it); a pre-v58 positional array (no drop-glue slot), a
//     pre-amendment-D one (no claim slot either) and a pre-v42 one (no tuple
//     table either) each decode with no claim;
//   * the text grammar refuses an `unlowered` row outside a `partial` claim
//     and a second claim (negative twins);
//   * `trust_ir::diff` reports a flipped claim as the `completeness` module
//     row (mutation control);
//   * the proof-program row `crit.unex06` (F-090) flips: an incomplete module
//     does not read as complete — `validate_module_complete` refuses `None`
//     by name and `Partial` with its rows.

use trust_ir::diff::{DiffOptions, diff_with};
use trust_ir::{Endianness, Module, ModuleCompleteness, Producer, TargetInfo, Ty, UnloweredRow};
use trust_ir_build::{CompletenessError, ModuleBuilder, validate_module, validate_module_complete};

/// A bodyless declaration is a foreign boundary, and the validator requires
/// an explicit target at one (`TargetInfoRequired`).
fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// The q04_heap shape of F-090: the crate declared `program` and `total`,
/// lowered `program` and refused `total` (a `Vec<u64>` body). The producer
/// emitted `total` as a bodyless declaration and says so in the claim; the
/// second row names an item nothing of which was emitted.
fn partial_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("ws5_3b_partial", target());
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let one = fb.iconst(Ty::U64, 1);
    let r = fb.add(Ty::U64, x, one);
    fb.ret(vec![r]);
    fb.build();
    let total = mb.declare_function("total", sig);
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.function_by_id_mut(total).unwrap().producer = Some(Producer::TRust);
    m.completeness = Some(ModuleCompleteness::Partial(unlowered_rows()));
    m
}

fn unlowered_rows() -> Vec<UnloweredRow> {
    vec![
        UnloweredRow {
            symbol: "total".into(),
            display_path: Some("q04_heap::total".into()),
            reason: "unsupported shape: Vec<u64> body (Box/Vec lowering)".into(),
        },
        UnloweredRow {
            symbol: "_ZN8q04_heap4bits17h\"quoted\"E".into(),
            display_path: None,
            reason: "union field read".into(),
        },
    ]
}

fn plain_module() -> Module {
    let mut m = partial_module();
    m.completeness = None;
    m
}

fn text_roundtrip(m: &Module) -> Module {
    let text = trust_ir::format::canonical_checked(m).expect("text carries the claim");
    trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("text parses: {e}\n{text}"))
}

// ---------------------------------------------------------------------------
// positive fixture: the claim round-trips through text / JSON / MessagePack
// ---------------------------------------------------------------------------

#[test]
fn a_partial_claim_round_trips_through_text_json_and_msgpack_and_validates() {
    let m = partial_module();
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    assert!(trust_ir::format::text_losses(&m).is_empty());

    let text = trust_ir::format::canonical_checked(&m).expect("text");
    assert!(text.contains("\ncompleteness partial\n"), "{text}");
    assert!(
        text.contains("unlowered \"total\" \"q04_heap::total\" \"unsupported shape"),
        "{text}"
    );
    assert!(
        text.contains("\\\"quoted\\\"E\" - \"union field read\""),
        "{text}"
    );
    let back = text_roundtrip(&m);
    assert_eq!(back.completeness, m.completeness);
    assert_eq!(
        trust_ir::format::canonical_checked(&back).unwrap(),
        text,
        "text is idempotent"
    );

    let json = serde_json::to_string(&m).expect("json");
    assert!(
        json.contains(r#""completeness":{"Partial":[{"symbol":"total""#),
        "{json}"
    );
    let back: Module = serde_json::from_str(&json).expect("json decodes");
    assert_eq!(back, m);

    let mp = rmp_serde::to_vec(&m).expect("msgpack");
    let back: Module = rmp_serde::from_slice(&mp).expect("msgpack decodes");
    assert_eq!(back, m);
    assert_eq!(
        rmp_serde::to_vec(&back).unwrap(),
        mp,
        "msgpack is idempotent"
    );

    // `Complete` takes the same three roads.
    let mut complete = m.clone();
    complete.completeness = Some(ModuleCompleteness::Complete);
    assert!(validate_module(&complete).is_empty());
    let text = trust_ir::format::canonical_checked(&complete).expect("text");
    assert!(text.contains("\ncompleteness complete\n"), "{text}");
    assert!(!text.contains("unlowered"), "{text}");
    assert_eq!(
        text_roundtrip(&complete),
        trust_ir::format::canonicalize(&complete)
    );
    let json = serde_json::to_string(&complete).expect("json");
    assert!(json.contains(r#""completeness":"Complete""#), "{json}");
    let back: Module = rmp_serde::from_slice(&rmp_serde::to_vec(&complete).unwrap()).unwrap();
    assert_eq!(back, complete);
}

// ---------------------------------------------------------------------------
// three values: `None` is not `Complete`, in every format
// ---------------------------------------------------------------------------

/// A module without a claim spells NO CLAIM explicitly: amendment D appended
/// `drop_glue` after the claim, so the claim is always emitted — JSON carries
/// `"completeness":null` — wire v58 appended `closure_layouts` after the
/// drop-glue table, so that table is always emitted too (`[]`), and v70
/// appended the blob table after the closure table, so the closure table is
/// always emitted as well and the empty blob table is the one trailing skip:
/// the positional MessagePack array ends with the nil claim and two empty
/// arrays. Every legacy shape still decodes with NO claim, never `Complete`:
/// the pre-v70 array (no closure-layout slot), the pre-v58 array (no
/// drop-glue slot either), the pre-amendment-D array (no claim slot either,
/// the pre-WS5.3b shape too) and the pre-v42 one (no `tuple_layouts` either).
#[test]
fn absent_claim_is_an_explicit_no_claim_and_legacy_shapes_decode_as_no_claim() {
    let plain = plain_module();
    let json = serde_json::to_string(&plain).expect("json");
    assert!(json.contains(r#""completeness":null"#), "{json}");
    assert!(json.contains(r#""drop_glue":[]"#), "{json}");
    assert!(json.contains(r#""closure_layouts":[]"#), "{json}");
    assert!(!json.contains("blobs"), "{json}");
    assert!(
        json.contains(r#""tuple_layouts":[]"#),
        "tuple_layouts is always emitted now that a field follows it: {json}"
    );
    let back: Module = serde_json::from_str(&json).expect("decodes");
    assert_eq!(back.completeness, None);
    // A pre-v70 document has no `closure_layouts` key, a pre-v58 one no
    // `drop_glue` key either, and a pre-amendment-D one no `completeness` key
    // either.
    let pre_blob_json = json.replace(r#","closure_layouts":[]"#, "");
    assert!(
        !pre_blob_json.contains("closure_layouts"),
        "{pre_blob_json}"
    );
    let back: Module = serde_json::from_str(&pre_blob_json).expect("pre-v70 decodes");
    assert_eq!(back, plain);
    let pre_closure_json = pre_blob_json.replace(r#","drop_glue":[]"#, "");
    assert!(
        !pre_closure_json.contains("drop_glue"),
        "{pre_closure_json}"
    );
    let back: Module = serde_json::from_str(&pre_closure_json).expect("pre-v58 decodes");
    assert_eq!(back, plain);
    let legacy_json = pre_closure_json.replace(r#","completeness":null"#, "");
    assert!(!legacy_json.contains("completeness"), "{legacy_json}");
    let back: Module = serde_json::from_str(&legacy_json).expect("legacy decodes");
    assert_eq!(back, plain);

    let mp = rmp_serde::to_vec(&plain).expect("msgpack");
    let back: Module = rmp_serde::from_slice(&mp).expect("decodes");
    assert_eq!(back, plain);
    // `Module` has more than 15 fields, so the array carries an `array16`
    // header: 23 fields, the nil claim then the empty drop-glue and
    // closure-layout tables (the empty blob table is skipped).
    assert_eq!(mp[0], 0xdc, "array16 header: {:#x}", mp[0]);
    let n = u16::from_be_bytes([mp[1], mp[2]]);
    assert_eq!(
        n, 23,
        "the field count with the claim, drop-glue and closure-layout slots, without the blob \
         table"
    );
    assert_eq!(
        &mp[mp.len() - 3..],
        &[0xc0, 0x90, 0x90],
        "the trailing nil claim and empty drop-glue and closure-layout tables"
    );
    // The pre-v70 array: no closure-layout slot.
    let mut legacy = mp.clone();
    legacy.pop();
    legacy[1..3].copy_from_slice(&(n - 1).to_be_bytes());
    let back: Module = rmp_serde::from_slice(&legacy).expect("pre-v70 array decodes");
    assert_eq!(back, plain);
    // The pre-v58 array: no drop-glue slot either.
    assert_eq!(
        *legacy.last().unwrap(),
        0x90,
        "the trailing empty drop-glue table"
    );
    legacy.pop();
    legacy[1..3].copy_from_slice(&(n - 2).to_be_bytes());
    let back: Module = rmp_serde::from_slice(&legacy).expect("pre-v58 array decodes");
    assert_eq!(back, plain);
    // The pre-amendment-D (and pre-WS5.3b) array: no claim slot either.
    assert_eq!(*legacy.last().unwrap(), 0xc0, "the trailing nil claim");
    legacy.pop();
    legacy[1..3].copy_from_slice(&(n - 3).to_be_bytes());
    let back: Module = rmp_serde::from_slice(&legacy).expect("pre-claim array decodes");
    assert_eq!(
        back.completeness, None,
        "a legacy array is NO CLAIM, never Complete"
    );
    assert_eq!(back, plain);
    // The pre-v42 array: no `tuple_layouts` slot either.
    assert_eq!(*legacy.last().unwrap(), 0x90, "trailing empty tuple table");
    legacy.pop();
    legacy[1..3].copy_from_slice(&(n - 4).to_be_bytes());
    let back: Module = rmp_serde::from_slice(&legacy).expect("pre-v42 array decodes");
    assert_eq!(
        back.completeness, None,
        "a legacy array is NO CLAIM, never Complete"
    );
    assert_eq!(back, plain);
}

/// Mutation (roadmap): decode a legacy binary blob and re-encode it through
/// every format — it must NOT carry `Complete`. The binary reader always
/// yields `None`, and the writers refuse a claim rather than inventing one.
#[test]
fn a_decoded_legacy_blob_never_claims_complete() {
    let plain = plain_module();
    let bytes = trust_ir::binary::serialize_module(&plain).expect("serialize_module: test fixture");
    let back = trust_ir::binary::deserialize_module(&bytes).expect("decodes");
    assert_eq!(back.completeness, None);
    assert_eq!(
        trust_ir::binary::serialize_module(&back).expect("serialize_module: test fixture"),
        bytes
    );
    let json = serde_json::to_string(&back).unwrap();
    assert!(!json.contains("Complete"), "{json}");
    let text = trust_ir::format::canonical_checked(&back).unwrap();
    assert!(!text.contains("completeness"), "{text}");
    assert_eq!(text_roundtrip(&back).completeness, None);
    assert!(
        validate_module_complete(&back).is_err(),
        "a decoded legacy blob is not known complete"
    );
}

// ---------------------------------------------------------------------------
// binary: refused by name until the wire batch
// ---------------------------------------------------------------------------

#[test]
fn binary_refuses_a_completeness_claim_by_name() {
    use trust_ir::binary::{BinaryProjectionError, ModuleBinaryOptions, ProjectedModuleBinaryPlan};
    for claim in [
        ModuleCompleteness::Complete,
        ModuleCompleteness::Partial(unlowered_rows()),
    ] {
        let mut m = plain_module();
        m.completeness = Some(claim);
        assert!(m.completeness_claim_unencodable());
        let err = ProjectedModuleBinaryPlan::try_new(&m, ModuleBinaryOptions::default())
            .err()
            .expect("projection must refuse the claim");
        assert_eq!(err, BinaryProjectionError::CompletenessClaimUnencodable);
        assert!(err.to_string().contains("Module.completeness"));

        // The blob entry refuses with the same typed refusal, never a panic.
        let refused = std::panic::catch_unwind(|| trust_ir::binary::serialize_module(&m))
            .expect("serialize_module never panics")
            .expect_err("serialize_module must refuse rather than drop the claim");
        assert_eq!(refused, err, "the blob entry names the same refusal");
        assert!(refused.to_string().contains("Module.completeness"));
        let panic = std::panic::catch_unwind(|| m.stable_digest())
            .expect_err("a claimed module has no wire identity yet");
        drop(panic);
        // The executable projection runs the same writer: it must not hash
        // the image with the claim silently projected away (roadmap: the
        // claim is a fact about the executable image, so this digest will
        // OBSERVE it once the wire part lands; until then it refuses).
        let panic = std::panic::catch_unwind(|| m.executable_content_digest_v1())
            .expect_err("the executable projection must not drop the claim");
        drop(panic);
        // The build crate's digest-keyed entry points refuse by name too.
        let blocker = trust_ir_build::wire_identity_blocker(&m).expect("blocked");
        assert!(
            matches!(
                &blocker,
                trust_ir_build::ValidationError::ModuleHasNoWireIdentity { construct, .. }
                    if construct.contains("Module.completeness")
            ),
            "{blocker:?}"
        );
    }

    // Control: the same module with the claim removed encodes and
    // round-trips at the current header — the refusal is about the claim.
    let plain = plain_module();
    assert!(!plain.completeness_claim_unencodable());
    assert!(trust_ir_build::wire_identity_blocker(&plain).is_none());
    let bytes = trust_ir::binary::serialize_module(&plain).expect("serialize_module: test fixture");
    let back = trust_ir::binary::deserialize_module(&bytes).expect("decode");
    assert_eq!(back, plain);
}

// ---------------------------------------------------------------------------
// text negative twins
// ---------------------------------------------------------------------------

#[test]
fn text_refuses_an_unlowered_row_outside_a_partial_claim_and_a_second_claim() {
    let m = partial_module();
    let text = trust_ir::format::canonical_checked(&m).expect("text");

    // Twin 1: the `unlowered` rows without their `completeness partial` head
    // — the parser refuses rather than dropping the rows.
    let headless = text.replace("\ncompleteness partial\n", "\n");
    let err = trust_ir::parser::parse_module(&headless).expect_err("rows without a claim");
    assert!(
        err.to_string()
            .contains("`unlowered` row outside a `completeness partial` claim"),
        "{err}"
    );

    // Twin 2: a second claim after the first.
    let doubled = text.replace(
        "\ncompleteness partial\n",
        "\ncompleteness complete\ncompleteness partial\n",
    );
    let err = trust_ir::parser::parse_module(&doubled).expect_err("two claims");
    assert!(
        err.to_string().contains("duplicate `completeness` claim"),
        "{err}"
    );

    // Twin 3: a row under a `complete` claim.
    let contradiction = text.replace("\ncompleteness partial\n", "\ncompleteness complete\n");
    let err = trust_ir::parser::parse_module(&contradiction).expect_err("rows under complete");
    assert!(err.to_string().contains("`unlowered` row outside"), "{err}");

    // Control: the unedited text parses back to the module.
    assert_eq!(text_roundtrip(&m).completeness, m.completeness);
}

// ---------------------------------------------------------------------------
// diff: a flipped claim is a module-level change
// ---------------------------------------------------------------------------

#[test]
fn diff_reports_a_flipped_claim_as_the_completeness_row() {
    let partial = partial_module();
    let mut complete = partial.clone();
    complete.completeness = Some(ModuleCompleteness::Complete);
    let plain = plain_module();

    let row = |a: &Module, b: &Module| {
        let d = diff_with(a, b, DiffOptions::default());
        d.module_meta_changes
            .iter()
            .find(|c| c.field == "completeness")
            .map(|c| (c.before.clone(), c.after.clone()))
    };
    let flipped = row(&partial, &complete).expect("Partial -> Complete is a change");
    assert!(
        flipped.0.contains("Partial") && flipped.1.contains("Complete"),
        "{flipped:?}"
    );
    let claimed = row(&plain, &complete).expect("None -> Complete is a change");
    assert!(
        claimed.0.contains("None") && claimed.1.contains("Complete"),
        "{claimed:?}"
    );
    assert!(
        row(&plain, &partial).is_some(),
        "None -> Partial is a change"
    );
    // Control: identical claims are no change.
    assert!(row(&partial, &partial.clone()).is_none());
    assert!(diff_with(&partial, &partial.clone(), DiffOptions::default()).is_empty());
}

// ---------------------------------------------------------------------------
// proof-program row (F-090): crit.unex06 — an incomplete module does not read
// as complete
// ---------------------------------------------------------------------------

/// `crit.unex06` measured a producer that drops bodies and emits a module
/// which validates and reads as whole. With the carrier, "is this module
/// complete?" has a checkable answer with THREE outcomes, and only an
/// affirmative `Complete` claim is `Ok`.
#[test]
fn ratchet_crit_unex06_an_incomplete_module_does_not_read_as_complete() {
    // No claim: the exact pre-carrier shape of every F-090 module.
    let plain = plain_module();
    assert!(validate_module(&plain).is_empty());
    assert_eq!(
        validate_module_complete(&plain),
        Err(CompletenessError::IncompletenessUnclaimed)
    );

    // A disclosed drop: refused with the rows.
    let partial = partial_module();
    assert!(validate_module(&partial).is_empty());
    let err = validate_module_complete(&partial).expect_err("partial is not complete");
    assert_eq!(
        err,
        CompletenessError::ModuleIncomplete {
            rows: unlowered_rows()
        }
    );
    let shown = err.to_string();
    assert!(
        shown.contains("2 unlowered item(s)")
            && shown.contains("\"total\" (q04_heap::total): unsupported shape"),
        "{shown}"
    );

    // Only an affirmative claim is complete.
    let mut complete = partial.clone();
    complete.completeness = Some(ModuleCompleteness::Complete);
    assert_eq!(validate_module_complete(&complete), Ok(()));
    assert!(ModuleCompleteness::Complete.is_complete());
    assert_eq!(ModuleCompleteness::Complete.unlowered(), &[]);
    assert_eq!(
        ModuleCompleteness::Partial(unlowered_rows())
            .unlowered()
            .len(),
        2
    );
}
